open Language
module Json = Yojson.Safe
module JsonUtil = Yojson.Safe.Util

module Node = struct
  include String

  let hash = Hashtbl.hash
end

module G = struct
  include Graph.Persistent.Digraph.ConcreteBidirectional (Node)

  let graph_attributes _ = []

  let default_vertex_attributes _ = []

  let vertex_name v = v

  let vertex_attributes _ = []

  let get_subgraph _ = None

  let default_edge_attributes _ = []

  let edge_attributes _ = []
end

module GraphUtils = Graph.Oper.P (G)

type t = G.t

let class_info = Hashtbl.create 65535

let assoc_fold ~f ~init x = List.fold_left f init (JsonUtil.to_assoc x)

let list_fold ~f ~init x = List.fold_left f init (JsonUtil.to_list x)

let make_arg_id arg_list =
  List.fold_left
    (fun (num, lst) p ->
      let name =
        JsonUtil.to_string p |> Str.split Regexp.dot |> List.rev |> List.hd
        |> Regexp.global_rm Regexp.open_end_bk
      in
      (num + 1, (name ^ string_of_int num) :: lst))
    (1, []) arg_list
  |> snd |> List.rev

let make_var arg_list =
  let init =
    VariableMap.add (Ident.Symbol "v1") (Ident.Var "this") VariableMap.empty
  in
  List.fold_left
    (fun (num, cond) p ->
      let escape_dollar = Regexp.global_rm Regexp.dollar p in
      ( num + 1,
        VariableMap.add
          (Ident.Symbol ("v" ^ string_of_int num))
          (Ident.Var escape_dollar) cond ))
    (2, init) arg_list
  |> snd

let make_any_to_symbol_mem s_num =
  let symbol = Ident.Symbol ("v" ^ string_of_int s_num) in
  Memory.add Ident.Any symbol Memory.empty

let make_var_to_symbol_mem var s_num mem =
  Memory.add (Ident.Var var) (Ident.Symbol ("v" ^ string_of_int s_num)) mem

let make_premem arg_list =
  let incr = List.length arg_list + 1 in
  let init =
    Memory.add (Ident.Symbol "v1")
      (make_any_to_symbol_mem (1 + incr))
      Memory.empty
  in
  let _, init_mem =
    List.fold_left
      (fun (num, cond) _ ->
        let mem = make_any_to_symbol_mem (num + incr) in
        (num + 1, Memory.add (Ident.Symbol ("v" ^ string_of_int num)) mem cond))
      (2, init) arg_list
  in
  let _, arg_mem =
    List.fold_left
      (fun (num, cond) p -> (num + 1, make_var_to_symbol_mem p num cond))
      (1 + (2 * incr), Memory.empty)
      arg_list
  in
  (* this's any symbol -> arg_mem *)
  Memory.add (Ident.Symbol ("v" ^ (1 + incr |> string_of_int))) arg_mem init_mem

let make_postmem arg_list premem =
  let decr = List.length arg_list in
  List.fold_left
    (fun (num, cond) _ ->
      let mem = make_any_to_symbol_mem (num - decr) in
      (num + 1, Memory.add (Ident.Symbol ("v" ^ string_of_int num)) mem cond))
    (1 + (2 * (decr + 1)), premem)
    arg_list
  |> snd

let make_summary arg_ids =
  let var = make_var arg_ids in
  let premem = make_premem arg_ids in
  let postmem = make_postmem arg_ids premem in
  {
    (* heuristic *)
    cost = Int 5;
    relation = RelationMap.empty;
    value = ValueMap.empty;
    use_field = UseFieldMap.M.empty;
    precond = (var, premem);
    postcond = (var, postmem);
    args = [];
  }

let get_modifier access : modifier =
  let access = JsonUtil.to_string access in
  if access = "public" then Public
  else if access = "private" then Private
  else if access = "protected" then Protected
  else if access = "default" then Default
  else (* unknown --> useless *) Private

let rec get_type t =
  match t with
  | "int" -> Int
  | "long" -> Long
  | "short" -> Short
  | "byte" -> Byte
  | "float" -> Float
  | "double" -> Double
  | "bool" -> Bool
  | "char" -> Char
  | "java.lang.String" -> String
  | "" -> NonType
  | _ when Utils.exist_regexp Regexp.open_end_bk t ->
      let typ = Regexp.first_rm Regexp.open_end_bk t |> get_type in
      Array typ
  | _ -> Object t

let filter_method_info methods =
  let m_names = JsonUtil.keys methods in
  List.fold_left
    (fun lst m_name ->
      let m_info = JsonUtil.member m_name methods in
      let r_type = JsonUtil.member "rtype" m_info |> JsonUtil.to_string in
      if r_type = "void" then m_name :: lst else lst)
    [] m_names

let get_method_info class_name method_name args arg_ids m_info =
  let this = This (get_type class_name) in
  let formal_params =
    List.map2
      (fun typ id -> Var (get_type (JsonUtil.to_string typ), id))
      args arg_ids
  in
  let is_static = JsonUtil.to_bool (JsonUtil.member "is_static" m_info) in
  {
    modifier = get_modifier (JsonUtil.member "access" m_info);
    is_static;
    formal_params = (if is_static then formal_params else this :: formal_params);
    return =
      (if Utils.is_init_method method_name then ""
       else JsonUtil.member "rtype" m_info |> JsonUtil.to_string);
    filename = "";
  }

let filter_class_name ?(is_stdlib = false) class_name =
  if not is_stdlib then false
  else if
    Str.string_match Regexp.javax class_name 0
    || Str.string_match Regexp.sun class_name 0
    || Str.string_match Regexp.com class_name 0
    || Str.string_match Regexp.org class_name 0
    || Str.string_match Regexp.jdk class_name 0
  then true
  else false

let filter_method_name m_name method_map =
  MethodInfoMap.mem m_name method_map
  || List.mem m_name Utils.filter_list
  || Utils.is_lambda_method m_name

let add_missing_methods ?(is_stdlib = false) class_name info summary_map
    method_map =
  match JsonUtil.member "methods" info with
  | `Null -> (summary_map, method_map)
  | methods ->
      assoc_fold
        ~f:(fun (s_map, m_map) (m_name, m_info) ->
          if
            filter_method_name m_name method_map
            || filter_class_name ~is_stdlib class_name
          then (s_map, m_map)
          else
            let args = JsonUtil.member "args" m_info |> JsonUtil.to_list in
            let arg_ids = make_arg_id args in
            ( SummaryMap.add m_name ([ make_summary arg_ids ], []) s_map,
              MethodInfoMap.add m_name
                (get_method_info class_name m_name args arg_ids m_info)
                m_map ))
        ~init:(summary_map, method_map) methods

let mapping_inheritance_info class_name info graph =
  let super_class = JsonUtil.member "super_class" info in
  let interfaces = JsonUtil.member "interfaces" info in
  match (super_class, interfaces) with
  (* `Null | `String, `Null | `List *)
  | `Null, `Null -> graph
  | `Null, _ ->
      list_fold
        ~f:(fun g i -> G.add_edge g (JsonUtil.to_string i) class_name)
        ~init:graph interfaces
  | _, `Null -> G.add_edge graph (JsonUtil.to_string super_class) class_name
  | _, _ ->
      list_fold
        ~f:(fun g i -> G.add_edge g (JsonUtil.to_string i) class_name)
        ~init:(G.add_edge graph (JsonUtil.to_string super_class) class_name)
        interfaces

let make_type ?(is_static = false) assoc =
  let access = JsonUtil.member "access" assoc |> JsonUtil.to_string in
  let is_public = access = "public" in
  let is_private = access = "private" in
  let is_abstract = JsonUtil.member "is_abstract" assoc |> JsonUtil.to_bool in
  let is_interface = JsonUtil.member "is_interface" assoc |> JsonUtil.to_bool in
  if is_interface then if is_public then Public_Interface else Default_Interface
  else if is_public then
    if is_static && is_abstract then Public_Static_Abstract
    else if is_static then Public_Static
    else if is_abstract then Public_Abstract
    else Public
  else if is_private then
    if is_static && is_abstract then Private_Static_Abstract
    else if is_static then Private_Static
    else if is_abstract then Private_Abstract
    else Private
  else if is_static && is_abstract then Default_Static_Abstract
  else if is_static then Default_Static
  else if is_abstract then Default_Abstract
  else Default

let get_inner_class_type ic_name is_static : class_info =
  match Hashtbl.find_opt class_info ic_name with
  | None when is_static -> { class_type = Private_Static }
  | None -> { class_type = Private }
  | Some info -> { class_type = make_type ~is_static info }

let mapping_class_type_info class_name info mmap =
  if ClassInfoMap.mem class_name mmap then mmap
  else
    match JsonUtil.member "inner_class" info with
    | `Null -> (* maybe parsing error *) mmap
    | ic ->
        assoc_fold
          ~f:(fun mmap (ic_name, is_static) ->
            let is_static = JsonUtil.to_bool is_static in
            let class_type = get_inner_class_type ic_name is_static in
            ClassInfoMap.add ic_name class_type mmap)
          ~init:mmap ic
        |> ClassInfoMap.add class_name { class_type = make_type info }

let init_class_info json =
  Hashtbl.reset class_info;
  List.iter
    (fun (class_name, info) -> Hashtbl.add class_info class_name info)
    (JsonUtil.to_assoc json)

let of_json summary_map method_map json =
  init_class_info json;
  let ctype_info, i_info, (summary_map, method_map) =
    assoc_fold
      ~f:(fun (ctype_info, i_info, (s_map, m_map)) (class_name, info) ->
        ( mapping_class_type_info class_name info ctype_info,
          mapping_inheritance_info class_name info i_info,
          add_missing_methods class_name info s_map m_map ))
      ~init:(ClassInfoMap.empty, G.empty, (summary_map, method_map))
      json
  in
  ((ctype_info, GraphUtils.transitive_closure i_info), summary_map, method_map)

let of_stdlib_json ctype_info i_info smap mmap json =
  init_class_info json;
  let ctype_info, i_info, (smap, mmap) =
    assoc_fold
      ~f:(fun (ct_info, i_info, (s_map, m_map)) (class_name, info) ->
        (* early filter out unnecessary classes *)
        if filter_class_name ~is_stdlib:true class_name then
          (ct_info, i_info, (s_map, m_map))
        else
          ( mapping_class_type_info class_name info ct_info,
            mapping_inheritance_info class_name info i_info,
            add_missing_methods ~is_stdlib:true class_name info s_map m_map ))
      ~init:(ctype_info, i_info, (smap, mmap))
      json
  in
  ((ctype_info, GraphUtils.transitive_closure i_info), smap, mmap)
