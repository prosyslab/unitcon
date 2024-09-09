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

module Graphviz = Graph.Graphviz.Dot (G)
include G

let make_arg_id arg_list =
  List.fold_left
    (fun (num, lst) p ->
      let name =
        JsonUtil.to_string p |> Str.split Regexp.dot |> List.rev |> List.hd
        |> Regexp.global_rm (Str.regexp "\\[\\]")
      in
      (num + 1, (name ^ string_of_int num) :: lst))
    (1, []) arg_list
  |> snd |> List.rev

let make_var arg_list =
  let init =
    Condition.M.add (Condition.RH_Symbol "v1") (Condition.RH_Var "this")
      Condition.M.empty
  in
  List.fold_left
    (fun (num, cond) p ->
      ( num + 1,
        Condition.M.add
          (Condition.RH_Symbol ("v" ^ string_of_int num))
          (Condition.RH_Var p) cond ))
    (2, init) arg_list
  |> snd

let make_premem arg_list =
  let incr = List.length arg_list + 1 in
  let value_map = Condition.M.empty in
  let init =
    Condition.M.add (Condition.RH_Symbol "v1")
      (Condition.M.add Condition.RH_Any
         (Condition.RH_Symbol ("v" ^ (1 + incr |> string_of_int)))
         value_map)
      Condition.M.empty
  in
  let init_mem =
    List.fold_left
      (fun (num, cond) _ ->
        ( num + 1,
          Condition.M.add
            (Condition.RH_Symbol ("v" ^ string_of_int num))
            (Condition.M.add Condition.RH_Any
               (Condition.RH_Symbol ("v" ^ (num + incr |> string_of_int)))
               value_map)
            cond ))
      (2, init) arg_list
    |> snd
  in
  let arg_mem =
    List.fold_left
      (fun (num, cond) p ->
        ( num + 1,
          Condition.M.add (Condition.RH_Var p)
            (Condition.RH_Symbol ("v" ^ string_of_int num))
            cond ))
      (1 + (2 * incr), value_map)
      arg_list
    |> snd
  in
  Condition.M.add
    (Condition.RH_Symbol ("v" ^ (1 + incr |> string_of_int)))
    arg_mem init_mem

let make_postmem arg_list premem =
  let value_map = Condition.M.empty in
  let decr = List.length arg_list in
  List.fold_left
    (fun (num, cond) _ ->
      ( num + 1,
        Condition.M.add
          (Condition.RH_Symbol ("v" ^ string_of_int num))
          (Condition.M.add Condition.RH_Any
             (Condition.RH_Symbol ("v" ^ (num - decr |> string_of_int)))
             value_map)
          cond ))
    (1 + (2 * (decr + 1)), premem)
    arg_list
  |> snd

let make_summary arg_ids =
  let var = make_var arg_ids in
  let premem = make_premem arg_ids in
  let postmem = make_postmem arg_ids premem in
  {
    relation = Relation.M.empty;
    value = Value.M.empty;
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
  | _ when Str.string_match (Str.regexp ".*\\[\\]") t 0 ->
      let typ = Regexp.first_rm (Str.regexp "\\[\\]") t |> get_type in
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
  MethodInfo.
    {
      modifier = get_modifier (JsonUtil.member "access" m_info);
      is_static;
      formal_params =
        (if is_static then formal_params else this :: formal_params);
      return =
        (if Utils.is_init_method method_name then ""
         else JsonUtil.member "rtype" m_info |> JsonUtil.to_string);
      filename = "";
    }

let filter_class_name ?(is_stdlib = false) class_name =
  if not is_stdlib then false
  else if
    Str.string_match (Str.regexp "javax") class_name 0
    || Str.string_match (Str.regexp "sun") class_name 0
    || Str.string_match (Str.regexp "com") class_name 0
    || Str.string_match (Str.regexp "org") class_name 0
    || Str.string_match (Str.regexp "jdk") class_name 0
  then true
  else false

let add_missing_methods ?(is_stdlib = false) class_name info summary_map
    method_map =
  match JsonUtil.member "methods" info with
  | `Null -> (summary_map, method_map)
  | methods ->
      let filtered_m_name =
        if is_stdlib then filter_method_info methods else JsonUtil.keys methods
      in
      List.fold_left
        (fun (s_map, m_map) m_name ->
          let m_info = JsonUtil.member m_name methods in
          if
            MethodInfo.M.mem m_name method_map
            || List.mem m_name Utils.filter_list
            || filter_class_name ~is_stdlib class_name
            || Utils.is_lambda_method m_name
          then (s_map, m_map)
          else
            let args = JsonUtil.member "args" m_info |> JsonUtil.to_list in
            let arg_ids = make_arg_id args in
            ( SummaryMap.M.add m_name ([ make_summary arg_ids ], []) s_map,
              MethodInfo.M.add m_name
                (get_method_info class_name m_name args arg_ids m_info)
                m_map ))
        (summary_map, method_map) filtered_m_name

let transitive_closure vertex graph =
  let get_children v = try G.succ graph v with Invalid_argument _ -> [] in
  let rec iter children g =
    match children with
    | hd :: tl ->
        if G.mem_edge g vertex hd then iter tl g
        else G.add_edge g vertex hd |> iter tl |> iter (get_children hd)
    | [] -> g
  in
  iter
    (get_children vertex
    |> List.fold_left (fun lst v -> get_children v :: lst) []
    |> List.rev |> List.flatten)
    graph

let mapping_inheritance_info class_name info graph =
  let super_class = JsonUtil.member "super_class" info in
  let interfaces = JsonUtil.member "interfaces" info in
  match (super_class, interfaces) with
  (* `Null | `String, `Null | `List *)
  | `Null, `Null -> graph
  | `Null, _ ->
      JsonUtil.to_list interfaces
      |> List.fold_left
           (fun g i -> G.add_edge g (JsonUtil.to_string i) class_name)
           graph
  | _, `Null -> G.add_edge graph (JsonUtil.to_string super_class) class_name
  | _, _ ->
      JsonUtil.to_list interfaces
      |> List.fold_left
           (fun g i -> G.add_edge g (JsonUtil.to_string i) class_name)
           (G.add_edge graph (JsonUtil.to_string super_class) class_name)

let make_type ?(is_static = false) assoc =
  let access = JsonUtil.member "access" assoc |> JsonUtil.to_string in
  let is_public = if access = "public" then true else false in
  let is_private = if access = "private" then true else false in
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

let mapping_class_type_info class_name json mmap =
  if ClassInfo.M.mem class_name mmap then mmap
  else
    let info = JsonUtil.member class_name json in
    let mmap =
      match JsonUtil.member "inner_class" info with
      | `Null -> mmap
      | ic ->
          List.fold_left
            (fun mmap ic_name ->
              let is_static = JsonUtil.member ic_name ic |> JsonUtil.to_bool in
              match JsonUtil.member ic_name json with
              | `Null when is_static ->
                  ClassInfo.M.add ic_name
                    ClassInfo.{ class_type = Private_Static }
                    mmap
              | `Null ->
                  ClassInfo.M.add ic_name
                    ClassInfo.{ class_type = Private }
                    mmap
              | _ ->
                  let info = JsonUtil.member ic_name json in
                  ClassInfo.M.add ic_name
                    ClassInfo.{ class_type = make_type ~is_static info }
                    mmap)
            mmap (JsonUtil.keys ic)
    in
    ClassInfo.M.add class_name ClassInfo.{ class_type = make_type info } mmap

let of_json summary_map method_map json =
  let class_type_info, inheritance_info, (summary_map, method_map) =
    List.fold_left
      (fun (ct_info, i_info, (s_map, m_map)) class_name ->
        let info = JsonUtil.member class_name json in
        ( mapping_class_type_info class_name json ct_info,
          mapping_inheritance_info class_name info i_info,
          add_missing_methods class_name info s_map m_map ))
      (ClassInfo.M.empty, G.empty, (summary_map, method_map))
      (JsonUtil.keys json)
  in
  let inheritance_info =
    List.fold_left
      (fun i_info class_name -> transitive_closure class_name i_info)
      inheritance_info (JsonUtil.keys json)
  in
  ((class_type_info, inheritance_info), summary_map, method_map)

let of_stdlib_json ctinfo iinfo smap mmap json =
  let ctinfo, iinfo, (smap, mmap) =
    List.fold_left
      (fun (ct_info, i_info, (s_map, m_map)) class_name ->
        let info = JsonUtil.member class_name json in
        ( mapping_class_type_info class_name json ct_info,
          mapping_inheritance_info class_name info i_info,
          add_missing_methods ~is_stdlib:true class_name info s_map m_map ))
      (ctinfo, iinfo, (smap, mmap))
      (JsonUtil.keys json)
  in
  let iinfo =
    List.fold_left
      (fun i_info class_name -> transitive_closure class_name i_info)
      iinfo (JsonUtil.keys json)
  in
  ((ctinfo, iinfo), smap, mmap)
