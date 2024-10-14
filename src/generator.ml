open Language
module CG = Callgraph.G
module IG = Inheritance.G
module ImportSet = Utils.ImportSet

exception Not_found_setter

exception Not_found_get_object

type data = {
  cg : Callgraph.t;
  summary : SummaryMap.t;
  cp_map : CallPropMap.t;
  m_info : MethodInfo.t;
  t_info : ReturnType.t * MethodType.t;
  c_info : ClassInfo.t * Inheritance.t;
  setter_map : SetterMap.t;
  inst_info : InstanceInfo.t;
  prim_info : PrimitiveInfo.t;
}

let update_prim p_data prim_info =
  {
    cg = p_data.cg;
    summary = p_data.summary;
    cp_map = p_data.cp_map;
    m_info = p_data.m_info;
    t_info = p_data.t_info;
    c_info = p_data.c_info;
    setter_map = p_data.setter_map;
    inst_info = p_data.inst_info;
    prim_info;
  }

module ObjTypeMap = struct
  module M = Map.Make (struct
    type t = string [@@deriving compare]
  end)

  type t = string M.t
end

let obj_type_merge old_types new_types =
  ObjTypeMap.M.merge
    (fun _ v1 v2 ->
      match (v1, v2) with
      | None, None -> None
      | Some _, _ -> v1
      | None, Some _ -> v2)
    old_types new_types

module ErrorEntrySet = Set.Make (struct
  type t = string * summary

  let compare = compare
end)

module ExploredMethod = Set.Make (struct
  type t = string [@@deriving compare]
end)

let outer = ref 0

let recv = ref 0

let new_var = ref 0

let explored_m = ref ExploredMethod.empty

let z3ctx =
  Z3.mk_context
    [
      ("model", "true");
      ("proof", "true");
      ("dump_models", "true");
      ("unsat_core", "true");
    ]

let solver = Z3.Solver.mk_solver z3ctx None

let mk_some x = Some x

let mk_var x = Condition.RH_Var x

let mk_symbol x = Condition.RH_Symbol x

let mk_index x = Condition.RH_Index x

let get_type v = match v with This typ -> typ | Var (typ, _) -> typ

let get_summaries m_name map =
  match SummaryMap.M.find_opt m_name map with
  | Some (s, _) -> s
  | None -> [ empty_summary ]

let get_first_summary m_name map = get_summaries m_name map |> List.hd

let get_fields m_name map =
  match SummaryMap.M.find_opt m_name map with
  | Some (_, fields) -> fields
  | None -> []

let get_formal_params m_name map =
  match MethodInfo.M.find_opt m_name map with
  | Some info -> info.MethodInfo.formal_params
  | None -> []

let get_setters c_name map =
  match SetterMap.M.find_opt c_name map with Some lst -> lst | None -> []

let get_ret_methods typ map =
  match ReturnType.M.find_opt typ map with Some lst -> lst | None -> []

let get_methods_of_class c_name map =
  match MethodType.M.find_opt c_name map with Some lst -> lst | None -> []

let get_subtypes typ ig =
  try IG.succ ig typ |> List.cons typ with Invalid_argument _ -> [ typ ]

let is_file_obj = function
  | Object t when t = "java.io.File" -> true
  | _ -> false

let is_instream_obj = function
  | Object t when t = "java.io.InputStream" -> true
  | _ -> false

let is_outstream_obj = function
  | Object t when t = "java.io.OutputStream" -> true
  | _ -> false

let is_comparable = function
  | Object t when t = "java.lang.Comparable" -> true
  | _ -> false

let is_object = function
  | Object t when t = "java.lang.Object" -> true
  | _ -> false

let is_number = function
  | Object t when t = "java.lang.Number" -> true
  | _ -> false

let special_class_list =
  [
    "java.lang.Comparable";
    "java.lang.Object";
    "java.lang.Number";
    "java.lang.Class";
  ]

let rec find_relation given_symbol relation =
  match Relation.M.find_opt given_symbol relation with
  | Some find_symbol -> find_relation find_symbol relation
  | None -> given_symbol

let get_target_symbol id { precond = pre_var, pre_mem; _ } =
  let get_target_id_symbol mem =
    match Condition.M.find_opt (mk_var id) mem with
    | Some field_symbol -> field_symbol
    | None -> get_id_symbol pre_var id
  in
  let this_symbol = get_id_symbol pre_var "this" in
  let this_tail_symbol = get_tail_symbol "this" this_symbol pre_mem in
  match Condition.M.find_opt this_tail_symbol pre_mem with
  | None -> this_symbol
  | Some mem -> get_target_id_symbol mem

let find_variable head_symbol variables =
  match Condition.M.find_opt (mk_symbol head_symbol) variables with
  | Some var -> get_rh_name ~is_var:true var
  | None -> ""

let more_find_head_symbol head_symbol _ memory =
  let is_head_symbol _ value =
    match value with
    | Condition.RH_Symbol s when head_symbol = s -> true
    | _ -> false
  in
  Condition.M.exists is_head_symbol memory

let get_symbol_list values =
  Value.M.fold (fun symbol _ symbol_list -> symbol :: symbol_list) values []

let rec find_real_head head_symbol memory =
  let exist_head_symbol =
    Condition.M.filter (more_find_head_symbol head_symbol) memory
  in
  let find_head_symbol head _ found =
    match head with Condition.RH_Symbol s -> s | _ -> found
  in
  let exist_head_symbol =
    Condition.M.fold find_head_symbol exist_head_symbol ""
  in
  if exist_head_symbol = "" then head_symbol
  else find_real_head exist_head_symbol memory

(* (symbol, value, head)
   value is set only when the symbol is RH_Index *)
let get_head_symbol symbol mem =
  let get_heads real_head head traces lst =
    match head with
    | Condition.RH_Index i when symbol = i ->
        (symbol, get_next_symbol traces mem |> get_rh_name |> mk_some, real_head)
        :: lst
    | _ -> lst
  in
  Condition.M.fold
    (fun hd_symbol trace hd_list ->
      let hd = find_real_head (get_rh_name hd_symbol) mem in
      Condition.M.fold
        (fun trace_hd trace_tl hd_list ->
          match trace_tl with
          | Condition.RH_Symbol s when symbol = s -> [ (symbol, None, hd) ]
          | _ -> get_heads hd trace_hd trace_tl hd_list)
        trace hd_list)
    mem []

(* memory: Condition.mem *)
(* return: (callee_actual_symbol * head_symbol) list *)
(* if head = "" then this symbol can be any value *)
let get_head_symbol_list (_, memory) symbols =
  List.fold_left
    (fun list symbol ->
      let head_sym_list = get_head_symbol symbol memory in
      if head_sym_list = [] then (symbol, None, "") :: list
      else List.fold_left (fun list elem -> elem :: list) list head_sym_list)
    [] symbols

let rec get_index count tgt_v params =
  match params with
  | hd :: _ when found_param_index tgt_v hd -> count
  | _ :: tl -> get_index (count + 1) tgt_v tl
  | [] -> -1

and found_param_index tgt_v param =
  match param with
  | This _ -> false
  | Var (_, id) when id = tgt_v -> true
  | _ -> false

let get_param_index head_symbol variables formal_params =
  let variable = find_variable head_symbol variables in
  let index = get_index 0 variable formal_params in
  index

let mk_param_pair callee_sym value head_sym variables formal_params =
  match value with
  | None ->
      let idx = get_param_index head_sym variables formal_params in
      (callee_sym, head_sym, idx)
  | _ -> (callee_sym, head_sym, -1)

(* variables: Condition.var *)
(* return: (callee_actual_symbol * head_symbol * param_index) list *)
(* if param_index = -1 then this symbol can be any value *)
let get_param_index_list head_symbol_list (variables, _) formal_params =
  List.fold_left
    (fun lst (symbol, idx_value, head_symbol) ->
      if head_symbol = "" then (symbol, head_symbol, -1) :: lst
      else
        mk_param_pair symbol idx_value head_symbol variables formal_params
        :: lst)
    [] head_symbol_list
  |> List.rev

(* caller_prop: contains boitv, citv, precond, postcond, arg *)
(* return: (caller_value_symbol * callee_value_symbol) *)
let get_caller_value_symbol_list caller_prop callee_param_index_list =
  List.fold_left
    (fun lst (callee_value_symbol, _, index) ->
      if index = -1 then ("", callee_value_symbol) :: lst
      else (List.nth caller_prop.args index, callee_value_symbol) :: lst)
    [] callee_param_index_list
  |> List.rev

let mk_new_uf method_name from_s to_s m_info =
  let params =
    match MethodInfo.M.find_opt method_name m_info with
    | Some p -> p.MethodInfo.formal_params
    | _ -> []
  in
  UseFieldMap.M.fold
    (fun sym field_set new_ufset ->
      let idx = get_param_index (get_rh_name sym) (fst from_s.precond) params in
      if idx = -1 then new_ufset
      else
        let head_symbol = List.nth to_s.args idx in
        let head = find_real_head head_symbol (snd to_s.precond) |> mk_symbol in
        UseFieldMap.M.add head field_set new_ufset)
    from_s.use_field UseFieldMap.M.empty

let get_field_symbol id symbol mem =
  get_tail_symbol (get_rh_name ~is_var:true id) symbol mem

let get_params_symbol m_name m_info { precond = pre_var, pre_mem; _ } =
  let params = get_formal_params m_name m_info in
  List.fold_left
    (fun lst param ->
      match param with
      | This _ -> lst
      | Var (_, var) ->
          get_field_symbol (mk_var "") (get_id_symbol pre_var var) pre_mem
          :: lst)
    [] params

let get_value_symbol key sym c t_mem c_mem =
  let get_indirect_sym mem =
    match Condition.M.find_opt Condition.RH_Any mem with
    | Some s -> s
    | None -> Condition.RH_Any (* fail to match *)
  in
  let c_sym =
    match Condition.M.find_opt key c with
    | Some s -> s
    | None -> get_indirect_sym c
  in
  let field_name = get_rh_name ~is_var:true key in
  let tail_t_symbol = get_tail_symbol field_name sym t_mem |> get_rh_name in
  let tail_c_symbol = get_tail_symbol field_name c_sym c_mem |> get_rh_name in
  (tail_t_symbol, tail_c_symbol)

let get_matched_value_symbol t_id t_symbol t_mem c_id c_symbol c_mem =
  let t_symbol = get_field_symbol t_id (mk_symbol t_symbol) t_mem in
  let c_symbol = get_field_symbol c_id (mk_symbol c_symbol) c_mem in
  let c_t_mem = Condition.M.find_opt t_symbol t_mem in
  let c_c_mem = Condition.M.find_opt c_symbol c_mem in
  match (c_t_mem, c_c_mem) with
  | None, _ -> []
  | _, None -> []
  | Some t, Some c ->
      let get_value_symbols key sym lst =
        get_value_symbol key sym c t_mem c_mem :: lst
      in
      Condition.M.fold get_value_symbols t []

let get_value_symbol_list ~is_init t_summary c_summary vs_list =
  if is_init then
    (* this, this *)
    let t_symbol, c_symbol = List.hd vs_list in
    if c_symbol = "" then []
    else
      let t_var, t_mem = t_summary.precond in
      let c_var, c_mem = c_summary.precond in
      let c_t_mem = Condition.M.find_opt (mk_symbol t_symbol) t_var in
      let c_c_mem = Condition.M.find_opt (mk_symbol c_symbol) c_var in
      match (c_t_mem, c_c_mem) with
      | None, _ | _, None -> [ (t_symbol, c_symbol) ]
      | Some t_id, Some c_id ->
          get_matched_value_symbol t_id t_symbol t_mem c_id c_symbol c_mem
  else vs_list

let is_from_error from_func summary =
  Value.M.fold
    (fun _ v check ->
      if v.Value.from_error then if from_func then 3 else 2 else check)
    summary.value 0

let contains_used_in_error base_set target_set =
  FieldSet.fold
    (fun f check ->
      if FieldSet.mem { name = f.name; used_in_error = true } base_set then true
      else check)
    target_set false

let vmap_maker symbol target_vmap from_error =
  let value = Value.M.find symbol target_vmap in
  Value.M.add symbol Value.{ from_error; value = value.Value.value } target_vmap

let get_array_size array summary =
  let _, memory = summary.precond in
  let array_symbol = org_symbol array summary in
  match Condition.M.find_opt (mk_symbol array_symbol) memory with
  | Some x -> (true, Condition.M.fold (fun _ _ size -> size + 1) x 0)
  | None -> (false, 1)

let get_predef_value_list typ p_info =
  match PrimitiveInfo.TypeMap.find_opt typ p_info with
  | Some map -> (
      match PrimitiveInfo.ClassMap.find_opt "" map with
      | Some value -> value
      | _ -> [ "NULL" ])
  | _ -> [ "NULL" ]

let get_extra_value_list typ import p_info =
  match PrimitiveInfo.TypeMap.find_opt typ p_info with
  | Some map -> (
      let file = Regexp.first_rm (Str.regexp "\\$.*$") import in
      match
        ( PrimitiveInfo.ClassMap.find_opt import map,
          PrimitiveInfo.ClassMap.find_opt file map )
      with
      | Some value, _ -> value
      | None, Some value -> value
      | _, _ -> [])
  | _ -> []

let not_found_value v =
  match v.Value.value with Value.Eq NonValue -> true | _ -> false

let calc_value_list from_error org_list default =
  (* default value have a penalty *)
  let prec = if from_error then -2 else 0 in
  List.fold_left (fun lst x -> (prec, x) :: lst) org_list default

let check_eq_l_one ~is_le (eq_v : Value.const) (l_v : Value.const) =
  let int_l eq l =
    if is_le then if eq <= l then true else false
    else if eq < l then true
    else false
  in
  let float_l eq l =
    if is_le then if eq <= l then true else false
    else if eq < l then true
    else false
  in
  match (eq_v, l_v) with
  | Int eq, Int l | Long eq, Long l | Int eq, Long l | Long eq, Int l ->
      if int_l eq l then Some true else Some false
  | Float eq, Float l
  | Double eq, Double l
  | Float eq, Double l
  | Double eq, Float l ->
      if float_l eq l then Some true else Some false
  | _ -> None

let check_eq_g_one ~is_ge (eq_v : Value.const) (g_v : Value.const) =
  let int_g eq g =
    if is_ge then if eq >= g then true else false
    else if eq > g then true
    else false
  in
  let float_g eq g =
    if is_ge then if eq >= g then true else false
    else if eq > g then true
    else false
  in
  match (eq_v, g_v) with
  | Int eq_i, Int g_i
  | Long eq_i, Long g_i
  | Int eq_i, Long g_i
  | Long eq_i, Int g_i ->
      if int_g eq_i g_i then Some true else Some false
  | Float eq_f, Float g_f
  | Double eq_f, Double g_f
  | Float eq_f, Double g_f
  | Double eq_f, Float g_f ->
      if float_g eq_f g_f then Some true else Some false
  | _ -> None

let check_eq_btw_one (eq_v : Value.const) (btw_min : Value.const)
    (btw_max : Value.const) =
  match (eq_v, btw_min, btw_max) with
  | Int eq_i, Int btw_min_i, Int btw_max_i
  | Int eq_i, Int btw_min_i, Long btw_max_i
  | Int eq_i, Long btw_min_i, Int btw_max_i
  | Int eq_i, Long btw_min_i, Long btw_max_i
  | Long eq_i, Int btw_min_i, Int btw_max_i
  | Long eq_i, Int btw_min_i, Long btw_max_i
  | Long eq_i, Long btw_min_i, Int btw_max_i
  | Long eq_i, Long btw_min_i, Long btw_max_i ->
      if eq_i >= btw_min_i && eq_i <= btw_max_i then Some true else Some false
  | Float eq_f, Float btw_min_f, Float btw_max_f
  | Float eq_f, Float btw_min_f, Double btw_max_f
  | Float eq_f, Double btw_min_f, Float btw_max_f
  | Float eq_f, Double btw_min_f, Double btw_max_f
  | Double eq_f, Float btw_min_f, Float btw_max_f
  | Double eq_f, Float btw_min_f, Double btw_max_f
  | Double eq_f, Double btw_min_f, Float btw_max_f
  | Double eq_f, Double btw_min_f, Double btw_max_f ->
      if eq_f >= btw_min_f && eq_f <= btw_max_f then Some true else Some false
  | _ -> None

let check_eq_out_one (eq_v : Value.const) (out_min : Value.const)
    (out_max : Value.const) =
  match (eq_v, out_min, out_max) with
  | Int eq_i, Int o_min_i, Int o_max_i
  | Int eq_i, Int o_min_i, Long o_max_i
  | Int eq_i, Long o_min_i, Int o_max_i
  | Int eq_i, Long o_min_i, Long o_max_i
  | Long eq_i, Int o_min_i, Int o_max_i
  | Long eq_i, Int o_min_i, Long o_max_i
  | Long eq_i, Long o_min_i, Int o_max_i
  | Long eq_i, Long o_min_i, Long o_max_i ->
      if eq_i < o_min_i && eq_i > o_max_i then Some true else Some false
  | Float eq_f, Float o_min_f, Float o_max_f
  | Float eq_f, Float o_min_f, Double o_max_f
  | Float eq_f, Double o_min_f, Float o_max_f
  | Float eq_f, Double o_min_f, Double o_max_f
  | Double eq_f, Float o_min_f, Float o_max_f
  | Double eq_f, Float o_min_f, Double o_max_f
  | Double eq_f, Double o_min_f, Float o_max_f
  | Double eq_f, Double o_min_f, Double o_max_f ->
      if eq_f < o_min_f && eq_f > o_max_f then Some true else Some false
  | _ -> None

let check_l_g_one ~is_e (l_v : Value.const) (g_v : Value.const) =
  let int_e l g =
    if is_e then if l >= g then true else false
    else if l > g then true
    else false
  in
  let float_e l g =
    if is_e then if l >= g then true else false
    else if l > g then true
    else false
  in
  match (l_v, g_v) with
  | Int l_i, Int g_i
  | Long l_i, Long g_i
  | Int l_i, Long g_i
  | Long l_i, Int g_i ->
      if int_e l_i g_i then Some true else Some false
  | Float l_f, Float g_f
  | Double l_f, Double g_f
  | Float l_f, Double g_f
  | Double l_f, Float g_f ->
      if float_e l_f g_f then Some true else Some false
  | _ -> None

let check_l_btw_one ~is_le (l_v : Value.const) (btw_min : Value.const) =
  let int_l l btw =
    if is_le then if l < btw then true else false
    else if l <= btw then true
    else false
  in
  let float_l l btw =
    if is_le then if l < btw then true else false
    else if l <= btw then true
    else false
  in
  match (l_v, btw_min) with
  | Int l_i, Int btw_min_i
  | Long l_i, Long btw_min_i
  | Int l_i, Long btw_min_i
  | Long l_i, Int btw_min_i ->
      if int_l l_i btw_min_i then Some false else Some true
  | Float l_f, Float btw_min_f
  | Double l_f, Double btw_min_f
  | Float l_f, Double btw_min_f
  | Double l_f, Float btw_min_f ->
      if float_l l_f btw_min_f then Some false else Some true
  | _ -> None

let check_g_btw_one ~is_ge (g_v : Value.const) (btw_max : Value.const) =
  let int_g g btw =
    if is_ge then if g > btw then true else false
    else if g >= btw then true
    else false
  in
  let float_g g btw =
    if is_ge then if g > btw then true else false
    else if g >= btw then true
    else false
  in
  match (g_v, btw_max) with
  | Int g_i, Int btw_max_i
  | Long g_i, Long btw_max_i
  | Int g_i, Long btw_max_i
  | Long g_i, Int btw_max_i ->
      if int_g g_i btw_max_i then Some false else Some true
  | Float g_f, Float btw_max_f
  | Double g_f, Double btw_max_f
  | Float g_f, Double btw_max_f
  | Double g_f, Float btw_max_f ->
      if float_g g_f btw_max_f then Some false else Some true
  | _ -> None

let check_btw_btw_one (caller_min : Value.const) (caller_max : Value.const)
    (callee_min : Value.const) (callee_max : Value.const) =
  match (caller_min, caller_max, callee_min, callee_max) with
  | Int r_min_i, Int r_max_i, Int e_min_i, Int e_max_i
  | Int r_min_i, Int r_max_i, Int e_min_i, Long e_max_i
  | Int r_min_i, Int r_max_i, Long e_min_i, Int e_max_i
  | Int r_min_i, Long r_max_i, Int e_min_i, Int e_max_i
  | Int r_min_i, Int r_max_i, Long e_min_i, Long e_max_i
  | Int r_min_i, Long r_max_i, Int e_min_i, Long e_max_i
  | Int r_min_i, Long r_max_i, Long e_min_i, Int e_max_i
  | Int r_min_i, Long r_max_i, Long e_min_i, Long e_max_i
  | Long r_min_i, Int r_max_i, Int e_min_i, Int e_max_i
  | Long r_min_i, Int r_max_i, Int e_min_i, Long e_max_i
  | Long r_min_i, Int r_max_i, Long e_min_i, Int e_max_i
  | Long r_min_i, Long r_max_i, Int e_min_i, Int e_max_i
  | Long r_min_i, Int r_max_i, Long e_min_i, Long e_max_i
  | Long r_min_i, Long r_max_i, Int e_min_i, Long e_max_i
  | Long r_min_i, Long r_max_i, Long e_min_i, Int e_max_i
  | Long r_min_i, Long r_max_i, Long e_min_i, Long e_max_i ->
      if r_max_i < e_min_i || e_max_i < r_min_i then Some false else Some true
  | Float r_min_f, Float r_max_f, Float e_min_f, Float e_max_f
  | Float r_min_f, Float r_max_f, Float e_min_f, Double e_max_f
  | Float r_min_f, Float r_max_f, Double e_min_f, Float e_max_f
  | Float r_min_f, Double r_max_f, Float e_min_f, Float e_max_f
  | Float r_min_f, Float r_max_f, Double e_min_f, Double e_max_f
  | Float r_min_f, Double r_max_f, Float e_min_f, Double e_max_f
  | Float r_min_f, Double r_max_f, Double e_min_f, Float e_max_f
  | Float r_min_f, Double r_max_f, Double e_min_f, Double e_max_f
  | Double r_min_f, Float r_max_f, Float e_min_f, Float e_max_f
  | Double r_min_f, Float r_max_f, Float e_min_f, Double e_max_f
  | Double r_min_f, Float r_max_f, Double e_min_f, Float e_max_f
  | Double r_min_f, Double r_max_f, Float e_min_f, Float e_max_f
  | Double r_min_f, Float r_max_f, Double e_min_f, Double e_max_f
  | Double r_min_f, Double r_max_f, Float e_min_f, Double e_max_f
  | Double r_min_f, Double r_max_f, Double e_min_f, Float e_max_f
  | Double r_min_f, Double r_max_f, Double e_min_f, Double e_max_f ->
      if r_max_f < e_min_f || e_max_f < r_min_f then Some false else Some true
  | _ -> None

let check_btw_out_one (btw_min : Value.const) (btw_max : Value.const)
    (out_min : Value.const) (out_max : Value.const) =
  match (btw_min, btw_max, out_min, out_max) with
  | Int btw_min_i, Int btw_max_i, Int o_min_i, Int o_max_i
  | Int btw_min_i, Int btw_max_i, Int o_min_i, Long o_max_i
  | Int btw_min_i, Int btw_max_i, Long o_min_i, Int o_max_i
  | Int btw_min_i, Long btw_max_i, Int o_min_i, Int o_max_i
  | Int btw_min_i, Int btw_max_i, Long o_min_i, Long o_max_i
  | Int btw_min_i, Long btw_max_i, Int o_min_i, Long o_max_i
  | Int btw_min_i, Long btw_max_i, Long o_min_i, Int o_max_i
  | Int btw_min_i, Long btw_max_i, Long o_min_i, Long o_max_i
  | Long btw_min_i, Int btw_max_i, Int o_min_i, Int o_max_i
  | Long btw_min_i, Int btw_max_i, Int o_min_i, Long o_max_i
  | Long btw_min_i, Int btw_max_i, Long o_min_i, Int o_max_i
  | Long btw_min_i, Long btw_max_i, Int o_min_i, Int o_max_i
  | Long btw_min_i, Int btw_max_i, Long o_min_i, Long o_max_i
  | Long btw_min_i, Long btw_max_i, Int o_min_i, Long o_max_i
  | Long btw_min_i, Long btw_max_i, Long o_min_i, Int o_max_i
  | Long btw_min_i, Long btw_max_i, Long o_min_i, Long o_max_i ->
      if o_min_i <= btw_min_i && o_max_i >= btw_max_i then Some false
      else Some true
  | Float btw_min_f, Float btw_max_f, Float o_min_f, Float o_max_f
  | Float btw_min_f, Float btw_max_f, Float o_min_f, Double o_max_f
  | Float btw_min_f, Float btw_max_f, Double o_min_f, Float o_max_f
  | Float btw_min_f, Double btw_max_f, Float o_min_f, Float o_max_f
  | Float btw_min_f, Float btw_max_f, Double o_min_f, Double o_max_f
  | Float btw_min_f, Double btw_max_f, Float o_min_f, Double o_max_f
  | Float btw_min_f, Double btw_max_f, Double o_min_f, Float o_max_f
  | Float btw_min_f, Double btw_max_f, Double o_min_f, Double o_max_f
  | Double btw_min_f, Float btw_max_f, Float o_min_f, Float o_max_f
  | Double btw_min_f, Float btw_max_f, Float o_min_f, Double o_max_f
  | Double btw_min_f, Float btw_max_f, Double o_min_f, Float o_max_f
  | Double btw_min_f, Double btw_max_f, Float o_min_f, Float o_max_f
  | Double btw_min_f, Float btw_max_f, Double o_min_f, Double o_max_f
  | Double btw_min_f, Double btw_max_f, Float o_min_f, Double o_max_f
  | Double btw_min_f, Double btw_max_f, Double o_min_f, Float o_max_f
  | Double btw_min_f, Double btw_max_f, Double o_min_f, Double o_max_f ->
      if btw_min_f <= o_min_f && btw_max_f >= o_max_f then Some false
      else Some true
  | _ -> None

let calc_z3_value value =
  match value with
  | Some v ->
      if Z3.Arithmetic.is_real v then Z3.Arithmetic.Real.numeral_to_string v
      else Z3.Arithmetic.Integer.numeral_to_string v
  | None -> ""

let calc_z3 id z3exp =
  let solver = Z3.Solver.mk_solver z3ctx None in
  Z3.Solver.add solver z3exp;
  let _ = Z3.Solver.check solver [] in
  match Z3.Solver.get_model solver with
  | Some m ->
      let value = Z3.Model.eval m id false in
      calc_z3_value value
  | None -> ""

let get_z3_val (v : Value.const) =
  match v with
  | Int i | Long i | Short i | Byte i ->
      Z3.Arithmetic.Integer.mk_numeral_i z3ctx i
  | Float f | Double f ->
      Z3.Arithmetic.Real.mk_numeral_s z3ctx (string_of_float f)
  | _ -> failwith "not implemented other number"

let get_z3_id (v : Value.const) id =
  match v with
  | Int _ | Long _ | Short _ | Byte _ ->
      Z3.Arithmetic.Integer.mk_const_s z3ctx id
  | Float _ | Double _ -> Z3.Arithmetic.Real.mk_const_s z3ctx id
  | _ -> failwith "not implemented other number"

let get_z3_result (op : Value.op) id =
  match op with
  | Eq v ->
      let var = get_z3_id v id in
      calc_z3 var [ Z3.Boolean.mk_eq z3ctx var (get_z3_val v) ]
  | Neq v ->
      let var = get_z3_id v id in
      calc_z3 var
        [ Z3.Boolean.mk_eq z3ctx var (get_z3_val v) |> Z3.Boolean.mk_not z3ctx ]
  | Le v ->
      let var = get_z3_id v id in
      calc_z3 var [ Z3.Arithmetic.mk_le z3ctx var (get_z3_val v) ]
  | Lt v ->
      let var = get_z3_id v id in
      calc_z3 var [ Z3.Arithmetic.mk_lt z3ctx var (get_z3_val v) ]
  | Ge v ->
      let var = get_z3_id v id in
      calc_z3 var [ Z3.Arithmetic.mk_ge z3ctx var (get_z3_val v) ]
  | Gt v ->
      let var = get_z3_id v id in
      calc_z3 var [ Z3.Arithmetic.mk_gt z3ctx var (get_z3_val v) ]
  | Between (v1, v2) ->
      let var = get_z3_id v1 id in
      calc_z3 var
        [
          Z3.Arithmetic.mk_ge z3ctx var (get_z3_val v1);
          Z3.Arithmetic.mk_le z3ctx var (get_z3_val v2);
        ]
  | Outside (v1, v2) ->
      let var = get_z3_id v1 id in
      calc_z3 var
        [
          Z3.Arithmetic.mk_lt z3ctx var (get_z3_val v1);
          Z3.Arithmetic.mk_gt z3ctx var (get_z3_val v2);
        ]

let find_target_var sym_trace find_var =
  Condition.M.fold
    (fun trace_hd _ trace_find_var ->
      match trace_hd with
      | Condition.RH_Var var -> mk_some var
      | _ -> trace_find_var)
    sym_trace find_var

let get_target_var t_sym mem =
  Condition.M.fold
    (fun symbol symbol_trace find_variable ->
      if get_rh_name symbol = t_sym then
        find_target_var symbol_trace find_variable
      else find_variable)
    mem None

let get_symbol_num symbol =
  match
    Regexp.first_rm Regexp.symbol (get_rh_name symbol) |> int_of_string_opt
  with
  | Some i -> i
  | _ -> 0

let get_fresh_num prev_num = prev_num + 1

let find_value_from_variable memory value target_variable =
  let get_tail_symbol _ trace found =
    match trace with Condition.RH_Symbol s -> s | _ -> found
  in
  let target_variable =
    Condition.M.fold
      (fun symbol symbol_trace find_variable ->
        let symbol = get_rh_name symbol in
        if symbol = target_variable then
          Condition.M.fold get_tail_symbol symbol_trace find_variable
        else find_variable)
      memory target_variable
  in
  Value.M.fold
    (fun symbol value find_value ->
      if symbol = target_variable then value else find_value)
    value
    Value.{ from_error = false; value = Value.Eq NonValue }

let find_target_value id { precond = pre_var, pre_mem; value; _ } =
  Condition.M.fold
    (fun symbol variable find_variable ->
      match variable with
      | Condition.RH_Var var when var = id -> (
          match symbol with Condition.RH_Symbol s -> s | _ -> find_variable)
      | _ -> find_variable)
    pre_var ""
  |> find_value_from_variable pre_mem value

let find_target_value_from_this id summary =
  let get_directed_field_symbol field symbol found =
    match field with
    | Condition.RH_Var v when v = id -> get_rh_name symbol
    | _ -> found
  in
  let this_sym default =
    match
      Condition.M.find_opt
        (org_symbol "this" summary |> mk_symbol)
        (snd summary.precond)
    with
    | Some this_mem ->
        Condition.M.fold get_directed_field_symbol this_mem default
    | _ -> default
  in
  this_sym "" |> find_value_from_variable (snd summary.precond) summary.value

let get_p_value p s =
  match p with
  | Var (_, id) -> find_target_value id s
  | _ -> failwith "Fail: find the target value"

let n_forward n start start_map =
  let key_compare (k1 : Condition.rh) (k2 : Condition.rh) =
    match (k1, k2) with
    | RH_Symbol _, RH_Symbol _ -> get_symbol_num k1 < get_symbol_num k2
    | _ -> false
  in
  let collect_key org_key map =
    Condition.M.fold
      (fun field k lst ->
        if key_compare org_key k then (org_key, field, k) :: lst else lst)
      map []
  in
  let find_key key map =
    match Condition.M.find_opt key map with
    | Some value -> collect_key key value
    | _ -> []
  in
  let get_matched_keys keys =
    List.fold_left
      (fun lst (_, _, k) -> find_key k start_map |> List.rev_append lst)
      [] keys
  in
  let rec forwards count key_list =
    if count >= n then key_list
    else
      let keys = get_matched_keys key_list in
      forwards (count + 1) keys
  in
  forwards 1 (find_key start start_map)

let check_new_value symbol vmap memory =
  let exist_field_value field value =
    match
      Value.M.find_opt (get_field_symbol field value memory |> get_rh_name) vmap
    with
    | Some _ -> true
    | _ -> false
  in
  let checker mem =
    Condition.M.fold
      (fun field value check ->
        let chk = exist_field_value field value in
        if chk then true else check)
      mem false
  in
  match Condition.M.find_opt symbol memory with
  | Some x -> checker x
  | _ -> false

let check_intersect_one caller_sym callee_sym caller_prop callee_summary =
  try
    let caller_value = Value.M.find caller_sym caller_prop.value in
    let callee_value = Value.M.find callee_sym callee_summary.value in
    let return_caller check =
      if check then
        ( (caller_value.Value.from_error || callee_value.Value.from_error)
          |> vmap_maker caller_sym caller_prop.value,
          check )
      else (caller_prop.value, check)
    in
    let get_result check_opt =
      match check_opt with
      | Some check -> return_caller check
      | _ -> (Value.M.empty, false)
    in
    match (caller_value.Value.value, callee_value.Value.value) with
    | Eq eq_v1, Eq eq_v2 ->
        if eq_v1 = eq_v2 then return_caller true else return_caller false
    | Eq eq_v, Neq neq_v | Neq neq_v, Eq eq_v ->
        if eq_v = neq_v then return_caller false else return_caller true
    | Eq eq_v, Le le_v | Le le_v, Eq eq_v ->
        check_eq_l_one ~is_le:true eq_v le_v |> get_result
    | Eq eq_v, Lt lt_v | Lt lt_v, Eq eq_v ->
        check_eq_l_one ~is_le:false eq_v lt_v |> get_result
    | Eq eq_v, Ge ge_v | Ge ge_v, Eq eq_v ->
        check_eq_g_one ~is_ge:true eq_v ge_v |> get_result
    | Eq eq_v, Gt gt_v | Gt gt_v, Eq eq_v ->
        check_eq_g_one ~is_ge:false eq_v gt_v |> get_result
    | Eq eq_v, Between (btw_min, btw_max) | Between (btw_min, btw_max), Eq eq_v
      ->
        check_eq_btw_one eq_v btw_min btw_max |> get_result
    | Eq eq_v, Outside (out_min, out_max) | Outside (out_min, out_max), Eq eq_v
      ->
        check_eq_out_one eq_v out_min out_max |> get_result
    | Le le_v, Ge ge_v | Ge ge_v, Le le_v ->
        check_l_g_one ~is_e:true le_v ge_v |> get_result
    | Le l_v, Gt g_v
    | Lt l_v, Ge g_v
    | Lt l_v, Gt g_v
    | Ge g_v, Lt l_v
    | Gt g_v, Le l_v
    | Gt g_v, Lt l_v ->
        check_l_g_one ~is_e:false l_v g_v |> get_result
    | Le le_v, Between (btw_min, _) | Between (btw_min, _), Le le_v ->
        check_l_btw_one ~is_le:true le_v btw_min |> get_result
    | Lt lt_v, Between (btw_min, _) | Between (btw_min, _), Lt lt_v ->
        check_l_btw_one ~is_le:false lt_v btw_min |> get_result
    | Ge ge_v, Between (_, btw_max) | Between (_, btw_max), Ge ge_v ->
        check_g_btw_one ~is_ge:true ge_v btw_max |> get_result
    | Gt gt_v, Between (_, btw_max) | Between (_, btw_max), Gt gt_v ->
        check_g_btw_one ~is_ge:false gt_v btw_max |> get_result
    | Between (r_min, r_max), Between (e_min, e_max) ->
        check_btw_btw_one r_min r_max e_min e_max |> get_result
    | Between (btw_min, btw_max), Outside (out_min, out_max)
    | Outside (out_min, out_max), Between (btw_min, btw_max) ->
        check_btw_out_one btw_min btw_max out_min out_max |> get_result
    | _, Outside _
    | Outside _, _
    | Lt _, Le _
    | Lt _, Lt _
    | Le _, Le _
    | Le _, Lt _
    | Gt _, Ge _
    | Gt _, Gt _
    | Ge _, Ge _
    | Ge _, Gt _
    | Neq _, _
    | _, Neq _ ->
        return_caller true
  with Not_found -> (
    try
      let callee_value = Value.M.find callee_sym callee_summary.value in
      ( Value.M.add caller_sym callee_value caller_prop.value
        |> Value.M.add callee_sym callee_value,
        true )
    with Not_found -> (
      try
        (* constructor prop propagation *)
        let caller_value = Value.M.find caller_sym caller_prop.value in
        (Value.M.add callee_sym caller_value callee_summary.value, true)
      with Not_found -> (caller_prop.value, true)))

let check_intersect ~is_init caller_prop callee_summary vs_list =
  let vs_list =
    get_value_symbol_list ~is_init caller_prop callee_summary vs_list
  in
  List.fold_left
    (fun lst (caller_symbol, callee_symbol) ->
      check_intersect_one caller_symbol callee_symbol caller_prop callee_summary
      :: lst)
    [] vs_list
  |> List.rev

(* value_sym_list: (caller, callee) list
   callee_sym_list: (symbol, value, head) list --> value is set only when symbol is index *)
let combine_memory { precond = _, pre_mem; _ } value_sym_list callee_sym_list =
  let combine r s value trace org_mem =
    Condition.M.add (mk_symbol r)
      (Condition.M.add (mk_index s) (mk_symbol value) trace)
      org_mem
  in
  let combine_memory r s value head mem =
    match Condition.M.find_opt (mk_symbol r) mem with
    | Some m when find_real_head r pre_mem = head -> combine r s value m mem
    | None when find_real_head r pre_mem = head ->
        combine r s value Condition.M.empty mem
    | _ -> mem
  in
  let iter_callee r mem =
    List.fold_left
      (fun mem (s, v, head) ->
        match v with
        | Some value -> combine_memory r s value head mem
        | _ -> mem)
      mem callee_sym_list
  in
  List.fold_left (fun mem (r, _) -> iter_callee r mem) pre_mem value_sym_list

let combine_value base_value vc_list =
  let merge_f _ v1 v2 =
    match (v1, v2) with
    | None, None -> None
    | Some _, _ -> v1
    | None, Some _ -> v2
  in
  List.fold_left
    (fun prop_values (prop_value, _) ->
      Value.M.merge merge_f prop_values prop_value)
    base_value vc_list

let satisfy callee_method callee_summary call_prop m_info =
  let callee_head_symbols =
    get_symbol_list callee_summary.value
    |> get_head_symbol_list callee_summary.precond
  in
  let value_symbol_list =
    (MethodInfo.M.find callee_method m_info).MethodInfo.formal_params
    |> get_param_index_list callee_head_symbols callee_summary.precond
    |> get_caller_value_symbol_list call_prop
  in
  let caller_new_mem =
    combine_memory call_prop value_symbol_list callee_head_symbols
  in
  let intersect_value =
    let values_and_check =
      check_intersect ~is_init:false call_prop callee_summary value_symbol_list
    in
    ( combine_value call_prop.value values_and_check,
      List.filter (fun (_, c) -> c = false) values_and_check )
  in
  if snd intersect_value = [] then (fst intersect_value, caller_new_mem, true)
  else (fst intersect_value, caller_new_mem, false)

let new_value_summary new_value old_summary =
  {
    relation = old_summary.relation;
    value = new_value;
    use_field = old_summary.use_field;
    precond = old_summary.precond;
    postcond = old_summary.postcond;
    args = old_summary.args;
  }

let new_mem_summary new_mem old_summary =
  {
    relation = old_summary.relation;
    value = old_summary.value;
    use_field = old_summary.use_field;
    precond = (fst old_summary.precond, new_mem);
    postcond = (fst old_summary.postcond, new_mem);
    args = old_summary.args;
  }

let new_uf_summary new_uf old_summary =
  {
    relation = old_summary.relation;
    value = old_summary.value;
    use_field = new_uf;
    precond = old_summary.precond;
    postcond = old_summary.postcond;
    args = old_summary.args;
  }

let add_new_mmap f1 f2 org_key field map =
  match Condition.M.find_opt org_key map with
  | Some x ->
      Condition.M.add org_key
        (Condition.M.add (get_rh_name ~is_var:true field |> mk_var) f1 x)
        map
      |> Condition.M.add f1 (Condition.M.add RH_Any f2 Condition.M.empty)
  | _ ->
      Condition.M.add org_key
        (Condition.M.add
           (get_rh_name ~is_var:true field |> mk_var)
           f1 Condition.M.empty)
        map
      |> Condition.M.add f1 (Condition.M.add RH_Any f2 Condition.M.empty)

let mk_new_memory org_key t_key_lst t_summary new_mem =
  let func (sym, value, new_pre_mem, new_post_mem) (_, field, key) =
    let field_name = get_rh_name ~is_var:true field in
    if field_name = "" then (sym, value, new_pre_mem, new_post_mem)
    else
      let fn1 = get_fresh_num 1 in
      let fn2 = get_fresh_num fn1 in
      let fv1 = string_of_int fn1 |> String.cat "u" |> mk_symbol in
      let fv2 = string_of_int fn2 |> String.cat "u" |> mk_symbol in
      let new_value =
        let s = get_tail_symbol "" key (snd t_summary.precond) |> get_rh_name in
        match Value.M.find_opt s t_summary.value with
        | Some v -> v
        | None -> value
      in
      let new_pre_mem = add_new_mmap fv1 fv2 org_key field new_pre_mem in
      let new_post_mem = add_new_mmap fv1 fv2 org_key field new_post_mem in
      (fv2, new_value, new_pre_mem, new_post_mem)
  in
  List.fold_left func new_mem t_key_lst

let get_origin_key count this_symbol condition =
  if count = 1 then this_symbol
  else
    let keys = n_forward (count - 1) this_symbol (snd condition) in
    let key, _, _ = List.hd keys in
    key

let rec forward count var_symbol this_symbol t_summary c_summary new_memory =
  let t_key_list = n_forward count var_symbol (snd t_summary.precond) in
  let c_key_list = n_forward count this_symbol (snd c_summary.postcond) in
  if t_key_list = [] then new_memory
  else if List.length t_key_list = List.length c_key_list then
    forward (count + 1) var_symbol this_symbol t_summary c_summary new_memory
  else
    let c_org_key = get_origin_key count this_symbol c_summary.postcond in
    mk_new_memory c_org_key t_key_list t_summary new_memory

let modify_summary id t_summary c_summary =
  let id = if id = "con_recv" then "this" else id in
  let var_symbol = org_symbol id t_summary |> mk_symbol in
  let this_symbol = org_symbol "this" c_summary |> mk_symbol in
  if check_new_value var_symbol t_summary.value (snd t_summary.precond) |> not
  then c_summary
  else
    let default_value = Value.{ from_error = false; value = Eq NonValue } in
    let symbol, value, pre_mem, post_mem =
      forward 1 var_symbol this_symbol t_summary c_summary
        (RH_Any, default_value, snd c_summary.precond, snd c_summary.postcond)
    in
    {
      relation = c_summary.relation;
      value =
        (if value = default_value then c_summary.value
         else Value.M.add (get_rh_name symbol) value c_summary.value);
      use_field = c_summary.use_field;
      precond = (fst c_summary.precond, pre_mem);
      postcond = (fst c_summary.postcond, post_mem);
      args = c_summary.args;
    }

let new_this_summary old_summary values =
  let this_symbol = org_symbol "this" old_summary |> mk_symbol in
  let new_mem mem =
    Condition.M.find this_symbol mem
    |> Condition.M.add
         (fst values |> fst |> mk_index)
         (snd values |> fst |> mk_symbol)
  in
  let new_premem = new_mem (snd old_summary.precond) in
  let new_postmem = new_mem (snd old_summary.postcond) in
  {
    relation = old_summary.relation;
    value =
      Value.M.add (fst values |> fst) (fst values |> snd) old_summary.value
      |> Value.M.add (snd values |> fst) (snd values |> snd);
    use_field = old_summary.use_field;
    precond =
      ( fst old_summary.precond,
        Condition.M.add this_symbol new_premem (snd old_summary.precond) );
    postcond =
      ( fst old_summary.postcond,
        Condition.M.add this_symbol new_postmem (snd old_summary.postcond) );
    args = old_summary.args;
  }

let modify_array_summary id t_summary a_summary =
  let from_error, value = get_array_size id t_summary in
  let new_value =
    Value.M.add
      (org_symbol "size" a_summary)
      Value.{ from_error; value = Value.Ge (Int value) }
      a_summary.value
  in
  let rec mk_new_summary new_summary summary =
    let tmp = get_array_index id summary in
    if fst tmp |> fst = "" then (new_summary, summary)
    else
      let new_mem = remove_array_index id (fst tmp |> fst) summary in
      mk_new_summary
        (new_this_summary new_summary tmp)
        (new_mem_summary new_mem summary)
  in
  mk_new_summary (new_value_summary new_value a_summary) t_summary |> fst

let is_receiver id = if id = "con_recv" || id = "con_outer" then true else false

let is_nested_class name = String.contains name '$'

let is_test_file f_name = Str.string_match (Str.regexp ".*/test/.*") f_name 0

let is_public_class class_name c_info =
  let is_public_class_type typ =
    match typ.ClassInfo.class_type with
    | Public | Public_Static | Public_Static_Abstract | Public_Abstract -> true
    | _ -> false
  in
  match ClassInfo.M.find_opt class_name c_info with
  | Some typ -> is_public_class_type typ
  | None -> true (* modeling class *)

let is_abstract_class class_name (c_info, _) =
  let is_abstract_class_type typ =
    match typ.ClassInfo.class_type with
    | Public_Abstract | Public_Static_Abstract | Private_Abstract
    | Private_Static_Abstract | Default_Abstract | Default_Static_Abstract ->
        true
    | _ -> false
  in
  match ClassInfo.M.find_opt class_name c_info with
  | Some typ -> is_abstract_class_type typ
  | _ -> false

let is_usable_default_class class_name c_info =
  let is_usable_default_class_type typ =
    match typ.ClassInfo.class_type with
    | (Default | Default_Static | Default_Static_Abstract | Default_Abstract)
      when !Cmdline.extension = Utils.get_package_name class_name ->
        true
    | _ -> false
  in
  if !Cmdline.extension = "" then false
  else
    match ClassInfo.M.find_opt class_name c_info with
    | Some typ -> is_usable_default_class_type typ
    | None -> false

let is_static_class name (c_info, _) =
  let is_static_class_type typ =
    match typ.ClassInfo.class_type with
    | Public_Static | Public_Static_Abstract -> true
    | (Default_Static | Default_Static_Abstract)
      when !Cmdline.extension <> ""
           && !Cmdline.extension = Utils.get_package_name name ->
        true
    | _ -> false
  in
  let name =
    Regexp.global_rm (Str.regexp "\\.<.*>(.*)$") name
    |> Regexp.global_rm (Str.regexp "(.*)$")
  in
  match ClassInfo.M.find_opt name c_info with
  | Some typ -> is_static_class_type typ
  | None -> false

let is_private_class class_package c_info =
  let is_private_class_type typ =
    match typ.ClassInfo.class_type with
    | Private | Private_Static | Private_Abstract | Private_Static_Abstract ->
        true
    | _ -> false
  in
  match ClassInfo.M.find_opt class_package (fst c_info) with
  | Some typ -> is_private_class_type typ
  | None -> false

let is_available_class name c_info =
  let is_available_class_type typ =
    match typ.ClassInfo.class_type with
    | Public | Public_Static -> true
    | _ -> false
  in
  match ClassInfo.M.find_opt name c_info with
  | Some typ -> is_available_class_type typ
  | _ -> true

let is_static m_name m_info =
  match MethodInfo.M.find_opt m_name m_info with
  | None -> false
  | Some info -> info.MethodInfo.is_static

let is_private m_name m_info =
  let is_private_method info =
    match info.MethodInfo.modifier with Private -> true | _ -> false
  in
  match MethodInfo.M.find_opt m_name m_info with
  | None -> false
  | Some info -> is_private_method info

let is_public m_name m_info =
  let is_public_method ?(is_test = false) info =
    match info.MethodInfo.modifier with
    | Public when not is_test -> true
    | _ -> false
  in
  match MethodInfo.M.find_opt m_name m_info with
  | None -> false
  | Some info ->
      (* If this method is a method in the test file,
         don't use it even if the modifier is public *)
      is_public_method ~is_test:(is_test_file info.MethodInfo.filename) info

let is_usable_default m_name m_info =
  let is_usable_default_method ?(is_test = false) info =
    let pkg = Utils.get_class_name m_name |> Utils.get_package_name in
    match info.MethodInfo.modifier with
    | (Default | Protected) when !Cmdline.extension = pkg && not is_test -> true
    | _ -> false
  in
  if !Cmdline.extension = "" then false
  else
    match MethodInfo.M.find_opt m_name m_info with
    | None -> false
    | Some info ->
        (* If this method is a method in the test file,
           don't use it even if the modifier is public or usable default *)
        is_usable_default_method
          ~is_test:(is_test_file info.MethodInfo.filename)
          info

let is_abstract m_name class_name_list m_info c_info =
  let target_class = Utils.get_class_name m_name in
  let m_name =
    Regexp.first_rm
      ("^" ^ Str.global_replace Regexp.dot "\\." target_class |> Str.regexp)
      m_name
  in
  if is_abstract_class target_class c_info |> not then false
  else
    List.fold_left
      (fun check class_name ->
        if class_name = target_class then check
        else if MethodInfo.M.mem (class_name ^ m_name) m_info then
          (* When the method is in an abstract class and child classes implement the method,
             this method is likely an abstract *)
          true
        else check)
      false class_name_list

let match_constructor_name class_name method_name =
  let class_name = Str.global_replace Regexp.dollar "\\$" class_name in
  Str.string_match (class_name ^ "\\.<init>" |> Str.regexp) method_name 0

let match_return_object class_name method_name m_info =
  let info = MethodInfo.M.find method_name m_info in
  let return = info.MethodInfo.return in
  String.equal class_name return

let is_available_method m_name m_info =
  (is_public m_name m_info || is_usable_default m_name m_info)
  && Utils.is_anonymous m_name |> not

let is_usable_method m_name m_info c_info =
  (is_public_class (Utils.get_class_name m_name) c_info
  || is_usable_default_class (Utils.get_class_name m_name) c_info)
  && is_available_method m_name m_info

let is_usable_constructor c_name m_name c_info ig =
  is_abstract_class c_name (c_info, ig) |> not
  && match_constructor_name c_name m_name

let is_usable_getter c_name m_name classes m_info c_info ig =
  match_return_object c_name m_name m_info
  && is_abstract m_name classes m_info (c_info, ig) |> not
  && Utils.is_init_method m_name |> not

let is_same_summary s1 s2 =
  let all_equal std op =
    Condition.M.fold
      (fun k v eq ->
        match Condition.M.find_opt k op with
        | Some v2 when v = v2 -> eq
        | _ -> false)
      std true
  in
  let equal v1 v2 = all_equal v1 v2 && all_equal v2 v1 in
  if Condition.M.equal equal (snd s1.postcond) (snd s2.postcond) then true
  else false

let rec check_param p1 p2 =
  match (p1, p2) with
  | v1 :: tl1, v2 :: tl2 ->
      if check_one_var v1 v2 then check_param tl1 tl2 else false
  | _ :: _, [] -> false
  | [], _ :: _ -> false
  | [], [] -> true

and check_one_var v1 v2 =
  match (v1, v2) with
  | Var (typ1, _), Var (typ2, _) when typ1 = typ2 -> true
  | This _, This _ -> true
  | _, _ -> false

let is_same_param_type c1 c2 m_info =
  let c1_info = MethodInfo.M.find c1 m_info in
  let c2_info = MethodInfo.M.find c2 m_info in
  check_param c1_info.MethodInfo.formal_params c2_info.MethodInfo.formal_params

let rec collect_dup_setter lst =
  match lst with
  | (_, _, h) :: t ->
      List.filter (fun (_, _, x) -> is_same_summary h x) t
      |> List.rev_append (collect_dup_setter t)
  | _ -> []

let prune_dup_summary_setter lst =
  if !Cmdline.basic_mode || !Cmdline.priority_mode then List.rev lst
  else
    List.fold_left
      (fun l s -> if collect_dup_setter lst |> List.mem s then l else s :: l)
      [] lst

let rec collect_dup m_info lst =
  match lst with
  | (_, ch, h) :: t ->
      List.filter
        (fun (_, cx, x) ->
          is_same_summary h x && is_same_param_type ch cx m_info)
        t
      |> List.rev_append (collect_dup m_info t)
  | _ -> []

let prune_dup_summary m_info lst =
  if !Cmdline.basic_mode || !Cmdline.priority_mode then List.rev lst
  else
    List.fold_left
      (fun l s -> if collect_dup m_info lst |> List.mem s then l else s :: l)
      [] lst

let get_package_from_v v =
  let rec get_object_from_array array =
    match array with Array a -> get_object_from_array a | _ -> array
  in
  let rec get_package = function
    | Int | Long | Short | Byte | Float | Double | Bool | Char | NonType -> ""
    | String -> "java.lang.String"
    | Array a -> get_object_from_array a |> get_package
    | Object t -> t
  in
  get_package (get_type v)

let is_recursive_param parent_class method_name m_info =
  let info = MethodInfo.M.find method_name m_info in
  let this = Object parent_class in
  List.fold_left
    (fun check var ->
      match var with Var (typ, _) when typ = this -> true | _ -> check)
    false info.MethodInfo.formal_params

let contains_symbol symbol memory =
  let inner_contains_symbol mem =
    Condition.M.fold
      (fun _ hd check -> if hd = symbol then true else check)
      mem false
  in
  match Condition.M.find_opt symbol memory with
  | Some _ -> true
  | _ ->
      Condition.M.fold
        (fun _ hd check -> check || inner_contains_symbol hd)
        memory false

let get_m_lst_from_one_c c_name m_name m_info c_info ig tgt_c_lst
    (org_c_lst, c_lst, ret_c_lst) tgt_c_name =
  if is_usable_method m_name m_info c_info then
    if is_usable_constructor tgt_c_name m_name c_info ig then
      if c_name = tgt_c_name then
        (m_name :: org_c_lst, m_name :: c_lst, ret_c_lst)
      else (org_c_lst, m_name :: c_lst, ret_c_lst)
    else if is_usable_getter tgt_c_name m_name tgt_c_lst m_info c_info ig then
      (org_c_lst, c_lst, m_name :: ret_c_lst)
    else (org_c_lst, c_lst, ret_c_lst)
  else (org_c_lst, c_lst, ret_c_lst)

let summary_filtering name m_info list =
  List.filter
    (fun (_, c, _) -> is_public c m_info || is_usable_default c m_info)
    list
  |> List.filter (fun (_, c, _) -> is_recursive_param name c m_info |> not)

let get_setter_list summary s_lst =
  List.fold_left
    (fun lst (s, fields) -> (s, fields, get_first_summary s summary) :: lst)
    [] s_lst
  |> List.rev |> prune_dup_summary_setter

let is_new_loc_field field summary =
  let is_null symbol =
    match Value.M.find_opt symbol summary.value with
    | Some x when x.Value.value = Eq Null -> true
    | _ -> false
  in
  let is_new_loc x =
    match x with
    | Condition.RH_Symbol _
      when is_null (get_rh_name x) |> not
           && contains_symbol x (snd summary.precond) |> not ->
        true
    | _ -> false
  in
  let is_new_loc_mem m =
    Condition.M.fold
      (fun _ x check -> if check || is_new_loc x then true else check)
      m false
  in
  let post_var, post_mem = summary.postcond in
  let field_var = get_id_symbol post_var field in
  match Condition.M.find_opt field_var post_mem with
  | None -> false
  | Some m -> is_new_loc_mem m

let ret_fld_name_of summary =
  let get_field field symbol mem acc =
    match field with
    | Condition.RH_Var v -> (v, get_tail_symbol "" symbol mem) :: acc
    | _ -> acc
  in
  let collect_field mem full_mem =
    Condition.M.fold
      (fun field symbol acc_lst -> get_field field symbol full_mem acc_lst)
      mem []
  in
  let pre_var, pre_mem = summary.precond in
  let this_var = get_id_symbol pre_var "this" in
  let candidate_fields =
    match Condition.M.find_opt (get_next_symbol this_var pre_mem) pre_mem with
    | Some m -> collect_field m pre_mem
    | _ -> []
  in
  let post_var, post_mem = summary.postcond in
  let return_var = get_id_symbol post_var "return" in
  let return_tail_symbol = get_tail_symbol "" return_var post_mem in
  let field_name =
    List.fold_left
      (fun found (field, sym) ->
        if sym = return_tail_symbol then field else found)
      "" candidate_fields
  in
  field_name

let is_getter_with_memory_effect m_summary fld_name =
  (* If the field name is empty, it indicates that the method doesn't return its field,
     so it should not be pruned for safety *)
  let new_loc = is_new_loc_field "return" m_summary in
  (fld_name = "" && not new_loc) || new_loc

let is_ret_recv_mem_effect fld_name subtypes summary m_info ret_recv_methods =
  let check_ret_recv fld_name subtypes m_name effect_fld_lst =
    let info = MethodInfo.M.find m_name m_info in
    List.mem info.MethodInfo.return subtypes && List.mem fld_name effect_fld_lst
  in
  List.fold_left
    (fun check m_name ->
      check
      || check_ret_recv fld_name subtypes m_name (get_fields m_name summary))
    false ret_recv_methods

let is_set_recv_mem_effect fld_name summary m_info set_recv_methods =
  let check_set_recv fld_name m_name summaries =
    let get_fld_symbol { postcond = post_var, post_mem; _ } =
      get_field_symbol (mk_var fld_name)
        (get_id_symbol post_var "this")
        post_mem
    in
    List.fold_left
      (fun check smy ->
        check
        || List.mem (get_fld_symbol smy) (get_params_symbol m_name m_info smy)
           |> not)
      false summaries
  in
  List.fold_left
    (fun check (m_name, fld_set) ->
      check
      || FieldSet.mem { used_in_error = false; name = fld_name } fld_set
         && check_set_recv fld_name m_name (get_summaries m_name summary))
    false set_recv_methods

let satisfied_c m_summary id candidate_constructor summary =
  let c_summaries = get_summaries candidate_constructor summary in
  let target_symbol =
    get_target_symbol (if is_receiver id then "this" else id) m_summary
    |> get_rh_name
  in
  if target_symbol = "" then [ (true, List.hd c_summaries) ]
  else
    let meet lst c_summary =
      ( [
          ( find_relation target_symbol m_summary.relation,
            get_id_symbol (fst c_summary.postcond) "this" |> get_rh_name );
        ]
        |> check_intersect ~is_init:true m_summary c_summary,
        c_summary )
      :: lst
    in
    let sat lst (check_summary, c_summary) =
      if List.filter (fun (_, c) -> c = false) check_summary = [] then
        ( true,
          c_summary
          |> new_value_summary (combine_value c_summary.value check_summary) )
        :: lst
      else (false, c_summary) :: lst
    in
    List.fold_left meet [] c_summaries |> List.fold_left sat []

let check_satisfied_c id const_name t_summary init sat_lst =
  let get_new_summary smy =
    if Utils.is_array_init const_name then modify_array_summary id t_summary smy
    else modify_summary id t_summary smy
  in
  List.fold_left
    (fun pick (check, smy) ->
      if check then
        let new_summary = get_new_summary smy in
        (is_from_error true new_summary, const_name, new_summary)
      else if pick = (0, "", empty_summary) then (-3, const_name, empty_summary)
      else pick)
    init sat_lst

let satisfied_c_list id t_summary summary method_list =
  if !Cmdline.basic_mode then
    List.fold_left
      (fun list constructor -> (0, constructor, empty_summary) :: list)
      [] method_list
    |> List.rev
  else if !Cmdline.pruning_mode then
    List.fold_left
      (fun list constructor ->
        let c_summaries = get_summaries constructor summary in
        (0, constructor, List.hd c_summaries) :: list)
      [] method_list
    |> List.rev
  else
    List.fold_left
      (fun list constructor ->
        let lst = satisfied_c t_summary id constructor summary in
        let init = (0, "", empty_summary) in
        let pick = check_satisfied_c id constructor t_summary init lst in
        if pick = init then list else pick :: list)
      [] method_list
    |> List.rev

let append l1 l2 =
  let rec iter accu ll1 ll2 =
    match (ll1, ll2) with
    | h1 :: t1, h2 :: t2 -> iter (h2 :: h1 :: accu) t1 t2
    | [], ll2 -> List.rev_append accu ll2
    | ll1, [] -> List.rev_append accu ll1
  in
  iter [] l1 l2

let add_import import set =
  (if is_nested_class import then
     ImportSet.add (Str.replace_first (Str.regexp "\\$.*$") "" import) set
   else set)
  |> ImportSet.add import
