open Language

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

let rec find_relation given_symbol relation =
  match Relation.M.find_opt given_symbol relation with
  | Some find_symbol -> find_relation find_symbol relation
  | None -> given_symbol

let get_target_symbol id { precond = pre_var, pre_mem; _ } =
  let this_symbol = get_id_symbol pre_var "this" in
  let this_tail_symbol = get_tail_symbol "this" this_symbol pre_mem in
  match Condition.M.find_opt this_tail_symbol pre_mem with
  | None -> this_symbol
  | Some mem -> (
      let if_field_symbol = Condition.M.find_opt (mk_var id) mem in
      match if_field_symbol with
      | Some field_symbol -> field_symbol
      | None -> get_id_symbol pre_var id)

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
  let exist_head_symbol =
    Condition.M.fold
      (fun head_cand _ cand ->
        match head_cand with Condition.RH_Symbol s -> s | _ -> cand)
      exist_head_symbol ""
  in
  if exist_head_symbol = "" then head_symbol
  else find_real_head exist_head_symbol memory

(* (symbol, value, head)
   value is set only when the symbol is RH_Index *)
let get_head_symbol symbol mem =
  Condition.M.fold
    (fun hd_symbol trace hd_list ->
      let hd = find_real_head (get_rh_name hd_symbol) mem in
      Condition.M.fold
        (fun trace_hd trace_tl hd_list ->
          match trace_tl with
          | Condition.RH_Symbol s when symbol = s -> [ (symbol, None, hd) ]
          | _ -> (
              match trace_hd with
              | Condition.RH_Index i when symbol = i ->
                  ( symbol,
                    get_next_symbol trace_tl mem |> get_rh_name |> mk_some,
                    hd )
                  :: hd_list
              | _ -> hd_list))
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

let get_param_index head_symbol variables formal_params =
  let variable = find_variable head_symbol variables in
  let index =
    let rec get_index count params =
      match params with
      | hd :: tl -> (
          match hd with
          | This _ -> get_index (count + 1) tl
          | Var (_, id) when id = variable -> count
          | _ -> get_index (count + 1) tl)
      | [] -> -1
    in
    get_index 0 formal_params
  in
  index

(* variables: Condition.var *)
(* return: (callee_actual_symbol * head_symbol * param_index) list *)
(* if param_index = -1 then this symbol can be any value *)
let get_param_index_list head_symbol_list (variables, _) formal_params =
  List.fold_left
    (fun lst (symbol, idx_value, head_symbol) ->
      if head_symbol = "" then (symbol, head_symbol, -1) :: lst
      else
        match idx_value with
        | None ->
            let index = get_param_index head_symbol variables formal_params in
            (symbol, head_symbol, index) :: lst
        | _ -> (symbol, head_symbol, -1) :: lst)
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
        UseFieldMap.M.add
          (find_real_head (List.nth to_s.args idx) (snd to_s.precond)
          |> mk_symbol)
          field_set new_ufset)
    from_s.use_field UseFieldMap.M.empty

let get_field_symbol id symbol mem =
  get_tail_symbol (get_rh_name ~is_var:true id) symbol mem

let get_value_symbol key sym c t_mem c_mem =
  let c_sym =
    match Condition.M.find_opt key c with
    | Some s -> s
    | None -> (
        match Condition.M.find_opt Condition.RH_Any c with
        | Some s -> s
        | None -> Condition.RH_Any (* fail to match *))
  in
  let field_name = get_rh_name ~is_var:true key in
  let tail_t_symbol = get_tail_symbol field_name sym t_mem |> get_rh_name in
  let tail_c_symbol = get_tail_symbol field_name c_sym c_mem |> get_rh_name in
  (tail_t_symbol, tail_c_symbol)

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
      | Some t_id, Some c_id -> (
          let t_symbol = get_field_symbol t_id (mk_symbol t_symbol) t_mem in
          let c_symbol = get_field_symbol c_id (mk_symbol c_symbol) c_mem in
          let c_t_mem = Condition.M.find_opt t_symbol t_mem in
          let c_c_mem = Condition.M.find_opt c_symbol c_mem in
          match (c_t_mem, c_c_mem) with
          | None, _ -> []
          | _, None -> []
          | Some t, Some c ->
              Condition.M.fold
                (fun key sym sym_list ->
                  get_value_symbol key sym c t_mem c_mem :: sym_list)
                t [])
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
  let iter_callee r mem =
    List.fold_left
      (fun mem (s, v, head) ->
        match v with
        | Some value -> (
            match Condition.M.find_opt (mk_symbol r) mem with
            | Some m when find_real_head r pre_mem = head ->
                combine r s value m mem
            | None when find_real_head r pre_mem = head ->
                combine r s value Condition.M.empty mem
            | _ -> mem)
        | _ -> mem)
      mem callee_sym_list
  in
  List.fold_left (fun mem (r, _) -> iter_callee r mem) pre_mem value_sym_list

let combine_value base_value vc_list =
  List.fold_left
    (fun prop_values (prop_value, _) ->
      Value.M.merge
        (fun _ v1 v2 ->
          match (v1, v2) with
          | None, None -> None
          | Some _, _ -> v1
          | None, Some _ -> v2)
        prop_values prop_value)
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

let is_receiver id = if id = "con_recv" || id = "con_outer" then true else false

let is_nested_class name = String.contains name '$'

let is_public_class class_name c_info =
  match ClassInfo.M.find_opt class_name c_info with
  | Some typ -> (
      match typ.ClassInfo.class_type with
      | Public | Public_Static | Public_Static_Abstract | Public_Abstract ->
          true
      | _ -> false)
  | None -> true (* modeling class *)

let is_abstract_class class_name (c_info, _) =
  match ClassInfo.M.find_opt class_name c_info with
  | Some typ -> (
      match typ.ClassInfo.class_type with
      | Public_Abstract | Public_Static_Abstract | Private_Abstract
      | Private_Static_Abstract | Default_Abstract | Default_Static_Abstract ->
          true
      | _ -> false)
  | _ -> false

let is_usable_default_class class_name c_info =
  if !Cmdline.extension = "" then false
  else
    match ClassInfo.M.find_opt class_name c_info with
    | Some typ -> (
        match typ.ClassInfo.class_type with
        | Default | Default_Static | Default_Static_Abstract | Default_Abstract
          ->
            if !Cmdline.extension = Utils.get_package_name class_name then true
            else false
        | _ -> false)
    | None -> false

let is_abstract_method method_name class_name_list m_info c_info =
  let target_class = Utils.get_class_name method_name in
  let m_name =
    Regexp.first_rm
      ("^" ^ Str.global_replace Regexp.dot "\\." target_class |> Str.regexp)
      method_name
  in
  if is_abstract_class target_class c_info |> not then false
  else
    List.fold_left
      (fun check class_name ->
        if class_name = target_class then check
        else if MethodInfo.M.mem (class_name ^ m_name) m_info then true
        else check)
      false class_name_list

let is_static_class name (c_info, _) =
  let name =
    Regexp.global_rm (Str.regexp "\\.<.*>(.*)$") name
    |> Regexp.global_rm (Str.regexp "(.*)$")
  in
  match ClassInfo.M.find_opt name c_info with
  | Some typ -> (
      match typ.ClassInfo.class_type with
      | Public_Static | Public_Static_Abstract -> true
      | (Default_Static | Default_Static_Abstract)
        when !Cmdline.extension <> ""
             && !Cmdline.extension = Utils.get_package_name name ->
          true
      | _ -> false)
  | None -> false

let is_private_class class_package c_info =
  match ClassInfo.M.find_opt class_package (fst c_info) with
  | Some info -> (
      let class_type = info.ClassInfo.class_type in
      match class_type with
      | Private | Private_Static | Private_Abstract | Private_Static_Abstract ->
          true
      | _ -> false)
  | None -> false

let is_static_method m_name m_info =
  match MethodInfo.M.find_opt m_name m_info with
  | None -> false
  | Some m -> m.MethodInfo.is_static

let is_private m_name m_info =
  match MethodInfo.M.find_opt m_name m_info with
  | None -> false
  | Some m -> ( match m.MethodInfo.modifier with Private -> true | _ -> false)

let is_public m_name m_info =
  match MethodInfo.M.find_opt m_name m_info with
  | None -> false
  | Some info -> (
      let is_test_file file_name =
        (* If this method is a method in the test file,
           don't use it even if the modifier is public *)
        Str.string_match (Str.regexp ".*/test/.*") file_name 0
      in
      match info.MethodInfo.modifier with
      | Public when is_test_file info.MethodInfo.filename |> not -> true
      | _ -> false)

let is_usable_default m_name m_info =
  if !Cmdline.extension = "" then false
  else
    match MethodInfo.M.find_opt m_name m_info with
    | None -> false
    | Some info -> (
        let is_test_file file_name =
          (* If this method is a method in the test file,
             don't use it even if the modifier is public or usable default *)
          Str.string_match (Str.regexp ".*/test/.*") file_name 0
        in
        match info.MethodInfo.modifier with
        | Default | Protected ->
            if
              !Cmdline.extension
              = (Utils.get_class_name m_name |> Utils.get_package_name)
              && is_test_file info.MethodInfo.filename |> not
            then true
            else false
        | _ -> false)

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

let is_same_param_type c1 c2 m_info =
  let c1_info = MethodInfo.M.find c1 m_info in
  let c2_info = MethodInfo.M.find c2 m_info in
  let rec check_param p1 p2 =
    match (p1, p2) with
    | v1 :: tl1, v2 :: tl2 -> (
        match (v1, v2) with
        | Var (typ1, _), Var (typ2, _) when typ1 = typ2 -> check_param tl1 tl2
        | This _, This _ -> check_param tl1 tl2
        | _, _ -> false)
    | _ :: _, [] -> false
    | [], _ :: _ -> false
    | [], [] -> true
  in
  check_param c1_info.MethodInfo.formal_params c2_info.MethodInfo.formal_params

let prune_dup_summary_setter lst =
  if !Cmdline.basic_mode || !Cmdline.priority_mode then List.rev lst
  else
    let rec collect_dup lst =
      match lst with
      | (_, _, h) :: t ->
          List.filter (fun (_, _, x) -> is_same_summary h x) t
          |> List.rev_append (collect_dup t)
      | _ -> []
    in
    List.fold_left
      (fun l s -> if collect_dup lst |> List.mem s then l else s :: l)
      [] lst

let prune_dup_summary m_info lst =
  if !Cmdline.basic_mode || !Cmdline.priority_mode then List.rev lst
  else
    let rec collect_dup lst =
      match lst with
      | (_, ch, h) :: t ->
          List.filter
            (fun (_, cx, x) ->
              is_same_summary h x && is_same_param_type ch cx m_info)
            t
          |> List.rev_append (collect_dup t)
      | _ -> []
    in
    List.fold_left
      (fun l s -> if collect_dup lst |> List.mem s then l else s :: l)
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
