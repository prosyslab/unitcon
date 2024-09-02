open Language
module CG = Callgraph.G
module IG = Inheritance.G
module ImportSet = Utils.ImportSet

exception Not_found_setter

exception Not_found_get_object

module TypeSet = Set.Make (struct
  type t = string [@@deriving compare]
end)

module VarSet = Set.Make (struct
  type t = variable [@@deriving compare]
end)

(* Set of VarSet *)
module VarSets = Set.Make (VarSet)

module VarListSet = Set.Make (struct
  type t = AST.var list

  let compare = compare
end)

module ErrorEntrySet = Set.Make (struct
  type t = string * summary

  let compare = compare
end)

module ExploredMethod = Set.Make (struct
  type t = string [@@deriving compare]
end)

module StmtMap = struct
  module M = Map.Make (struct
    type t = AST.t

    let compare = compare
  end)

  type t = AST.t list M.t
end

type partial_tc = {
  unroll : int;
  nt_cost : int;
  t_cost : int;
  prec : int; (* number of precise statement *)
  tc : AST.t;
  loop_ids : AST.LoopIdMap.t;
}

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

(* non-terminal cost for p, terminal cost for p, precision for p *)
let get_cost p =
  if p.unroll > 1 then (p.nt_cost, p.t_cost, p.prec) else (0, 0, 0)

let mk_cost prev_p curr_tc curr_loop_id prec =
  {
    unroll = prev_p.unroll + 1;
    nt_cost = AST.count_nt curr_tc;
    t_cost = AST.count_t curr_tc;
    prec;
    tc = curr_tc;
    loop_ids = curr_loop_id;
  }

let empty_id_map = AST.LoopIdMap.M.empty

let empty_p =
  {
    unroll = 0;
    nt_cost = 0;
    t_cost = 0;
    prec = 0;
    tc = AST.Skip;
    loop_ids = empty_id_map;
  }

let mk_some x = Some x

let mk_var x = Condition.RH_Var x

let mk_symbol x = Condition.RH_Symbol x

let mk_index x = Condition.RH_Index x

let rec find_relation given_symbol relation =
  match Relation.M.find_opt given_symbol relation with
  | Some find_symbol -> find_relation find_symbol relation
  | None -> given_symbol

let get_target_symbol id { precond = pre_var, pre_mem; _ } =
  let this_symbol = AST.get_id_symbol pre_var "this" in
  let this_tail_symbol = AST.get_tail_symbol "this" this_symbol pre_mem in
  match Condition.M.find_opt this_tail_symbol pre_mem with
  | None -> this_symbol
  | Some mem -> (
      let if_field_symbol = Condition.M.find_opt (mk_var id) mem in
      match if_field_symbol with
      | Some field_symbol -> field_symbol
      | None -> AST.get_id_symbol pre_var id)

let find_variable head_symbol variables =
  match Condition.M.find_opt (mk_symbol head_symbol) variables with
  | Some var -> AST.get_rh_name ~is_var:true var
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
      let hd = find_real_head (AST.get_rh_name hd_symbol) mem in
      Condition.M.fold
        (fun trace_hd trace_tl hd_list ->
          match trace_tl with
          | Condition.RH_Symbol s when symbol = s -> [ (symbol, None, hd) ]
          | _ -> (
              match trace_hd with
              | Condition.RH_Index i when symbol = i ->
                  ( symbol,
                    AST.get_next_symbol trace_tl mem
                    |> AST.get_rh_name |> mk_some,
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
      let idx =
        get_param_index (AST.get_rh_name sym) (fst from_s.precond) params
      in
      if idx = -1 then new_ufset
      else
        UseFieldMap.M.add
          (find_real_head (List.nth to_s.args idx) (snd to_s.precond)
          |> mk_symbol)
          field_set new_ufset)
    from_s.use_field UseFieldMap.M.empty

let get_field_symbol id symbol mem =
  AST.get_tail_symbol (AST.get_rh_name ~is_var:true id) symbol mem

let get_value_symbol key sym c t_mem c_mem =
  let c_sym =
    match Condition.M.find_opt key c with
    | Some s -> s
    | None -> (
        match Condition.M.find_opt Condition.RH_Any c with
        | Some s -> s
        | None -> Condition.RH_Any (* fail to match *))
  in
  let field_name = AST.get_rh_name ~is_var:true key in
  let tail_t_symbol =
    AST.get_tail_symbol field_name sym t_mem |> AST.get_rh_name
  in
  let tail_c_symbol =
    AST.get_tail_symbol field_name c_sym c_mem |> AST.get_rh_name
  in
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

let get_type v = match v with This typ -> typ | Var (typ, _) -> typ

let is_string x =
  match AST.get_vinfo x |> fst with String -> true | _ -> false

let is_primitive x =
  match AST.get_vinfo x |> fst with
  | Int | Long | Short | Byte | Float | Double | Bool | Char | String -> true
  | _ -> false

let is_primitive_from_v v =
  match get_type (fst v.AST.variable) with
  | Int | Long | Short | Byte | Float | Double | Bool | Char | String -> true
  | _ -> false

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
      ("^" ^ Str.global_replace (Str.regexp ".") "\\." target_class
      |> Str.regexp)
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

let prune_dup_summary lst =
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

let get_m_lst x0 m_info (c_info, ig) =
  let class_name = AST.get_vinfo x0 |> fst |> get_class_name in
  let class_to_find =
    try IG.succ ig class_name |> List.cons class_name
    with Invalid_argument _ -> [ class_name ]
  in
  MethodInfo.M.fold
    (fun m_name _ method_list ->
      List.fold_left
        (fun (c_lst, ret_c_lst) class_name_to_find ->
          if
            (is_public_class (Utils.get_class_name m_name) c_info
            || is_usable_default_class (Utils.get_class_name m_name) c_info)
            && is_available_method m_name m_info
          then
            if
              is_abstract_class class_name_to_find (c_info, ig) |> not
              && match_constructor_name class_name_to_find m_name
            then (m_name :: c_lst, ret_c_lst)
            else if
              match_return_object class_name_to_find m_name m_info
              && is_abstract_method m_name class_to_find m_info (c_info, ig)
                 |> not
              && Utils.is_init_method m_name |> not
            then (c_lst, m_name :: ret_c_lst)
            else (c_lst, ret_c_lst)
          else (c_lst, ret_c_lst))
        method_list class_to_find)
    m_info ([], [])

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

let is_new_loc_field field summary =
  let is_null symbol =
    match Value.M.find_opt symbol summary.value with
    | Some x when x.Value.value = Eq Null -> true
    | _ -> false
  in
  let is_new_loc x =
    match x with
    | Condition.RH_Symbol _
      when is_null (AST.get_rh_name x) |> not
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
  let field_var = AST.get_id_symbol post_var field in
  match Condition.M.find_opt field_var post_mem with
  | None -> false
  | Some m -> is_new_loc_mem m

let ret_fld_name_of summary =
  let collect_field mem full_mem =
    Condition.M.fold
      (fun field symbol acc_lst ->
        match field with
        | Condition.RH_Var v ->
            (v, AST.get_tail_symbol "" symbol full_mem) :: acc_lst
        | _ -> acc_lst)
      mem []
  in
  let pre_var, pre_mem = summary.precond in
  let this_var = AST.get_id_symbol pre_var "this" in
  let candidate_fields =
    match
      Condition.M.find_opt (AST.get_next_symbol this_var pre_mem) pre_mem
    with
    | Some m -> collect_field m pre_mem
    | _ -> []
  in
  let post_var, post_mem = summary.postcond in
  let return_var = AST.get_id_symbol post_var "return" in
  let return_tail_symbol = AST.get_tail_symbol "" return_var post_mem in
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

let collect_recv m_info (ret_type, m_type) c_info s_map subtypes =
  let is_available_class typ c_info =
    match ClassInfo.M.find_opt typ c_info with
    | Some t -> (
        match t.ClassInfo.class_type with
        | Public | Public_Static -> true
        | _ -> false)
    | _ -> true
  in
  (* cond_r is same as cond_common *)
  let cond_common typ m_name =
    is_available_method m_name m_info && is_available_class typ (fst c_info)
  in
  let cond_c typ m_name =
    cond_common typ m_name && match_constructor_name typ m_name
  in
  let cond_s typ (m_name, field_set) =
    cond_common typ m_name && FieldSet.is_empty field_set |> not
  in
  let get_r_list typ =
    (try ReturnType.M.find typ ret_type with _ -> [])
    |> List.fold_left
         (fun lst x -> if cond_common typ x then x :: lst else lst)
         []
  in
  let get_c_list typ =
    (try MethodType.M.find typ m_type with _ -> [])
    |> List.fold_left (fun lst x -> if cond_c typ x then x :: lst else lst) []
  in
  let get_s_list typ =
    (try SetterMap.M.find typ s_map with _ -> [])
    |> List.fold_left
         (fun lst setter -> if cond_s typ setter then setter :: lst else lst)
         []
  in
  TypeSet.fold
    (fun typ (ret_list, set_list) ->
      ( List.rev_append (get_r_list typ) (get_c_list typ)
        |> List.rev_append ret_list,
        List.rev_append (get_s_list typ) set_list ))
    subtypes ([], [])

let calc_z3 id z3exp =
  let solver = Z3.Solver.mk_solver z3ctx None in
  Z3.Solver.add solver z3exp;
  let _ = Z3.Solver.check solver [] in
  match Z3.Solver.get_model solver with
  | Some m -> (
      let value = Z3.Model.eval m id false in
      match value with
      | Some v ->
          if Z3.Arithmetic.is_real v then Z3.Arithmetic.Real.numeral_to_string v
          else Z3.Arithmetic.Integer.numeral_to_string v
      | None -> "")
  | None -> ""

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

let default_value_list typ import p_info =
  let predef = get_predef_value_list typ p_info in
  let extra = get_extra_value_list typ import p_info in
  let lst = List.rev_append predef extra in
  match typ with
  | Int | Long | Short | Byte ->
      let f acc x =
        match int_of_string_opt x with
        | Some i -> AST.Primitive (Z i) :: acc
        | _ -> acc
      in
      List.fold_left f [] lst
  | Float | Double ->
      let f acc x =
        match float_of_string_opt x with
        | Some i -> AST.Primitive (R i) :: acc
        | _ -> acc
      in
      List.fold_left f [] lst
  | Bool ->
      let f acc x =
        match bool_of_string_opt x with
        | Some i -> AST.Primitive (B i) :: acc
        | _ -> acc
      in
      List.fold_left f [] lst
  | Char ->
      let f acc x =
        if String.length x = 1 then AST.Primitive (C x.[0]) :: acc else acc
      in
      List.fold_left f [] lst
  | String ->
      (* String constant is already expanded when finding error entries *)
      let f acc x =
        if List.mem (AST.Primitive (S x)) acc then acc
        else if x = "NULL" then AST.Null :: acc
        else AST.Primitive (S x) :: acc
      in
      List.fold_left f [] predef
  | _ ->
      let f acc x = if x = "NULL" then AST.Null :: acc else acc in
      List.fold_left f [] lst

let not_found_value v =
  match v.Value.value with Value.Eq NonValue -> true | _ -> false

let calc_value_list from_error org_list default =
  (* default value have a penalty *)
  let prec = if from_error then -2 else 0 in
  List.fold_left (fun lst x -> (prec, x) :: lst) org_list default

let filter_size id lst =
  if id = "size" || id = "index" || id = "capacity" then
    List.filter
      (fun x -> match snd x with AST.Primitive (Z x) -> x >= 0 | _ -> false)
      lst
  else lst

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

let calc_value id value default =
  let prec = if value.Value.from_error then 2 else 0 in
  let calc_int result =
    match int_of_string_opt result with
    | Some i ->
        calc_value_list value.Value.from_error
          [ (prec, AST.Primitive (Z i)) ]
          default
        |> filter_size id
    | _ -> calc_value_list false [] default |> filter_size id
  in
  let calc_float result =
    match float_of_string_opt result with
    | Some f ->
        calc_value_list value.Value.from_error
          [ (prec, AST.Primitive (R f)) ]
          default
    | _ -> calc_value_list false [] default
  in
  match value.Value.value with
  | Eq v -> (
      match v with
      | Int _ | Long _ | Short _ | Byte _ ->
          let result = get_z3_result value.Value.value id in
          calc_int result
      | Float _ | Double _ ->
          let result = get_z3_result value.Value.value id in
          calc_float result
      | Bool b ->
          calc_value_list value.Value.from_error
            [ (prec, AST.Primitive (B b)) ]
            default
      | Char c ->
          calc_value_list value.Value.from_error
            [ (prec, AST.Primitive (C c)) ]
            default
      | String s ->
          calc_value_list value.Value.from_error
            [ (prec, AST.Primitive (S s)) ]
            default
      | Null -> [ (prec, AST.Null) ]
      | _ -> failwith "not implemented eq")
  | Neq v -> (
      match v with
      | Int _ | Long _ | Short _ | Byte _ ->
          let result = get_z3_result value.Value.value id in
          calc_int result
      | Float _ | Double _ ->
          let result = get_z3_result value.Value.value id in
          calc_float result
      | Bool b ->
          calc_value_list value.Value.from_error
            [ (prec, AST.Primitive (B (not b))) ]
            default
      | String s ->
          calc_value_list value.Value.from_error
            [ (prec, AST.Primitive (S ("not_" ^ s))) ]
            default
      | Null ->
          (* Among the const, only the string can be defined as null *)
          List.fold_left
            (fun lst x ->
              if x = AST.Null then (-prec, x) :: lst else (prec, x) :: lst)
            [] default
      | _ -> failwith "not implemented neq")
  | Le v -> (
      match v with
      | Int _ | Long _ | Short _ | Byte _ ->
          let result = get_z3_result value.Value.value id in
          calc_int result
      | Float _ | Double _ ->
          let result = get_z3_result value.Value.value id in
          calc_float result
      | _ -> failwith "not implemented le")
  | Lt v -> (
      match v with
      | Int _ | Long _ | Short _ | Byte _ ->
          let result = get_z3_result value.Value.value id in
          calc_int result
      | Float _ | Double _ ->
          let result = get_z3_result value.Value.value id in
          calc_float result
      | _ -> failwith "not implemented lt")
  | Ge v -> (
      match v with
      | Int _ | Long _ | Short _ | Byte _ ->
          let result = get_z3_result value.Value.value id in
          calc_int result
      | Float _ | Double _ ->
          let result = get_z3_result value.Value.value id in
          calc_float result
      | _ -> failwith "not implemented ge")
  | Gt v -> (
      match v with
      | Int _ | Long _ | Short _ | Byte _ ->
          let result = get_z3_result value.Value.value id in
          calc_int result
      | Float _ | Double _ ->
          let result = get_z3_result value.Value.value id in
          calc_float result
      | _ -> failwith "not implemented gt")
  | Between (v1, v2) -> (
      match (v1, v2) with
      | Int _, _ | Long _, _ ->
          let result = get_z3_result value.Value.value id in
          calc_int result
      | Float _, _ | Double _, _ ->
          let result = get_z3_result value.Value.value id in
          calc_float result
      | MinusInf, PlusInf -> calc_value_list value.Value.from_error [] default
      | _ -> failwith "not implemented between")
  | Outside (v1, v2) -> (
      match (v1, v2) with
      | Int _, _ | Long _, _ ->
          let result = get_z3_result value.Value.value id in
          calc_int result
      | Float _, _ | Double _, _ ->
          let result = get_z3_result value.Value.value id in
          calc_float result
      | _ -> failwith "not implemented outside")

let find_value_from_variable memory value target_variable =
  let target_variable =
    Condition.M.fold
      (fun symbol symbol_trace find_variable ->
        let symbol = AST.get_rh_name symbol in
        if symbol = target_variable then
          Condition.M.fold
            (fun _ trace_tl trace_find_var ->
              match trace_tl with
              | Condition.RH_Symbol s -> s
              | _ -> trace_find_var)
            symbol_trace find_variable
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
  let this_sym default =
    match
      Condition.M.find_opt
        (AST.org_symbol "this" summary |> mk_symbol)
        (snd summary.precond)
    with
    | Some this_mem ->
        Condition.M.fold
          (fun field symbol find_variable ->
            match field with
            | Condition.RH_Var v when v = id -> AST.get_rh_name symbol
            | _ -> find_variable)
          this_mem default
    | _ -> default
  in
  this_sym "" |> find_value_from_variable (snd summary.precond) summary.value

let get_value v p_info =
  let typ, id = AST.get_vinfo v in
  let find_value1 = find_target_value id (AST.get_v v).summary in
  let find_value2 = find_target_value_from_this id (AST.get_v v).summary in
  let default =
    if !Cmdline.with_fuzz then [ AST.WithFuzz ]
    else default_value_list typ (AST.get_v v).import p_info
  in
  let found_value =
    if not_found_value find_value1 then
      if not_found_value find_value2 then
        let default_value =
          List.fold_left (fun lst x -> (0, x) :: lst) [] default
        in
        if typ = Int then filter_size id default_value else default_value
      else calc_value id find_value2 default
    else calc_value id find_value1 default
  in
  if !Cmdline.with_fuzz then
    let null_exists lst =
      List.fold_left
        (fun exist (_, value) -> if value = AST.Null then true else exist)
        false lst
    in
    if typ = String && not (null_exists found_value) then
      (* fuzzer can not generate a null value, so add a null value if needed *)
      (0, AST.Null) :: found_value
    else found_value
  else found_value

let get_array_size array summary =
  let _, memory = summary.precond in
  let array_symbol = AST.org_symbol array summary in
  match Condition.M.find_opt (mk_symbol array_symbol) memory with
  | Some x -> (true, Condition.M.fold (fun _ _ size -> size + 1) x 0)
  | None -> (false, 1)

let get_same_type_param params =
  let get_type p = match p with Var (t, _) -> t | _ -> NonType in
  let mk_new_set p =
    List.fold_left
      (fun set op_p ->
        if get_type p = get_type op_p && get_type p <> NonType then
          VarSet.add op_p set
        else set)
      (VarSet.add p VarSet.empty)
      params
  in
  List.fold_left
    (fun sets p -> VarSets.add (mk_new_set p) sets)
    VarSets.empty params

let get_same_precond_param summary param_sets =
  VarSets.fold
    (fun set sets ->
      let filter_singleton set =
        if VarSet.cardinal set < 2 then VarSet.empty else set
      in
      let get_p_value p s =
        match p with
        | Var (_, id) -> find_target_value id s
        | _ -> failwith "Fail: find the target value"
      in
      let new_set =
        VarSet.fold
          (fun p new_set ->
            let v = get_p_value p summary in
            VarSet.fold
              (fun op_p new_set ->
                if v = get_p_value op_p summary then VarSet.add op_p new_set
                else new_set)
              set (VarSet.add p new_set))
          set VarSet.empty
        |> filter_singleton
      in
      VarSets.add new_set sets)
    param_sets VarSets.empty
  |> VarSets.filter (fun x -> VarSet.is_empty x |> not)

let get_same_params_set summary params =
  let new_p = List.fold_left (fun p v -> v :: p) [] params |> List.rev in
  get_same_type_param new_p |> get_same_precond_param summary

let satisfied_c m_summary id candidate_constructor summary =
  let c_summaries, _ = SummaryMap.M.find candidate_constructor summary in
  let target_symbol =
    get_target_symbol (if is_receiver id then "this" else id) m_summary
    |> AST.get_rh_name
  in
  if target_symbol = "" then [ (true, List.hd c_summaries) ]
  else
    let meet lst c_summary =
      ( [
          ( find_relation target_symbol m_summary.relation,
            AST.get_id_symbol (fst c_summary.postcond) "this" |> AST.get_rh_name
          );
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

let find_class_file =
  List.fold_left
    (fun gvar_list const ->
      (0, AST.GlobalConstant (const ^ ".class")) :: gvar_list)
    []
    [ "UnitconInterface"; "UnitconEnum" ]

let find_enum_var_list c_name i_info =
  match InstanceInfo.M.find_opt c_name i_info with
  | None -> []
  | Some info ->
      List.fold_left
        (fun gvar_list const ->
          (0, AST.GlobalConstant (c_name ^ "." ^ const)) :: gvar_list)
        [] info

let all_global_var c_name s_trace =
  Condition.M.fold
    (fun head _ gvar_list ->
      match head with
      | Condition.RH_Var var ->
          (0, AST.GlobalConstant (AST.get_short_class_name c_name ^ "." ^ var))
          :: gvar_list
      | _ -> gvar_list)
    s_trace []

let compare_global_var c_name t_var s_trace =
  Condition.M.fold
    (fun head _ gvar ->
      match head with
      | Condition.RH_Var var when var = t_var ->
          AST.get_short_class_name c_name ^ "." ^ var |> mk_some
      | _ -> gvar)
    s_trace None

let find_global_var_list c_name t_var mem summary m_info =
  let get_compared_global_var v init_summary var_lst =
    let new_gvar gv =
      (is_from_error false (List.hd init_summary), AST.GlobalConstant gv)
    in
    (Condition.M.fold (fun _ s_trace list ->
         match compare_global_var c_name v s_trace with
         | Some gv -> new_gvar gv :: list
         | None -> list))
      mem var_lst
  in
  SummaryMap.M.fold
    (fun init_name (init_summary, _) list ->
      let _, init_mem = (List.hd init_summary).precond in
      if
        Str.string_match (c_name ^ "\\.<clinit>" |> Str.regexp) init_name 0
        && (is_public init_name m_info || is_usable_default init_name m_info)
      then
        match t_var with
        | Some v ->
            get_compared_global_var v init_summary list
            |> (Condition.M.fold (fun _ s_trace list ->
                    List.rev_append (all_global_var c_name s_trace) list))
                 init_mem
        | None ->
            (Condition.M.fold (fun _ s_trace list ->
                 List.rev_append (all_global_var c_name s_trace) list))
              init_mem list
      else list)
    summary []

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
      if AST.get_rh_name symbol = t_sym then
        find_target_var symbol_trace find_variable
      else find_variable)
    mem None

let global_var_list class_name t_summary summary m_info i_info =
  let vars, mem = t_summary.precond in
  let t_var =
    Condition.M.fold
      (fun symbol var find_var ->
        match var with
        | Condition.RH_Var var ->
            if Str.string_match (".*\\." ^ class_name |> Str.regexp) var 0 then
              AST.get_rh_name symbol |> mk_some
            else find_var
        | _ -> find_var)
      vars None
  in
  match t_var with
  | None ->
      if class_name = "java.lang.Class" then find_class_file
      else
        let gvlist = find_global_var_list class_name None mem summary m_info in
        if gvlist = [] then find_enum_var_list class_name i_info else gvlist
  | Some x ->
      find_global_var_list class_name (get_target_var x mem) mem summary m_info

let get_symbol_num symbol =
  match
    Regexp.first_rm Regexp.symbol (AST.get_rh_name symbol) |> int_of_string_opt
  with
  | Some i -> i
  | _ -> 0

let get_fresh_num prev_num = prev_num + 1

let n_forward n start start_map =
  let key_compare k1 k2 =
    match (k1, k2) with
    | Condition.RH_Symbol _, Condition.RH_Symbol _ ->
        get_symbol_num k1 < get_symbol_num k2
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
  let rec forwards count key_list =
    if count >= n then key_list
    else
      let keys =
        List.fold_left
          (fun lst (_, _, k) -> find_key k start_map |> List.rev_append lst)
          [] key_list
      in
      forwards (count + 1) keys
  in
  forwards 1 (find_key start start_map)

let check_new_value symbol vmap memory =
  let checker mem =
    Condition.M.fold
      (fun field value check ->
        match
          Value.M.find_opt
            (get_field_symbol field value memory |> AST.get_rh_name)
            vmap
        with
        | Some _ -> true
        | _ -> check)
      mem false
  in
  match Condition.M.find_opt symbol memory with
  | Some x -> checker x
  | _ -> false

let add_new_mmap f1 f2 org_key field map =
  match Condition.M.find_opt org_key map with
  | Some x ->
      Condition.M.add org_key
        (Condition.M.add (AST.get_rh_name ~is_var:true field |> mk_var) f1 x)
        map
      |> Condition.M.add f1 (Condition.M.add RH_Any f2 Condition.M.empty)
  | _ ->
      Condition.M.add org_key
        (Condition.M.add
           (AST.get_rh_name ~is_var:true field |> mk_var)
           f1 Condition.M.empty)
        map
      |> Condition.M.add f1 (Condition.M.add RH_Any f2 Condition.M.empty)

let mk_new_memory org_key t_key_lst t_summary new_mem =
  let func (sym, value, new_pre_mem, new_post_mem) (_, field, key) =
    let field_name = AST.get_rh_name ~is_var:true field in
    if field_name = "" then (sym, value, new_pre_mem, new_post_mem)
    else
      let fn1 = get_fresh_num 1 in
      let fn2 = get_fresh_num fn1 in
      let fv1 = string_of_int fn1 |> String.cat "u" |> mk_symbol in
      let fv2 = string_of_int fn2 |> String.cat "u" |> mk_symbol in
      let new_value =
        try
          Value.M.find
            (AST.get_tail_symbol "" key (snd t_summary.precond)
            |> AST.get_rh_name)
            t_summary.value
        with _ -> value
      in
      let new_pre_mem = add_new_mmap fv1 fv2 org_key field new_pre_mem in
      let new_post_mem = add_new_mmap fv1 fv2 org_key field new_post_mem in
      (fv2, new_value, new_pre_mem, new_post_mem)
  in
  List.fold_left func new_mem t_key_lst

let rec forward count var_symbol this_symbol t_summary c_summary new_memory =
  let t_key_list = n_forward count var_symbol (snd t_summary.precond) in
  let c_key_list = n_forward count this_symbol (snd c_summary.postcond) in
  if t_key_list = [] then new_memory
  else if List.length t_key_list = List.length c_key_list then
    forward (count + 1) var_symbol this_symbol t_summary c_summary new_memory
  else
    let c_org_key =
      if count = 1 then this_symbol
      else
        let c_org_key, _, _ =
          n_forward (count - 1) this_symbol (snd c_summary.postcond) |> List.hd
        in
        c_org_key
    in
    mk_new_memory c_org_key t_key_list t_summary new_memory

let modify_summary id t_summary c_summary =
  let id = if id = "con_recv" then "this" else id in
  let var_symbol = AST.org_symbol id t_summary |> mk_symbol in
  let this_symbol = AST.org_symbol "this" c_summary |> mk_symbol in
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
         else Value.M.add (AST.get_rh_name symbol) value c_summary.value);
      use_field = c_summary.use_field;
      precond = (fst c_summary.precond, pre_mem);
      postcond = (fst c_summary.postcond, post_mem);
      args = c_summary.args;
    }

let new_this_summary old_summary values =
  let this_symbol = AST.org_symbol "this" old_summary |> mk_symbol in
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
      (AST.org_symbol "size" a_summary)
      Value.{ from_error; value = Value.Ge (Int value) }
      a_summary.value
  in
  let rec mk_new_summary new_summary summary =
    let tmp = AST.get_array_index id summary in
    if fst tmp |> fst = "" then (new_summary, summary)
    else
      let new_mem = AST.remove_array_index id (fst tmp |> fst) summary in
      mk_new_summary
        (new_this_summary new_summary tmp)
        (new_mem_summary new_mem summary)
  in
  mk_new_summary (new_value_summary new_value a_summary) t_summary |> fst

let get_param v summary =
  let get_field id =
    AST.get_field_from_ufmap id (fst summary.precond) summary.use_field
  in
  let make_new_var id =
    AST.
      {
        import = get_package_from_v v;
        variable = (v, mk_some !new_var);
        field = get_field id;
        summary;
      }
  in
  match v with
  | Var (typ, _) when typ = NonType -> None
  | This _ ->
      incr new_var;
      make_new_var "this" |> mk_some
  | Var (_, id) ->
      incr new_var;
      make_new_var id |> mk_some

let get_org_params_list summary org_param =
  List.fold_left
    (fun params v ->
      match get_param v summary with Some p -> p :: params | _ -> params)
    [] org_param
  |> List.rev

let find_org_param org_params_list p =
  List.fold_left
    (fun param real_arg ->
      if p = fst real_arg.AST.variable then real_arg else param)
    AST.empty_var org_params_list

let mk_params_list summary params_set org_param =
  let find_same_param target =
    let t = fst target.AST.variable in
    VarSets.fold
      (fun set find ->
        let fst_p = VarSet.elements set |> List.hd in
        VarSet.fold (fun p f -> if t = p then fst_p else f) set find)
      params_set t
  in
  let org_params_list = get_org_params_list summary org_param in
  let rec mk_params org_params params_list =
    match org_params with
    | hd :: tl ->
        let same_param = find_same_param hd |> find_org_param org_params_list in
        (if params_list = [] then [ [ hd ] ]
         else if hd = same_param then
           (* not found the same parameter *)
           List.fold_left
             (fun acc list -> List.cons (hd :: list) acc)
             [] params_list
         else
           List.fold_left
             (fun acc list ->
               List.cons (same_param :: list) acc |> List.cons (hd :: list))
             [] params_list)
        |> mk_params tl
    | _ -> params_list
  in
  mk_params org_params_list []

let mk_arg ~is_s param s =
  let param = if is_s then param else List.tl param in
  let same_params_set = get_same_params_set s param in
  mk_params_list s same_params_set param
  |> List.fold_left
       (fun arg_set lst -> VarListSet.add (List.rev lst) arg_set)
       VarListSet.empty

let summary_filtering name m_info list =
  List.filter
    (fun (_, c, _) -> is_public c m_info || is_usable_default c m_info)
    list
  |> List.filter (fun (_, c, _) -> is_recursive_param name c m_info |> not)

let get_field_set ret s_map =
  let c_name = AST.get_vinfo ret |> fst |> get_class_name in
  let fields =
    List.fold_left
      (fun fm (_, fields) -> FieldSet.union fields fm)
      (AST.get_v ret).field
      (try SetterMap.M.find c_name s_map with _ -> [])
  in
  FieldSet.fold
    (fun x new_fields ->
      let dup = Field.{ used_in_error = false; name = x.name } in
      if x.used_in_error && FieldSet.mem dup new_fields then
        FieldSet.remove dup new_fields
      else new_fields)
    fields fields

let error_entry_func ee es m_info _ =
  let param = (MethodInfo.M.find ee m_info).MethodInfo.formal_params in
  let f_arg_list = mk_arg ~is_s:(is_static_method ee m_info) param es in
  let c_name = Utils.get_class_name ee in
  let f =
    AST.F { typ = c_name; method_name = ee; import = c_name; summary = es }
  in
  if VarListSet.is_empty f_arg_list then [ (0, f, []) ]
  else VarListSet.fold (fun f_arg acc -> (0, f, f_arg) :: acc) f_arg_list []

let get_setter_list summary s_lst =
  List.fold_left
    (fun lst (s, fields) ->
      let smy =
        try SummaryMap.M.find s summary |> fst |> List.hd
        with _ -> empty_summary
      in
      (s, fields, smy) :: lst)
    [] s_lst
  |> List.rev |> prune_dup_summary

let mk_void_func (var : AST.var) id class_name m_info s_lst =
  let get_arg_list s =
    mk_arg
      ~is_s:(is_static_method s m_info)
      (MethodInfo.M.find s m_info).MethodInfo.formal_params var.summary
  in
  let get_f s =
    let typ =
      if Utils.is_array class_name then
        AST.get_vinfo id |> fst |> get_array_class_name
      else class_name
    in
    AST.F { typ; method_name = s; import = var.import; summary = var.summary }
  in
  List.fold_left
    (fun lst (s, fields, _) ->
      let f_arg_list = get_arg_list s in
      let prec =
        if contains_used_in_error var.field fields || Utils.is_modeling_set s
        then 0
        else -2
      in
      let f = get_f s in
      if VarListSet.is_empty f_arg_list then (prec, f, []) :: lst
      else
        VarListSet.fold
          (fun f_arg acc -> (prec, f, f_arg) :: acc)
          f_arg_list lst)
    [] s_lst

(* id is receiver variable *)
let get_void_func id ?(ee = "") ?(es = empty_summary) summary m_info c_info
    s_map =
  if AST.is_id id then error_entry_func ee es m_info c_info
  else
    let var = AST.get_v id in
    let class_name = AST.get_vinfo id |> fst |> get_class_name in
    if class_name = "" || class_name = "String" then []
    else
      (try SetterMap.M.find class_name s_map with _ -> [])
      |> List.filter (fun (s, _) -> is_available_method s m_info)
      |> get_setter_list summary
      |> mk_void_func var id class_name m_info

let check_satisfied_c id const_name t_summary init sat_lst =
  (List.fold_left (fun pick (check, smy) ->
       if check then
         if Utils.is_array_init const_name then
           let new_summary = modify_array_summary id t_summary smy in
           (is_from_error true new_summary, const_name, new_summary)
         else
           let new_summary = modify_summary id t_summary smy in
           (is_from_error true new_summary, const_name, new_summary)
       else if pick = (0, "", empty_summary) then (-3, const_name, empty_summary)
       else pick))
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
        let c_summaries =
          try SummaryMap.M.find constructor summary |> fst
          with _ -> [ empty_summary ]
        in
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

let get_cfunc id constructor m_info =
  let cost, c, s = constructor in
  let t = Utils.get_class_name c in
  let t =
    if Utils.is_array t then AST.get_vinfo id |> fst |> get_array_class_name
    else t
  in
  let func = AST.F { typ = t; method_name = c; import = t; summary = s } in
  let arg_list =
    mk_arg
      ~is_s:(is_static_method c m_info)
      (MethodInfo.M.find c m_info).MethodInfo.formal_params s
  in
  if VarListSet.is_empty arg_list then [ (cost, (func, AST.Arg [])) ]
  else
    VarListSet.fold
      (fun arg cfuncs -> (cost, (func, AST.Arg arg)) :: cfuncs)
      arg_list []

let get_cfuncs id list m_info =
  List.fold_left
    (fun lst (cost, c, s) ->
      List.rev_append (get_cfunc id (cost, c, s) m_info) lst)
    [] list

let get_c ret c_lst summary m_info c_info =
  let class_name = AST.get_vinfo ret |> fst |> get_class_name in
  if class_name = "" then []
  else
    let id = AST.get_vinfo ret |> snd in
    let s_list =
      satisfied_c_list id (AST.get_v ret).summary summary c_lst
      |> List.filter (fun (_, c, _) ->
             is_abstract_class (c |> Utils.get_class_name) c_info |> not)
      |> summary_filtering class_name m_info
      |> prune_dup_summary
    in
    get_cfuncs ret s_list m_info

let is_ret_recv_mem_effect fld_name subtypes summary m_info ret_recv_methods =
  let check_ret_recv fld_name subtypes m_name effect_fld_lst =
    let info = MethodInfo.M.find m_name m_info in
    List.mem info.MethodInfo.return subtypes && List.mem fld_name effect_fld_lst
  in
  List.fold_left
    (fun check m_name ->
      check
      || check_ret_recv fld_name subtypes m_name
           (SummaryMap.M.find m_name summary |> snd))
    false ret_recv_methods

let get_params_symbol m_name m_info { precond = pre_var, pre_mem; _ } =
  let info = MethodInfo.M.find m_name m_info in
  List.fold_left
    (fun lst param ->
      match param with
      | This _ -> lst
      | Var (_, var) ->
          get_field_symbol (mk_var "") (AST.get_id_symbol pre_var var) pre_mem
          :: lst)
    [] info.MethodInfo.formal_params

let is_set_recv_mem_effect fld_name summary m_info set_recv_methods =
  let check_set_recv fld_name m_name summaries =
    let get_fld_symbol { postcond = post_var, post_mem; _ } =
      get_field_symbol (mk_var fld_name)
        (AST.get_id_symbol post_var "this")
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
         && check_set_recv fld_name m_name
              (SummaryMap.M.find m_name summary |> fst))
    false set_recv_methods

let get_recv_type c_info summary_lst =
  List.fold_left
    (fun need_typ_set (_, c, _) ->
      let recv_type = Utils.get_class_name c in
      let subtypes =
        try IG.succ (snd c_info) recv_type |> List.cons recv_type
        with Invalid_argument _ -> [ recv_type ]
      in
      TypeSet.union (TypeSet.of_list subtypes) need_typ_set)
    TypeSet.empty summary_lst

let memory_effect_filtering summary m_info type_info c_info s_map smy_lst =
  let smy_lst = List.rev smy_lst in
  if !Cmdline.basic_mode || !Cmdline.priority_mode then List.rev smy_lst
  else
    let recv_type = get_recv_type c_info smy_lst in
    let ret_recv_methods, set_recv_methods =
      collect_recv m_info type_info c_info s_map recv_type
    in
    List.fold_left
      (fun lst (i, c, c_smy) ->
        let fld_name = ret_fld_name_of c_smy in
        let recv_type = Utils.get_class_name c in
        let subtypes =
          if is_static_method c m_info then []
          else
            try IG.succ (snd c_info) recv_type |> List.cons recv_type
            with Invalid_argument _ -> [ recv_type ]
        in
        let check_getter = is_getter_with_memory_effect c_smy fld_name in
        if subtypes = [] && check_getter then (i, c, c_smy) :: lst
        else if
          check_getter
          || is_ret_recv_mem_effect fld_name subtypes summary m_info
               ret_recv_methods
          || is_set_recv_mem_effect fld_name summary m_info set_recv_methods
        then (i, c, c_smy) :: lst
        else lst)
      [] smy_lst

let get_ret_c ret ret_obj_lst summary m_info type_info c_info s_map =
  let class_name = AST.get_vinfo ret |> fst |> get_class_name in
  if class_name = "" then []
  else
    let id = AST.get_vinfo ret |> snd in
    let s_list =
      satisfied_c_list id (AST.get_v ret).summary summary ret_obj_lst
      |> summary_filtering class_name m_info
      |> prune_dup_summary
      |> memory_effect_filtering summary m_info type_info c_info s_map
    in
    get_cfuncs ret s_list m_info

let get_inner_func f arg =
  let fname =
    Str.split Regexp.dollar (AST.get_func f).method_name |> List.rev |> List.hd
  in
  let n_f =
    AST.F
      {
        typ = (AST.get_func f).typ;
        method_name = fname;
        import = (AST.get_func f).import;
        summary = (AST.get_func f).summary;
      }
  in
  (* outer class variable *)
  let recv = try AST.get_arg arg |> List.hd with _ -> AST.empty_var in
  let n_recv =
    let var =
      Object
        ((AST.get_func f).method_name
        |> Regexp.first_rm (Str.regexp ("\\$" ^ fname)))
    in
    AST.Variable
      {
        import = recv.import;
        variable = (Var (var, "con_outer"), mk_some !outer);
        field = FieldSet.empty;
        summary = recv.summary;
      }
  in
  (n_recv, n_f, AST.Arg (try AST.get_arg arg |> List.tl with _ -> []))

let cname_condition m_name m_info c_info =
  match MethodInfo.M.find_opt m_name m_info with
  | Some info ->
      info.MethodInfo.return <> ""
      && (is_static_method m_name m_info || is_static_class m_name c_info)
      || Utils.is_init_method m_name
  | _ -> Utils.is_init_method m_name

let get_cname f = AST.ClassName (AST.get_func f).AST.typ

let get_arg_seq (args : AST.id list) =
  let already_arg = ref [] in
  List.fold_left
    (fun s arg ->
      if List.mem arg !already_arg then s
      else (
        already_arg := arg :: !already_arg;
        let x =
          List.fold_left (fun lst x -> AST.mk_const_arg x arg :: lst) [] s
        in
        if is_primitive arg then x
        else
          List.rev_append
            (List.fold_left (fun lst x -> AST.mk_assign_arg x arg :: lst) [] s)
            x))
    [ AST.Skip ] args

let mk_arg_seq arg class_name =
  let modified_x x =
    if is_primitive_from_v x then AST.modify_import class_name x else x
  in
  get_arg_seq
    (List.fold_left
       (fun lst x -> AST.Variable (modified_x x) :: lst)
       [] (AST.get_arg arg))

let loop_id_merge old_ids new_ids =
  AST.LoopIdMap.M.merge
    (fun _ v1 v2 ->
      match (v1, v2) with
      | None, None -> None
      | Some _, _ -> v1
      | None, Some _ -> v2)
    old_ids new_ids

(* low priority --> ... --> high priority *)
let sort_const consts =
  List.stable_sort (fun (c1, _) (c2, _) -> compare c1 c2) consts

let const_unroll p summary m_info i_info p_info =
  let get_r3 x =
    List.fold_left
      (fun lst x1 ->
        match snd x1 with
        | AST.Primitive _ -> lst
        | _ -> (fst x1, AST.const_rule3 p, empty_id_map) :: lst)
      [] (get_value x p_info)
  in
  let get_r2 x =
    List.fold_left
      (fun lst x1 -> (fst x1, AST.const_rule2 p (snd x1), empty_id_map) :: lst)
      []
      (global_var_list
         (get_class_name (AST.get_vinfo x |> fst))
         (AST.get_v x).summary summary m_info i_info)
  in
  match p with
  | AST.Const (x, _) ->
      if is_primitive x then
        if !Cmdline.with_loop then
          let prec, exps =
            List.fold_left
              (fun (prec, lst) x1 ->
                let prec = if prec < fst x1 then fst x1 else prec in
                (prec, snd x1 :: lst))
              (min_int, [])
              (get_value x p_info |> sort_const)
          in
          [
            ( prec,
              AST.const_rule_loop p,
              AST.LoopIdMap.M.add x exps empty_id_map );
          ]
        else
          List.fold_left
            (fun lst x1 ->
              (fst x1, AST.const_rule1 p (snd x1), empty_id_map) :: lst)
            [] (get_value x p_info)
      else
        let r2 = get_r2 x in
        if is_receiver (AST.get_vinfo x |> snd) then r2
        else List.rev_append (get_r3 x) r2
  | _ -> failwith "Fail: const_unroll"

let fcall_in_assign_unroll p summary m_info type_info c_info s_map =
  match p with
  | AST.Assign (x0, _, _, _) ->
      let field_set = get_field_set x0 s_map in
      let c_lst, ret_c_lst = get_m_lst x0 m_info c_info in
      if c_lst = [] && ret_c_lst = [] then raise Not_found_get_object
      else
        List.rev_append
          (get_c x0 c_lst summary m_info c_info)
          (get_ret_c x0 ret_c_lst summary m_info type_info c_info s_map)
        |> List.fold_left
             (fun lst (prec, (f, arg)) ->
               (prec, AST.fcall_in_assign_rule p field_set f arg, empty_id_map)
               :: lst)
             []
  | _ -> failwith "Fail: fcall_in_assign_unroll"

let recv_in_assign_unroll (prec, p, loop_ids) m_info c_info =
  match p with
  | AST.Assign (_, _, f, arg) when AST.recv_in_assign p ->
      if
        is_nested_class (AST.get_func f).import
        && is_static_class (AST.get_func f).import c_info |> not
        && Utils.is_init_method (AST.get_func f).method_name
      then (
        let recv, f, arg = get_inner_func f arg in
        if (AST.get_v recv).import = "" then
          (* The import of the inner class function being empty means
             that the receiver is an empty variable *)
          []
        else
          let r2 = AST.recv_in_assign_rule2_1 p recv f arg in
          let r3 = AST.recv_in_assign_rule3_1 p recv f arg in
          incr outer;
          (prec, r2, loop_ids) :: [ (prec, r3, loop_ids) ])
      else if cname_condition (AST.get_func f).method_name m_info c_info then
        [ (prec, get_cname f |> AST.recv_in_assign_rule1 p, loop_ids) ]
      else
        let r2 = AST.recv_in_assign_rule2 p "con_recv" !recv in
        let r3 = AST.recv_in_assign_rule3 p "con_recv" !recv in
        incr recv;
        (prec, r2, loop_ids) :: [ (prec, r3, loop_ids) ]
  | _ -> failwith "Fail: recv_in_assign_unroll"

let rec arg_in_assign_unroll (prec, p, loop_ids) =
  match p with
  | AST.Assign (_, _, f, arg) when AST.arg_in_assign p ->
      let class_name = Utils.get_class_name (AST.get_func f).method_name in
      mk_arg_seq arg class_name
      |> List.fold_left
           (fun lst x ->
             ( prec,
               AST.arg_in_assign_rule p x (AST.Param (AST.get_arg arg)),
               loop_ids )
             :: lst)
           []
  | Seq (s1, s2) when AST.arg_in_assign s2 ->
      arg_in_assign_unroll (prec, s2, loop_ids)
      |> List.fold_left
           (fun lst (p', s', loop') ->
             (p', AST.Seq (s1, s'), loop_id_merge loop_ids loop') :: lst)
           []
  | _ -> failwith "Fail: arg_in_assign_unroll"

let void_unroll p =
  (0, AST.void_rule1 p, empty_id_map)
  :: List.fold_left
       (fun lst x -> (0, x, empty_id_map) :: lst)
       [] (AST.void_rule2 p)

let fcall_in_void_unroll p summary m_info c_info s_map =
  match p with
  | AST.Void (x, _, _) ->
      let lst = get_void_func x summary m_info c_info s_map in
      if lst = [] then raise Not_found_setter
      else
        List.fold_left
          (fun lst (prec, f, arg) ->
            (prec, AST.fcall_in_void_rule p f (AST.Arg arg), empty_id_map)
            :: lst)
          [] lst
  | _ -> failwith "Fail: fcall_in_void_unroll"

let recv_in_void_unroll (prec, p, loop_ids) m_info c_info =
  match p with
  | AST.Void (_, f, _) when AST.recv_in_void p ->
      if cname_condition (AST.get_func f).method_name m_info c_info then
        [ (prec, get_cname f |> AST.recv_in_void_rule1 p, loop_ids) ]
      else
        let r2 = AST.recv_in_void_rule2 p "con_recv" !recv in
        let r3 = AST.recv_in_void_rule3 p "con_recv" !recv in
        incr recv;
        (prec, r2, loop_ids) :: [ (prec, r3, loop_ids) ]
  | _ -> failwith "Fail: recv_in_void_unroll"

let rec arg_in_void_unroll (prec, p, loop_ids) =
  match p with
  | AST.Void (_, f, arg) when AST.arg_in_void p ->
      let class_name = Utils.get_class_name (AST.get_func f).method_name in
      mk_arg_seq arg class_name
      |> List.fold_left
           (fun lst x ->
             ( prec,
               AST.arg_in_void_rule p x (AST.Param (AST.get_arg arg)),
               loop_ids )
             :: lst)
           []
  | Seq (s1, s2) when AST.arg_in_void s2 ->
      arg_in_void_unroll (prec, s2, loop_ids)
      |> List.fold_left
           (fun lst (p', s', loop') -> (p', AST.Seq (s1, s'), loop') :: lst)
           []
  | _ -> failwith "Fail: arg_in_void_unroll"

let append l1 l2 =
  let rec iter accu ll1 ll2 =
    match (ll1, ll2) with
    | h1 :: t1, h2 :: t2 -> iter (h2 :: h1 :: accu) t1 t2
    | [], ll2 -> List.rev_append accu ll2
    | ll1, [] -> List.rev_append accu ll1
  in
  iter [] l1 l2

let one_unroll p summary m_info type_info c_info s_map i_info p_info =
  match p with
  | AST.Seq _ when AST.void p -> void_unroll p
  | Const _ when AST.const p -> const_unroll p summary m_info i_info p_info
  | Assign _ when AST.fcall_in_assign p -> (
      (* fcall_in_assign --> recv_in_assign --> arg_in_assign *)
      match fcall_in_assign_unroll p summary m_info type_info c_info s_map with
      | exception Not_found_get_object ->
          if !Cmdline.mock then [ (0, AST.mk_mock_statement p, empty_id_map) ]
          else raise Not_found_get_object
      | p_lst ->
          let lst =
            p_lst
            |> List.fold_left
                 (fun acc_lst x ->
                   recv_in_assign_unroll x m_info c_info |> append acc_lst)
                 []
            |> List.fold_left
                 (fun acc_lst x -> arg_in_assign_unroll x |> append acc_lst)
                 []
          in
          if
            !Cmdline.mock
            && List.filter
                 (fun (_, x, _) ->
                   AST.count_params x < 2 (* at least receiver *))
                 p_lst
               = []
          then (0, AST.mk_mock_statement p, empty_id_map) :: lst
          else lst)
  | Void _ when AST.fcall1_in_void p ->
      (* fcall1_in_void --> recv_in_void --> arg_in_void *)
      fcall_in_void_unroll p summary m_info c_info s_map
      |> List.fold_left
           (fun acc_lst x ->
             recv_in_void_unroll x m_info c_info |> append acc_lst)
           []
      |> List.fold_left
           (fun acc_lst x -> arg_in_void_unroll x |> append acc_lst)
           []
  | Void _ when AST.fcall2_in_void p ->
      (* fcall2_in_void --> arg_in_void *)
      fcall_in_void_unroll p summary m_info c_info s_map
      |> List.fold_left
           (fun acc_lst x -> arg_in_void_unroll x |> append acc_lst)
           []
  | Void _ when AST.recv_in_void p ->
      (* unroll error entry *)
      recv_in_void_unroll (0, p, empty_id_map) m_info c_info
      |> List.fold_left
           (fun acc_lst x -> arg_in_void_unroll x |> append acc_lst)
           []
  | _ -> failwith "Fail: one_unroll"

let rec all_unroll ?(assign_ground = false) p summary m_info type_info c_info
    s_map i_info p_info stmt_map =
  match p with
  | _ when AST.ground p -> stmt_map
  | _ when assign_ground ->
      all_unroll_void p summary m_info type_info c_info s_map i_info p_info
        stmt_map
  | AST.Seq (s1, s2) when s2 = AST.Stmt ->
      all_unroll ~assign_ground s1 summary m_info type_info c_info s_map i_info
        p_info stmt_map
  | AST.Seq (s1, s2) ->
      all_unroll ~assign_ground s1 summary m_info type_info c_info s_map i_info
        p_info stmt_map
      |> all_unroll ~assign_ground s2 summary m_info type_info c_info s_map
           i_info p_info
  | _ ->
      StmtMap.M.add p
        (one_unroll p summary m_info type_info c_info s_map i_info p_info)
        stmt_map

and all_unroll_void p summary m_info type_info c_info s_map i_info p_info
    stmt_map =
  match p with
  | _ when AST.ground p -> stmt_map
  | AST.Seq _ when AST.void p ->
      StmtMap.M.add p
        (one_unroll p summary m_info type_info c_info s_map i_info p_info)
        stmt_map
  | Seq (s1, s2) -> (
      let new_void s1 (p', s', loop') =
        (p', AST.Seq (AST.modify_last_assign s1, s'), loop')
      in
      let new_void_list s1 s2 =
        one_unroll
          (AST.Seq (AST.last_code s1, s2))
          summary m_info type_info c_info s_map i_info p_info
        |> List.fold_left (fun lst void -> new_void s1 void :: lst) []
        |> List.rev
      in
      match AST.last_code s1 with
      | AST.Assign _ when AST.is_stmt s2 ->
          StmtMap.M.add p (new_void_list s1 s2) stmt_map
      | _ ->
          all_unroll_void s1 summary m_info type_info c_info s_map i_info p_info
            stmt_map
          |> all_unroll_void s2 summary m_info type_info c_info s_map i_info
               p_info)
  | _ -> failwith "Fail: all_unroll_void"

let rec change_stmt p s new_s =
  match p with
  | _ when p = s -> new_s
  | AST.Seq (s1, s2) when s1 = s -> AST.Seq (new_s, s2)
  | AST.Seq (s1, s2) when s2 = s -> AST.Seq (s1, new_s)
  | AST.Seq (s1, s2) -> AST.Seq (change_stmt s1 s new_s, change_stmt s2 s new_s)
  | _ -> p

let rec return_stmts p =
  match p with
  | _ when AST.ground p -> [] (* ground check of partial tc is first *)
  | AST.Seq (s1, s2) -> p :: List.rev_append (return_stmts s1) (return_stmts s2)
  | _ -> [ p ]

let sort_stmts map stmts =
  List.stable_sort
    (fun s1 s2 ->
      match (StmtMap.M.find_opt s1 map, StmtMap.M.find_opt s2 map) with
      | Some l1, Some l2 -> compare (List.length l1) (List.length l2)
      | Some _, None -> 1
      | None, Some _ -> -1
      | None, None -> 0)
    stmts

let combinate (prec, p, loop_ids) stmt_map =
  let combinate_stmt (p', s', loop_ids') s new_s_list =
    List.fold_left
      (fun lst (new_p, new_s, new_loop) ->
        (p' + new_p, change_stmt s' s new_s, loop_id_merge loop_ids' new_loop)
        :: lst)
      [] new_s_list
  in
  let combinate_stmts s new_s_lst partial_lst =
    List.fold_left
      (fun l _p -> combinate_stmt _p s new_s_lst |> append l)
      [] partial_lst
  in
  (* stmts is all fragments of statements in partial tc *)
  let all_combinate stmts =
    List.fold_left
      (fun lst s ->
        match StmtMap.M.find_opt s stmt_map with
        | Some new_s_list when new_s_list = [] ->
            (* Because these will be never grounded, remove all *)
            []
        | Some new_s_list -> combinate_stmts s new_s_list lst
        | _ -> lst)
      [ (prec, p, loop_ids) ]
      stmts
  in
  return_stmts p |> sort_stmts stmt_map |> all_combinate |> List.rev

(* find error entry *)
let rec find_ee e_method e_summary cg summary call_prop_map m_info c_info =
  let propagation caller_method caller_preconds call_prop =
    let new_value, new_mem, check_match =
      try satisfy e_method e_summary call_prop m_info
      with _ ->
        Logger.info "Fail to find a satisfiable error entry method";
        (Value.M.empty, Condition.M.empty, false)
    in
    let new_uf = mk_new_uf e_method e_summary call_prop m_info in
    if !Cmdline.basic_mode then
      ErrorEntrySet.union caller_preconds
        (find_ee caller_method empty_summary cg summary call_prop_map m_info
           c_info)
    else if !Cmdline.pruning_mode then
      ErrorEntrySet.union caller_preconds
        (find_ee caller_method call_prop cg summary call_prop_map m_info c_info)
    else if check_match then
      let new_call_prop =
        new_value_summary new_value call_prop
        |> new_mem_summary new_mem |> new_uf_summary new_uf
      in
      ErrorEntrySet.union caller_preconds
        (find_ee caller_method new_call_prop cg summary call_prop_map m_info
           c_info)
    else caller_preconds
  in
  if is_public e_method m_info || is_usable_default e_method m_info then
    ErrorEntrySet.add (e_method, e_summary) ErrorEntrySet.empty
  else
    let caller_list =
      try CG.succ cg e_method |> List.filter (fun x -> x <> e_method)
      with Invalid_argument _ -> []
    in
    List.fold_left
      (fun set caller_method ->
        (match
           CallPropMap.M.find_opt (caller_method, e_method) call_prop_map
         with
        | None ->
            (* It is possible without any specific conditions *)
            find_ee caller_method empty_summary cg summary call_prop_map m_info
              c_info
        | Some prop_list ->
            List.fold_left
              (fun caller_preconds call_prop ->
                if ExploredMethod.mem caller_method !explored_m then
                  (* if the caller method is included in the error entry set,
                       avoiding duplicate calculation *)
                  caller_preconds
                else (
                  explored_m := ExploredMethod.add caller_method !explored_m;
                  propagation caller_method caller_preconds call_prop))
              ErrorEntrySet.empty prop_list)
        |> ErrorEntrySet.union set)
      ErrorEntrySet.empty caller_list

let pretty_format p =
  let rec imports s set =
    let add_import import set =
      (if is_nested_class import then
         ImportSet.add (Str.replace_first (Str.regexp "\\$.*$") "" import) set
       else set)
      |> ImportSet.add import
    in
    match s with
    | AST.Seq (s1, s2) -> imports s1 set |> imports s2
    | Const (x, _) -> add_import (AST.get_v x).import set
    | Assign (x0, _, f, arg) ->
        List.fold_left
          (fun s (a : AST.var) -> add_import a.import s)
          set (AST.get_param arg)
        |> add_import (AST.get_v x0).import
        |> add_import (AST.get_func f).import
    | Void (_, f, arg) ->
        List.fold_left
          (fun s (a : AST.var) -> add_import a.import s)
          set (AST.get_param arg)
        |> add_import (AST.get_func f).import
    | _ -> set
  in
  (imports p ImportSet.empty, AST.code p)

let priority_q queue =
  List.stable_sort
    (fun p1 p2 ->
      let nt1, t1, prec1 = get_cost p1 in
      let nt2, t2, prec2 = get_cost p2 in
      if compare (nt1 + t1 - prec1) (nt2 + t2 - prec2) <> 0 then
        compare (nt1 + t1 - prec1) (nt2 + t2 - prec2)
      else if compare prec1 prec2 <> 0 then compare prec2 prec1
      else compare nt1 nt2)
    queue

let rec mk_testcase summary m_info type_info c_info s_map i_info p_info queue =
  let queue =
    if !Cmdline.basic_mode || !Cmdline.pruning_mode then queue
    else priority_q queue
  in
  match queue with
  | p :: tl ->
      if !Cmdline.with_fuzz && AST.ground p.tc && AST.with_withfuzz p.tc then
        [ (Need_Fuzzer, pretty_format p.tc, p.loop_ids, tl) ]
      else if !Cmdline.with_loop && AST.ground p.tc && AST.with_withloop p.tc
      then [ (Need_Loop, pretty_format p.tc, p.loop_ids, tl) ]
      else if AST.ground p.tc then
        [ (Complete, pretty_format p.tc, p.loop_ids, tl) ]
      else
        (match
           all_unroll ~assign_ground:(AST.assign_ground p.tc) p.tc summary
             m_info type_info c_info s_map i_info p_info StmtMap.M.empty
         with
        | exception Not_found_setter -> tl
        | exception Not_found_get_object -> tl
        | x ->
            combinate (p.prec, p.tc, p.loop_ids) x
            |> List.fold_left
                 (fun lst (new_p, new_s, new_loop) ->
                   mk_cost p new_s new_loop new_p :: lst)
                 []
            |> List.rev_append (List.rev tl))
        |> mk_testcase summary m_info type_info c_info s_map i_info p_info
  | [] -> []

let mk_testcases ~is_start queue (e_method, error_summary)
    ( cg,
      summary,
      call_prop_map,
      m_info,
      type_info,
      c_info,
      s_map,
      i_info,
      p_info ) =
  let apply_rule list =
    List.fold_left
      (fun lst (_, f, arg) ->
        AST.fcall_in_void_rule (AST.Void (Id, Func, Arg [])) f (AST.Arg arg)
        :: lst)
      [] list
  in
  let p_info, init =
    if is_start then
      ErrorEntrySet.fold
        (fun (ee, ee_s) (p_info_init, init_list) ->
          ( Constant.expand_string_value ee p_info_init,
            apply_rule
              (get_void_func AST.Id ~ee ~es:ee_s summary m_info c_info s_map)
            |> List.fold_left
                 (fun lst new_tc ->
                   mk_cost empty_p new_tc empty_id_map 0 :: lst)
                 []
            |> List.rev_append init_list ))
        (find_ee e_method error_summary cg summary call_prop_map m_info c_info)
        (p_info, [])
    else (p_info, queue)
  in
  let result =
    mk_testcase summary m_info type_info c_info s_map i_info p_info init
  in
  if result = [] then (Incomplete, (ImportSet.empty, ""), empty_id_map, [])
  else List.hd result
