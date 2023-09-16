module Relation = Language.Relation
module Value = Language.Value
module Condition = Language.Condition
module MethodInfo = Language.MethodInfo
module SummaryMap = Language.SummaryMap
module CallPropMap = Language.CallPropMap
module ClassInfo = Language.ClassInfo
module SetterMap = Language.SetterMap
module FieldSet = Language.FieldSet
module EnumInfo = Language.EnumInfo
module CG = Callgraph.G
module IG = Inheritance.G
module AST = Language.AST

module ImportSet = Set.Make (struct
  type t = string

  let compare = compare
end)

module ErrorEntrySet = Set.Make (struct
  type t = string * Language.summary

  let compare = compare
end)

let outer = ref 0

let recv = ref 0

let new_var = ref 0

let pkg = ref ""

let z3ctx =
  Z3.mk_context
    [
      ("model", "true");
      ("proof", "true");
      ("dump_models", "true");
      ("unsat_core", "true");
    ]

let solver = Z3.Solver.mk_solver z3ctx None

(* penalty for unsatisfied conditions, # of non-terminals for p *)
let get_cost p = (p |> fst, AST.count_nt (p |> snd))

let rec find_relation given_symbol relation =
  match Relation.M.find_opt given_symbol relation with
  | Some find_symbol -> find_relation find_symbol relation
  | None -> given_symbol

let get_rh_name ~is_var rh =
  if is_var then match rh with Condition.RH_Var v -> v | _ -> ""
  else match rh with Condition.RH_Symbol s -> s | _ -> ""

let get_next_symbol symbol memory =
  let next_symbol = Condition.M.find_opt symbol memory in
  match next_symbol with
  | Some sym -> (
      match Condition.M.find_opt Condition.RH_Any sym with
      | Some s -> s
      | None -> symbol)
  | None -> symbol

let rec get_tail_symbol field_name symbol memory =
  let next_symbol = Condition.M.find_opt symbol memory in
  match next_symbol with
  | Some sym -> (
      match Condition.M.find_opt (Condition.RH_Var field_name) sym with
      | Some s -> get_tail_symbol field_name s memory
      | None -> (
          match Condition.M.find_opt Condition.RH_Any sym with
          | Some any_sym -> get_tail_symbol field_name any_sym memory
          | None -> symbol))
  | None -> symbol

let get_id_symbol id variable memory =
  let this_symbol =
    Condition.M.fold
      (fun symbol symbol_id this_symbol ->
        match symbol_id with
        | Condition.RH_Var v when v = "this" -> symbol
        | _ -> this_symbol)
      variable Condition.RH_Any
  in
  let this_tail_symbol = get_tail_symbol "this" this_symbol memory in
  let this_field_mem = Condition.M.find_opt this_tail_symbol memory in
  match this_field_mem with
  | None -> this_symbol
  | Some mem -> (
      let if_field_symbol = Condition.M.find_opt (Condition.RH_Var id) mem in
      match if_field_symbol with
      | Some field_symbol -> field_symbol
      | None ->
          let symbol =
            Condition.M.fold
              (fun symbol symbol_id this_tail_symbol ->
                match symbol_id with
                | Condition.RH_Var v when v = id -> symbol
                | _ -> this_tail_symbol)
              variable Condition.RH_Any
          in
          symbol)

let find_variable head_symbol variables =
  match Condition.M.find_opt (Condition.RH_Symbol head_symbol) variables with
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
   value is set only when the symbol is RH_Index.
*)
let get_head_symbol symbol memory =
  Condition.M.fold
    (fun head_symbol trace head_list ->
      let head =
        find_real_head (get_rh_name ~is_var:false head_symbol) memory
      in
      Condition.M.fold
        (fun trace_head trace_tail head_list ->
          match trace_tail with
          | Condition.RH_Symbol s when symbol = s -> [ (symbol, None, head) ]
          | _ -> (
              match trace_head with
              | Condition.RH_Index i when symbol = i ->
                  ( symbol,
                    Some
                      (get_next_symbol trace_tail memory
                      |> get_rh_name ~is_var:false),
                    head )
                  :: head_list
              | _ -> head_list))
        trace head_list)
    memory []

(* memory: Condition.mem *)
(* return: (callee_actual_symbol * head_symbol) list *)
(* if head = "" then this symbol can be any value *)
let get_head_symbol_list symbols (_, memory) =
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
          match hd |> snd with
          | Language.This _ -> get_index (count + 1) tl
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
  List.map
    (fun (symbol, idx_value, head_symbol) ->
      if head_symbol = "" then (symbol, head_symbol, -1)
      else
        match idx_value with
        | None ->
            let index = get_param_index head_symbol variables formal_params in
            (symbol, head_symbol, index)
        | _ -> (symbol, head_symbol, -1))
    head_symbol_list

(* caller_prop: contains boitv, citv, precond, postcond, arg *)
(* return: (caller_value_symbol * callee_value_symbol) *)
let get_caller_value_symbol_list caller_prop callee_param_index_list =
  List.map
    (fun (callee_value_symbol, _, index) ->
      if index = -1 then ("", callee_value_symbol)
      else
        let caller_value_symbol = List.nth caller_prop.Language.args index in
        (caller_value_symbol, callee_value_symbol))
    callee_param_index_list

let get_field_symbol id symbol mem =
  get_tail_symbol
    (id |> get_rh_name ~is_var:true)
    (Condition.RH_Symbol symbol) mem

let get_value_symbol key sym c t_mem c_mem =
  let c_sym =
    match Condition.M.find_opt key c with
    | Some s -> s
    | None -> (
        match Condition.M.find_opt Condition.RH_Any c with
        | Some s -> s
        | None -> Condition.RH_Any (*fail to match*))
  in
  let field_name = get_rh_name ~is_var:true key in
  let tail_t_symbol =
    get_tail_symbol field_name sym t_mem |> get_rh_name ~is_var:false
  in
  let tail_c_symbol =
    get_tail_symbol field_name c_sym c_mem |> get_rh_name ~is_var:false
  in
  (tail_t_symbol, tail_c_symbol)

let get_value_symbol_list ~is_init t_summary c_summary vs_list =
  if is_init then
    (*this, this*)
    let t_symbol, c_symbol = vs_list |> List.hd in
    let t_var, t_mem = t_summary.Language.precond in
    let c_var, c_mem = c_summary.Language.precond in
    let c_t_mem = Condition.M.find_opt (Condition.RH_Symbol t_symbol) t_var in
    let c_c_mem = Condition.M.find_opt (Condition.RH_Symbol c_symbol) c_var in
    match (c_t_mem, c_c_mem) with
    | None, _ | _, None -> [ (t_symbol, c_symbol) ]
    | Some t_id, Some c_id -> (
        let t_symbol = get_field_symbol t_id t_symbol t_mem in
        let c_symbol = get_field_symbol c_id c_symbol c_mem in
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

let check_intersect ~is_init caller_prop callee_summary vs_list =
  let check_one caller_symbol callee_symbol =
    try
      let caller_value =
        Value.M.find caller_symbol caller_prop.Language.value
      in
      let callee_value =
        Value.M.find callee_symbol callee_summary.Language.value
      in
      match (caller_value, callee_value) with
      | Eq eq_v1, Eq eq_v2 ->
          if eq_v1 = eq_v2 then (caller_prop.Language.value, true)
          else (caller_prop.Language.value, false)
      | Eq eq_v, Neq neq_v | Neq neq_v, Eq eq_v ->
          if eq_v = neq_v then (caller_prop.Language.value, false)
          else (caller_prop.Language.value, true)
      | Eq eq_v, Le le_v | Le le_v, Eq eq_v -> (
          match (eq_v, le_v) with
          | Int eq_i, Int le_i
          | Long eq_i, Long le_i
          | Int eq_i, Long le_i
          | Long eq_i, Int le_i ->
              if eq_i <= le_i then (caller_prop.Language.value, true)
              else (caller_prop.Language.value, false)
          | Float eq_f, Float le_f
          | Double eq_f, Double le_f
          | Float eq_f, Double le_f
          | Double eq_f, Float le_f ->
              if eq_f <= le_f then (caller_prop.Language.value, true)
              else (caller_prop.Language.value, false)
          | _ -> failwith "not allowed type in eq, le")
      | Eq eq_v, Lt lt_v | Lt lt_v, Eq eq_v -> (
          match (eq_v, lt_v) with
          | Int eq_i, Int lt_i
          | Long eq_i, Long lt_i
          | Int eq_i, Long lt_i
          | Long eq_i, Int lt_i ->
              if eq_i < lt_i then (caller_prop.Language.value, true)
              else (caller_prop.Language.value, false)
          | Float eq_f, Float lt_f
          | Double eq_f, Double lt_f
          | Float eq_f, Double lt_f
          | Double eq_f, Float lt_f ->
              if eq_f < lt_f then (caller_prop.Language.value, true)
              else (caller_prop.Language.value, false)
          | _ -> failwith "not allowed type in eq, lt")
      | Eq eq_v, Ge ge_v | Ge ge_v, Eq eq_v -> (
          match (eq_v, ge_v) with
          | Int eq_i, Int ge_i
          | Long eq_i, Long ge_i
          | Int eq_i, Long ge_i
          | Long eq_i, Int ge_i ->
              if eq_i >= ge_i then (caller_prop.Language.value, true)
              else (caller_prop.Language.value, false)
          | Float eq_f, Float ge_f
          | Double eq_f, Double ge_f
          | Float eq_f, Double ge_f
          | Double eq_f, Float ge_f ->
              if eq_f >= ge_f then (caller_prop.Language.value, true)
              else (caller_prop.Language.value, false)
          | _ -> failwith "not allowed type in eq, ge")
      | Eq eq_v, Gt gt_v | Gt gt_v, Eq eq_v -> (
          match (eq_v, gt_v) with
          | Int eq_i, Int gt_i
          | Long eq_i, Long gt_i
          | Int eq_i, Long gt_i
          | Long eq_i, Int gt_i ->
              if eq_i > gt_i then (caller_prop.Language.value, true)
              else (caller_prop.Language.value, false)
          | Float eq_f, Float gt_f
          | Double eq_f, Double gt_f
          | Float eq_f, Double gt_f
          | Double eq_f, Float gt_f ->
              if eq_f > gt_f then (caller_prop.Language.value, true)
              else (caller_prop.Language.value, false)
          | _ -> failwith "not allowed type in eq, gt")
      | Eq eq_v, Between (btw_min, btw_max)
      | Between (btw_min, btw_max), Eq eq_v -> (
          match (eq_v, btw_min, btw_max) with
          | Int eq_i, Int btw_min_i, Int btw_max_i
          | Int eq_i, Int btw_min_i, Long btw_max_i
          | Int eq_i, Long btw_min_i, Int btw_max_i
          | Int eq_i, Long btw_min_i, Long btw_max_i
          | Long eq_i, Int btw_min_i, Int btw_max_i
          | Long eq_i, Int btw_min_i, Long btw_max_i
          | Long eq_i, Long btw_min_i, Int btw_max_i
          | Long eq_i, Long btw_min_i, Long btw_max_i ->
              if eq_i >= btw_min_i && eq_i <= btw_max_i then
                (caller_prop.Language.value, true)
              else (caller_prop.Language.value, false)
          | Float eq_f, Float btw_min_f, Float btw_max_f
          | Float eq_f, Float btw_min_f, Double btw_max_f
          | Float eq_f, Double btw_min_f, Float btw_max_f
          | Float eq_f, Double btw_min_f, Double btw_max_f
          | Double eq_f, Float btw_min_f, Float btw_max_f
          | Double eq_f, Float btw_min_f, Double btw_max_f
          | Double eq_f, Double btw_min_f, Float btw_max_f
          | Double eq_f, Double btw_min_f, Double btw_max_f ->
              if eq_f >= btw_min_f && eq_f <= btw_max_f then
                (caller_prop.Language.value, true)
              else (caller_prop.Language.value, false)
          | _ -> failwith "not allowed type in eq, between")
      | Eq eq_v, Outside (out_min, out_max)
      | Outside (out_min, out_max), Eq eq_v -> (
          match (eq_v, out_min, out_max) with
          | Int eq_i, Int o_min_i, Int o_max_i
          | Int eq_i, Int o_min_i, Long o_max_i
          | Int eq_i, Long o_min_i, Int o_max_i
          | Int eq_i, Long o_min_i, Long o_max_i
          | Long eq_i, Int o_min_i, Int o_max_i
          | Long eq_i, Int o_min_i, Long o_max_i
          | Long eq_i, Long o_min_i, Int o_max_i
          | Long eq_i, Long o_min_i, Long o_max_i ->
              if eq_i < o_min_i && eq_i > o_max_i then
                (caller_prop.Language.value, true)
              else (caller_prop.Language.value, false)
          | Float eq_f, Float o_min_f, Float o_max_f
          | Float eq_f, Float o_min_f, Double o_max_f
          | Float eq_f, Double o_min_f, Float o_max_f
          | Float eq_f, Double o_min_f, Double o_max_f
          | Double eq_f, Float o_min_f, Float o_max_f
          | Double eq_f, Float o_min_f, Double o_max_f
          | Double eq_f, Double o_min_f, Float o_max_f
          | Double eq_f, Double o_min_f, Double o_max_f ->
              if eq_f < o_min_f && eq_f > o_max_f then
                (caller_prop.Language.value, true)
              else (caller_prop.Language.value, false)
          | _ -> failwith "not allowed type in eq, outside")
      | Le le_v, Ge ge_v | Ge ge_v, Le le_v -> (
          match (le_v, ge_v) with
          | Int le_i, Int ge_i
          | Long le_i, Long ge_i
          | Int le_i, Long ge_i
          | Long le_i, Int ge_i ->
              if le_i >= ge_i then (caller_prop.Language.value, true)
              else (caller_prop.Language.value, false)
          | Float le_f, Float ge_f
          | Double le_f, Double ge_f
          | Float le_f, Double ge_f
          | Double le_f, Float ge_f ->
              if le_f >= ge_f then (caller_prop.Language.value, true)
              else (caller_prop.Language.value, false)
          | _ -> failwith "not allowed type in le, ge")
      | Le l_v, Gt g_v
      | Lt l_v, Ge g_v
      | Lt l_v, Gt g_v
      | Ge g_v, Lt l_v
      | Gt g_v, Le l_v
      | Gt g_v, Lt l_v -> (
          match (l_v, g_v) with
          | Int l_i, Int g_i
          | Long l_i, Long g_i
          | Int l_i, Long g_i
          | Long l_i, Int g_i ->
              if l_i > g_i then (caller_prop.Language.value, true)
              else (caller_prop.Language.value, false)
          | Float l_f, Float g_f
          | Double l_f, Double g_f
          | Float l_f, Double g_f
          | Double l_f, Float g_f ->
              if l_f > g_f then (caller_prop.Language.value, true)
              else (caller_prop.Language.value, false)
          | _ -> failwith "not allowed type in le, ge")
      | Le le_v, Between (btw_min, btw_max)
      | Between (btw_min, btw_max), Le le_v -> (
          match (le_v, btw_min, btw_max) with
          | Int le_i, Int btw_min_i, Int _
          | Int le_i, Int btw_min_i, Long _
          | Long le_i, Long btw_min_i, Int _
          | Long le_i, Long btw_min_i, Long _
          | Int le_i, Long btw_min_i, Int _
          | Int le_i, Long btw_min_i, Long _
          | Long le_i, Int btw_min_i, Int _
          | Long le_i, Int btw_min_i, Long _ ->
              if le_i < btw_min_i then (caller_prop.Language.value, false)
              else (caller_prop.Language.value, true)
          | Float le_f, Float btw_min_f, Float _
          | Float le_f, Float btw_min_f, Double _
          | Double le_f, Double btw_min_f, Float _
          | Double le_f, Double btw_min_f, Double _
          | Float le_f, Double btw_min_f, Float _
          | Float le_f, Double btw_min_f, Double _
          | Double le_f, Float btw_min_f, Float _
          | Double le_f, Float btw_min_f, Double _ ->
              if le_f < btw_min_f then (caller_prop.Language.value, false)
              else (caller_prop.Language.value, true)
          | _ -> failwith "not allowed type in le, between")
      | Lt lt_v, Between (btw_min, btw_max)
      | Between (btw_min, btw_max), Lt lt_v -> (
          match (lt_v, btw_min, btw_max) with
          | Int lt_i, Int btw_min_i, Int _
          | Int lt_i, Int btw_min_i, Long _
          | Long lt_i, Long btw_min_i, Int _
          | Long lt_i, Long btw_min_i, Long _
          | Int lt_i, Long btw_min_i, Int _
          | Int lt_i, Long btw_min_i, Long _
          | Long lt_i, Int btw_min_i, Int _
          | Long lt_i, Int btw_min_i, Long _ ->
              if lt_i <= btw_min_i then (caller_prop.Language.value, false)
              else (caller_prop.Language.value, true)
          | Float lt_f, Float btw_min_f, Float _
          | Float lt_f, Float btw_min_f, Double _
          | Double lt_f, Double btw_min_f, Float _
          | Double lt_f, Double btw_min_f, Double _
          | Float lt_f, Double btw_min_f, Float _
          | Float lt_f, Double btw_min_f, Double _
          | Double lt_f, Float btw_min_f, Float _
          | Double lt_f, Float btw_min_f, Double _ ->
              if lt_f <= btw_min_f then (caller_prop.Language.value, false)
              else (caller_prop.Language.value, true)
          | _ -> failwith "not allowed type in lt, between")
      | Ge ge_v, Between (btw_min, btw_max)
      | Between (btw_min, btw_max), Ge ge_v -> (
          match (ge_v, btw_min, btw_max) with
          | Int ge_i, Int _, Int btw_max_i
          | Int ge_i, Long _, Int btw_max_i
          | Long ge_i, Int _, Long btw_max_i
          | Long ge_i, Long _, Long btw_max_i
          | Int ge_i, Int _, Long btw_max_i
          | Int ge_i, Long _, Long btw_max_i
          | Long ge_i, Int _, Int btw_max_i
          | Long ge_i, Long _, Int btw_max_i ->
              if ge_i > btw_max_i then (caller_prop.Language.value, false)
              else (caller_prop.Language.value, true)
          | Float ge_f, Float _, Float btw_max_f
          | Float ge_f, Double _, Float btw_max_f
          | Double ge_f, Float _, Double btw_max_f
          | Double ge_f, Double _, Double btw_max_f
          | Float ge_f, Float _, Double btw_max_f
          | Float ge_f, Double _, Double btw_max_f
          | Double ge_f, Float _, Float btw_max_f
          | Double ge_f, Double _, Float btw_max_f ->
              if ge_f > btw_max_f then (caller_prop.Language.value, false)
              else (caller_prop.Language.value, true)
          | _ -> failwith "not allowed type in ge, between")
      | Gt gt_v, Between (btw_min, btw_max)
      | Between (btw_min, btw_max), Gt gt_v -> (
          match (gt_v, btw_min, btw_max) with
          | Int gt_i, Int _, Int btw_max_i
          | Int gt_i, Long _, Int btw_max_i
          | Long gt_i, Int _, Long btw_max_i
          | Long gt_i, Long _, Long btw_max_i
          | Int gt_i, Int _, Long btw_max_i
          | Int gt_i, Long _, Long btw_max_i
          | Long gt_i, Int _, Int btw_max_i
          | Long gt_i, Long _, Int btw_max_i ->
              if gt_i >= btw_max_i then (caller_prop.Language.value, false)
              else (caller_prop.Language.value, true)
          | Float gt_f, Float _, Float btw_max_f
          | Float gt_f, Double _, Float btw_max_f
          | Double gt_f, Float _, Double btw_max_f
          | Double gt_f, Double _, Double btw_max_f
          | Float gt_f, Float _, Double btw_max_f
          | Float gt_f, Double _, Double btw_max_f
          | Double gt_f, Float _, Float btw_max_f
          | Double gt_f, Double _, Float btw_max_f ->
              if gt_f >= btw_max_f then (caller_prop.Language.value, false)
              else (caller_prop.Language.value, true)
          | _ -> failwith "not allowed type in gt, between")
      | Between (caller_min, caller_max), Between (callee_min, callee_max) -> (
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
              if r_max_i < e_min_i || e_max_i < r_min_i then
                (caller_prop.Language.value, false)
              else (caller_prop.Language.value, true)
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
              if r_max_f < e_min_f || e_max_f < r_min_f then
                (caller_prop.Language.value, false)
              else (caller_prop.Language.value, true)
          | _ -> failwith "not allowed type in between, between")
      | Between (btw_min, btw_max), Outside (out_min, out_max)
      | Outside (out_min, out_max), Between (btw_min, btw_max) -> (
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
              if o_min_i <= btw_min_i && o_max_i >= btw_max_i then
                (caller_prop.Language.value, false)
              else (caller_prop.Language.value, true)
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
          | Double btw_min_f, Double btw_max_f, Double o_min_f, Double o_max_f
            ->
              if btw_min_f <= o_min_f && btw_max_f >= o_max_f then
                (caller_prop.Language.value, false)
              else (caller_prop.Language.value, true)
          | _ -> failwith "not allowed type in between, outside")
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
          (caller_prop.Language.value, true)
    with Not_found -> (
      try
        let callee_value =
          Value.M.find callee_symbol callee_summary.Language.value
        in
        ( Value.M.add caller_symbol callee_value caller_prop.Language.value
          |> Value.M.add callee_symbol callee_value,
          true )
      with Not_found -> (
        try
          (* constructor prop propagation *)
          let caller_value =
            Value.M.find caller_symbol caller_prop.Language.value
          in
          ( Value.M.add callee_symbol caller_value callee_summary.Language.value,
            true )
        with Not_found -> (caller_prop.Language.value, true)))
  in
  let vs_list =
    get_value_symbol_list ~is_init caller_prop callee_summary vs_list
  in
  List.map
    (fun (caller_symbol, callee_symbol) ->
      check_one caller_symbol callee_symbol)
    vs_list

(* value_symbol_list: (caller, callee) list
   callee_sym_list: (symbol, value, head) list --> value is set only when symbol is index
*)
let combine_memory base_summary value_symbol_list callee_sym_list =
  let _, memory = base_summary.Language.precond in
  List.fold_left
    (fun mem (r, _) ->
      List.fold_left
        (fun mem (s, v, head) ->
          match v with
          | Some value -> (
              match Condition.M.find_opt (Condition.RH_Symbol r) mem with
              | Some m when find_real_head r memory = head ->
                  Condition.M.add (Condition.RH_Symbol r)
                    (Condition.M.add (Condition.RH_Index s)
                       (Condition.RH_Symbol value) m)
                    mem
              | None when find_real_head r memory = head ->
                  Condition.M.add (Condition.RH_Symbol r)
                    (Condition.M.add (Condition.RH_Index s)
                       (Condition.RH_Symbol value) Condition.M.empty)
                    mem
              | _ -> mem)
          | _ -> mem)
        mem callee_sym_list)
    memory value_symbol_list

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
  let callee_m_info = MethodInfo.M.find callee_method m_info in
  let callee_params = callee_m_info.MethodInfo.formal_params in
  let callee_symbols = callee_summary.Language.value |> get_symbol_list in
  let callee_head_symbols =
    get_head_symbol_list callee_symbols callee_summary.Language.precond
  in
  let param_indexes =
    get_param_index_list callee_head_symbols callee_summary.Language.precond
      callee_params
  in
  let value_symbol_list =
    get_caller_value_symbol_list call_prop param_indexes
  in
  let caller_new_mem =
    combine_memory call_prop value_symbol_list callee_head_symbols
  in
  let intersect_value =
    let values_and_check =
      check_intersect ~is_init:false call_prop callee_summary value_symbol_list
    in
    let values = combine_value call_prop.Language.value values_and_check in
    let check = List.filter (fun (_, c) -> c = false) values_and_check in
    (values, check)
  in
  let values, check = intersect_value in
  if check = [] then (values, caller_new_mem, true)
  else (values, caller_new_mem, false)

let new_value_summary old_summary new_value =
  Language.
    {
      relation = old_summary.relation;
      value = new_value;
      precond = old_summary.precond;
      postcond = old_summary.postcond;
      args = old_summary.args;
    }

let new_mem_summary old_summary new_mem =
  Language.
    {
      relation = old_summary.relation;
      value = old_summary.value;
      precond = (old_summary.precond |> fst, new_mem);
      postcond = (old_summary.postcond |> fst, new_mem);
      args = old_summary.args;
    }

let replace_nested_symbol str = Str.global_replace Regexp.dollar "." str

let is_primitive x =
  match AST.get_vinfo x |> fst with
  | Int | Long | Float | Double | Bool | Char | String -> true
  | _ -> false

let is_receiver id = if id = "con_recv" || id = "con_outer" then true else false

let is_nested_class name = String.contains name '$'

let is_normal_class class_name c_info =
  match ClassInfo.M.find_opt class_name c_info with
  | Some typ -> (
      match typ.ClassInfo.class_type with
      | Language.Static | Language.Normal -> true
      | _ -> false)
  | None -> true (* modeling class *)

let is_s_class name (c_info, _) =
  let name =
    Regexp.global_rm (Str.regexp "\\.<.*>(.*)$") name
    |> Regexp.global_rm (Str.regexp "(.*)$")
  in
  match ClassInfo.M.find_opt name c_info with
  | Some typ -> (
      match typ.ClassInfo.class_type with Language.Static -> true | _ -> false)
  | None -> false

let is_private_class class_package c_info =
  match ClassInfo.M.find_opt class_package (c_info |> fst) with
  | Some info -> (
      let class_type = info.ClassInfo.class_type in
      match class_type with Language.Private -> true | _ -> false)
  | None -> false

let is_s_method m_name m_info =
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
  | Some m -> ( match m.MethodInfo.modifier with Public -> true | _ -> false)

let is_init_method method_name =
  Str.string_match (".*\\.<init>" |> Str.regexp) method_name 0

let is_array_init m =
  let arr =
    [ "Int"; "Long"; "Float"; "Double"; "Bool"; "Char"; "String"; "Object" ]
  in
  let rec check arr =
    match arr with
    | h :: t ->
        if Str.string_match (h ^ "Array\\.<init>" |> Str.regexp) m 0 then true
        else check t
    | [] -> false
  in
  check arr

let get_class_name ~infer method_name =
  if infer then Regexp.global_rm ("\\..+(.*)" |> Str.regexp) method_name
  else Regexp.global_rm ("(.*)" |> Str.regexp) method_name

let get_package_from_param formal_params =
  List.fold_left
    (fun found (import, var) ->
      match var with Language.This _ -> import | _ -> found)
    "" formal_params

(* e.g., java.util.Date --> contain class name *)
let get_package_from_method t_method (c_info, _) =
  let class_name = get_class_name ~infer:true t_method in
  let full_class_name =
    ClassInfo.M.fold
      (fun full_name _ find_name ->
        let name = Str.split Regexp.dot full_name |> List.rev |> List.hd in
        if class_name = name then full_name else find_name)
      c_info ""
  in
  full_class_name

let get_package t_method m_info c_info =
  let info = MethodInfo.M.find t_method m_info in
  let p_package = get_package_from_param info.MethodInfo.formal_params in
  let m_package = get_package_from_method t_method c_info in
  if p_package = "" then m_package else p_package

(* e.g., java.util. --> not contain class name *)
let get_import t_method (c_info, _) =
  let class_name = get_class_name ~infer:true t_method in
  let full_class_name =
    ClassInfo.M.fold
      (fun full_name _ find_name ->
        let name = Str.split Regexp.dot full_name |> List.rev |> List.hd in
        if class_name = name then
          let name = Str.global_replace Regexp.dollar "\\$" name in
          let s = name ^ "$" in
          Regexp.global_rm (Str.regexp s) full_name
        else find_name)
      c_info ""
  in
  full_class_name

let is_test_file file_name =
  Str.string_match (Str.regexp ".*/test/.*") file_name 0

let is_public_or_default method_name m_info c_info =
  let info = MethodInfo.M.find method_name m_info in
  let is_test_file =
    (* If this method is a method in the test file,
       don't use it even if the modifier is public*)
    is_test_file info.MethodInfo.filename
  in
  let package = get_package method_name m_info c_info in
  let name =
    try
      Str.split Regexp.dot package
      |> List.rev |> List.hd
      |> Str.global_replace Regexp.dollar "\\$"
    with _ -> ""
  in
  let s = name ^ "$" in
  let package = Regexp.global_rm (Str.regexp s) package in
  if Str.string_match (Str.regexp package) !pkg 0 then
    match info.MethodInfo.modifier with
    | Default | Protected | Public -> true
    | _ -> false
  else
    match info.MethodInfo.modifier with
    | Public when not is_test_file -> true
    | _ -> false

let is_recursive_param parent_class method_name m_info =
  let info = MethodInfo.M.find method_name m_info in
  let this = Language.Object parent_class in
  List.fold_left
    (fun check (_, var) ->
      match var with
      | Language.Var (typ, _) when typ = this -> true
      | _ -> check)
    false info.MethodInfo.formal_params

let is_void_method m_name s_map =
  let c_name = get_class_name ~infer:true m_name in
  let slist = try SetterMap.M.find c_name s_map with _ -> [] in
  let rec check lst =
    match lst with
    | hd :: _ when m_name = (hd |> fst) -> true
    | _ :: tl -> check tl
    | [] -> false
  in
  check slist

let calc_z3 id z3exp =
  let solver = Z3.Solver.mk_solver z3ctx None in
  Z3.Solver.add solver z3exp;
  let _ = Z3.Solver.check solver [] in
  let model = Z3.Solver.get_model solver |> Option.get in
  let value = Z3.Model.eval model id false in
  match value with
  | Some v ->
      if Z3.Arithmetic.is_real v then Z3.Arithmetic.Real.numeral_to_string v
      else Z3.Arithmetic.Integer.numeral_to_string v
  | None -> ""

let default_value_list typ =
  let default_value =
    match typ with
    | Language.Int | Long ->
        [
          AST.Primitive (Z 1);
          AST.Primitive (Z 0);
          AST.Primitive (Z (-1));
          AST.Primitive (Z 100);
          AST.Primitive (Z (-100));
          AST.Primitive (Z 1000);
          AST.Primitive (Z (-1000));
        ]
    | Float | Double ->
        [
          AST.Primitive (R 1.0);
          AST.Primitive (R 0.0);
          AST.Primitive (R (-1.0));
          AST.Primitive (R 100.0);
          AST.Primitive (R (-100.0));
          AST.Primitive (R 1000.0);
          AST.Primitive (R (-1000.0));
        ]
    | Bool -> [ AST.Primitive (B false); AST.Primitive (B true) ]
    | Char -> [ AST.Primitive (C 'x') ]
    | String -> [ AST.Null; AST.Primitive (S ""); AST.Primitive (S "string") ]
    | _ -> [ AST.Null ]
  in
  default_value

let not_found_value = function Value.Eq None -> true | _ -> false

let calc_value_list typ org_list =
  List.fold_left
    (fun lst x -> (1000, x) :: lst)
    org_list (default_value_list typ)

let calc_value id = function
  | Value.Eq v -> (
      match v with
      | Int i | Long i ->
          let var = Z3.Arithmetic.Integer.mk_const_s z3ctx id in
          let exp =
            Z3.Arithmetic.Integer.mk_numeral_i z3ctx i
            |> Z3.Boolean.mk_eq z3ctx var
          in
          calc_value_list Int
            [ (0, AST.Primitive (Z (calc_z3 var [ exp ] |> int_of_string))) ]
      | Float f | Double f ->
          let var = Z3.Arithmetic.Real.mk_const_s z3ctx id in
          let exp =
            Z3.Arithmetic.Real.mk_numeral_s z3ctx (f |> string_of_float)
            |> Z3.Boolean.mk_eq z3ctx var
          in
          calc_value_list Float
            [ (0, AST.Primitive (R (calc_z3 var [ exp ] |> float_of_string))) ]
      | Bool b -> calc_value_list Bool [ (0, AST.Primitive (B b)) ]
      | Char c -> calc_value_list Char [ (0, AST.Primitive (C c)) ]
      | String s -> calc_value_list String [ (0, AST.Primitive (S s)) ]
      | Null -> [ (0, AST.Null) ]
      | _ -> failwith "not implemented eq")
  | Value.Neq v -> (
      match v with
      | Int i | Long i ->
          let var = Z3.Arithmetic.Integer.mk_const_s z3ctx id in
          let exp =
            Z3.Arithmetic.Integer.mk_numeral_i z3ctx i
            |> Z3.Boolean.mk_eq z3ctx var |> Z3.Boolean.mk_not z3ctx
          in
          calc_value_list Int
            [ (0, AST.Primitive (Z (calc_z3 var [ exp ] |> int_of_string))) ]
      | Float f | Double f ->
          let var = Z3.Arithmetic.Real.mk_const_s z3ctx id in
          let exp =
            Z3.Arithmetic.Real.mk_numeral_s z3ctx (f |> string_of_float)
            |> Z3.Boolean.mk_eq z3ctx var |> Z3.Boolean.mk_not z3ctx
          in
          calc_value_list Float
            [ (0, AST.Primitive (R (calc_z3 var [ exp ] |> float_of_string))) ]
      | Bool b -> calc_value_list Bool [ (0, AST.Primitive (B (b |> not))) ]
      | String s ->
          calc_value_list String [ (0, AST.Primitive (S ("not_" ^ s))) ]
      | Null ->
          (* Among the const, only the string can be defined as null *)
          List.fold_left
            (fun lst x ->
              if x = AST.Null then (1000, x) :: lst else (0, x) :: lst)
            []
            (default_value_list String)
      | _ -> failwith "not implemented neq")
  | Value.Le v -> (
      match v with
      | Int i | Long i ->
          let var = Z3.Arithmetic.Integer.mk_const_s z3ctx id in
          let exp =
            Z3.Arithmetic.Integer.mk_numeral_i z3ctx i
            |> Z3.Arithmetic.mk_le z3ctx var
          in
          calc_value_list Int
            [ (0, AST.Primitive (Z (calc_z3 var [ exp ] |> int_of_string))) ]
      | Float f | Double f ->
          let var = Z3.Arithmetic.Real.mk_const_s z3ctx id in
          let exp =
            Z3.Arithmetic.Real.mk_numeral_s z3ctx (f |> string_of_float)
            |> Z3.Arithmetic.mk_le z3ctx var
          in
          calc_value_list Float
            [ (0, AST.Primitive (R (calc_z3 var [ exp ] |> float_of_string))) ]
      | _ -> failwith "not implemented le")
  | Value.Lt v -> (
      match v with
      | Int i | Long i ->
          let var = Z3.Arithmetic.Integer.mk_const_s z3ctx id in
          let exp =
            Z3.Arithmetic.Integer.mk_numeral_i z3ctx i
            |> Z3.Arithmetic.mk_lt z3ctx var
          in
          calc_value_list Int
            [ (0, AST.Primitive (Z (calc_z3 var [ exp ] |> int_of_string))) ]
      | Float f | Double f ->
          let var = Z3.Arithmetic.Real.mk_const_s z3ctx id in
          let exp =
            Z3.Arithmetic.Real.mk_numeral_s z3ctx (f |> string_of_float)
            |> Z3.Arithmetic.mk_lt z3ctx var
          in
          calc_value_list Float
            [ (0, AST.Primitive (R (calc_z3 var [ exp ] |> float_of_string))) ]
      | _ -> failwith "not implemented lt")
  | Value.Ge v -> (
      match v with
      | Int i | Long i ->
          let var = Z3.Arithmetic.Integer.mk_const_s z3ctx id in
          let exp =
            Z3.Arithmetic.Integer.mk_numeral_i z3ctx i
            |> Z3.Arithmetic.mk_ge z3ctx var
          in
          calc_value_list Int
            [ (0, AST.Primitive (Z (calc_z3 var [ exp ] |> int_of_string))) ]
      | Float f | Double f ->
          let var = Z3.Arithmetic.Real.mk_const_s z3ctx id in
          let exp =
            Z3.Arithmetic.Real.mk_numeral_s z3ctx (f |> string_of_float)
            |> Z3.Arithmetic.mk_ge z3ctx var
          in
          calc_value_list Float
            [ (0, AST.Primitive (R (calc_z3 var [ exp ] |> float_of_string))) ]
      | _ -> failwith "not implemented ge")
  | Value.Gt v -> (
      match v with
      | Int i | Long i ->
          let var = Z3.Arithmetic.Integer.mk_const_s z3ctx id in
          let exp =
            Z3.Arithmetic.Integer.mk_numeral_i z3ctx i
            |> Z3.Arithmetic.mk_gt z3ctx var
          in
          calc_value_list Int
            [ (0, AST.Primitive (Z (calc_z3 var [ exp ] |> int_of_string))) ]
      | Float f | Double f ->
          let var = Z3.Arithmetic.Real.mk_const_s z3ctx id in
          let exp =
            Z3.Arithmetic.Real.mk_numeral_s z3ctx (f |> string_of_float)
            |> Z3.Arithmetic.mk_gt z3ctx var
          in
          [ (0, AST.Primitive (R (calc_z3 var [ exp ] |> float_of_string))) ]
      | _ -> failwith "not implemented gt")
  | Value.Between (v1, v2) -> (
      match (v1, v2) with
      | Int i1, Int i2 | Long i1, Long i2 | Int i1, Long i2 | Long i1, Int i2 ->
          let var = Z3.Arithmetic.Integer.mk_const_s z3ctx id in
          let exp =
            [
              Z3.Arithmetic.Integer.mk_numeral_i z3ctx i1
              |> Z3.Arithmetic.mk_ge z3ctx var;
              Z3.Arithmetic.Integer.mk_numeral_i z3ctx i2
              |> Z3.Arithmetic.mk_le z3ctx var;
            ]
          in
          calc_value_list Int
            [ (0, AST.Primitive (Z (calc_z3 var exp |> int_of_string))) ]
      | Float f1, Float f2
      | Double f1, Double f2
      | Float f1, Double f2
      | Double f1, Float f2 ->
          let var = Z3.Arithmetic.Real.mk_const_s z3ctx id in
          let exp =
            [
              Z3.Arithmetic.Real.mk_numeral_s z3ctx (f1 |> string_of_float)
              |> Z3.Arithmetic.mk_ge z3ctx var;
              Z3.Arithmetic.Real.mk_numeral_s z3ctx (f2 |> string_of_float)
              |> Z3.Arithmetic.mk_le z3ctx var;
            ]
          in
          calc_value_list Float
            [ (0, AST.Primitive (R (calc_z3 var exp |> float_of_string))) ]
      | _ -> failwith "not implemented between")
  | Value.Outside (v1, v2) -> (
      match (v1, v2) with
      | Int i1, Int i2 | Long i1, Long i2 | Int i1, Long i2 | Long i1, Int i2 ->
          let var = Z3.Arithmetic.Integer.mk_const_s z3ctx id in
          let exp =
            [
              Z3.Arithmetic.Integer.mk_numeral_i z3ctx i1
              |> Z3.Arithmetic.mk_lt z3ctx var;
              Z3.Arithmetic.Integer.mk_numeral_i z3ctx i2
              |> Z3.Arithmetic.mk_gt z3ctx var;
            ]
          in
          calc_value_list Int
            [ (0, AST.Primitive (Z (calc_z3 var exp |> int_of_string))) ]
      | Float f1, Float f2
      | Double f1, Double f2
      | Float f1, Double f2
      | Double f1, Float f2 ->
          let var = Z3.Arithmetic.Real.mk_const_s z3ctx id in
          let exp =
            [
              Z3.Arithmetic.Real.mk_numeral_s z3ctx (f1 |> string_of_float)
              |> Z3.Arithmetic.mk_lt z3ctx var;
              Z3.Arithmetic.Real.mk_numeral_s z3ctx (f2 |> string_of_float)
              |> Z3.Arithmetic.mk_gt z3ctx var;
            ]
          in
          calc_value_list Float
            [ (0, AST.Primitive (R (calc_z3 var exp |> float_of_string))) ]
      | _ -> failwith "not implemented outside")

let get_value typ id summary =
  let variables, mem = summary.Language.precond in
  let target_variable =
    Condition.M.fold
      (fun symbol variable find_variable ->
        match variable with
        | Condition.RH_Var var when var = id -> (
            match symbol with Condition.RH_Symbol s -> s | _ -> find_variable)
        | _ -> find_variable)
      variables ""
  in
  let target_variable =
    Condition.M.fold
      (fun symbol symbol_trace find_variable ->
        let symbol = get_rh_name ~is_var:false symbol in
        if symbol = target_variable then
          Condition.M.fold
            (fun _ trace_tail trace_find_var ->
              match trace_tail with
              | Condition.RH_Symbol s -> s
              | _ -> trace_find_var)
            symbol_trace find_variable
        else find_variable)
      mem target_variable
  in
  let values = summary.Language.value in
  let find_value =
    Value.M.fold
      (fun symbol value find_value ->
        if symbol = target_variable then value else find_value)
      values (Value.Eq None)
  in
  if not_found_value find_value then
    List.fold_left (fun lst x -> (0, x) :: lst) [] (default_value_list typ)
  else calc_value id find_value

let get_array_size array summary =
  let _, memory = summary.Language.precond in
  let array_symbol = AST.org_symbol array summary in
  match Condition.M.find_opt (Condition.RH_Symbol array_symbol) memory with
  | Some x -> Condition.M.fold (fun _ _ size -> size + 1) x 0
  | None -> 1

let satisfied_c method_summary id candidate_constructor summary =
  let c_summarys = SummaryMap.M.find candidate_constructor summary in
  let method_symbols, method_memory = method_summary.Language.precond in
  let id = if is_receiver id then "this" else id in
  let target_symbol =
    get_id_symbol id method_symbols method_memory |> get_rh_name ~is_var:false
  in
  if target_symbol = "" then (true, c_summarys |> List.hd)
  else
    let target_symbol =
      find_relation target_symbol method_summary.Language.relation
    in
    let check_summarys =
      List.map
        (fun c_summary ->
          let c_target_symbol =
            Condition.M.fold
              (fun symbol p_id target ->
                let symbol = get_rh_name ~is_var:false symbol in
                match p_id with
                | Condition.RH_Var pre_id when pre_id = "this" -> symbol
                | _ -> target)
              (c_summary.Language.postcond |> fst)
              ""
          in
          ( check_intersect ~is_init:true method_summary c_summary
              [ (target_symbol, c_target_symbol) ],
            c_summary ))
        c_summarys
    in
    List.fold_left
      (fun check_value (check_summary, c_summary) ->
        let check = List.filter (fun (_, c) -> c = false) check_summary in
        let new_c_summary =
          combine_value c_summary.Language.value check_summary
          |> new_value_summary c_summary
        in
        if check = [] then (true, new_c_summary) else check_value)
      (false, Language.empty_summary)
      check_summarys

let match_constructor_name class_name method_name =
  let class_name =
    Str.split Regexp.dot class_name
    |> List.rev |> List.hd
    |> Str.global_replace Regexp.dollar "\\$"
  in
  Str.string_match (class_name ^ "\\.<init>" |> Str.regexp) method_name 0

let match_return_object class_name method_name m_info =
  let class_name =
    Str.split Regexp.dot class_name
    |> List.rev |> List.hd
    |> Str.global_replace Regexp.dollar "\\$"
  in
  let info = MethodInfo.M.find method_name m_info in
  let return = info.MethodInfo.return in
  Str.string_match (Str.regexp class_name) return 0

let get_clist (class_package, class_name) m_info (c_info, ig) =
  let full_class_name =
    if class_package = "" then class_name else class_package
  in
  let class_to_find =
    try IG.succ ig full_class_name |> List.cons full_class_name
    with Invalid_argument _ -> [ full_class_name ]
  in
  MethodInfo.M.fold
    (fun method_name _ method_list ->
      List.fold_left
        (fun init_list class_name_to_find ->
          if
            is_normal_class class_name_to_find c_info
            && is_private method_name m_info |> not
            && match_constructor_name class_name_to_find method_name
          then (method_name, class_name_to_find) :: init_list
          else init_list)
        method_list class_to_find)
    m_info []

let find_class_file =
  List.fold_left
    (fun gvar_list const ->
      (0, AST.GlobalConstant (const ^ ".class")) :: gvar_list)
    []
    [ "unitcon_interface"; "unitcon_enum" ]

let find_enum_var_list c_name e_info =
  if EnumInfo.M.mem c_name e_info then
    List.fold_left
      (fun gvar_list const ->
        (0, AST.GlobalConstant (c_name ^ "." ^ const)) :: gvar_list)
      []
      (EnumInfo.M.find c_name e_info)
  else []

let find_global_var_list c_name t_var mem summary m_info =
  let all_var cost s_trace =
    Condition.M.fold
      (fun head _ gvar_list ->
        match head with
        | Condition.RH_Var var ->
            (cost, AST.GlobalConstant (c_name ^ "." ^ var)) :: gvar_list
        | _ -> gvar_list)
      s_trace []
  in
  let compare_var t_var s_trace =
    Condition.M.fold
      (fun head _ gvar ->
        match head with
        | Condition.RH_Var var when var = t_var -> Some (c_name ^ "." ^ var)
        | _ -> gvar)
      s_trace None
  in
  SummaryMap.M.fold
    (fun init_name init_summary list ->
      let _, init_mem = (init_summary |> List.hd).Language.precond in
      if
        Str.string_match (c_name ^ "\\.<clinit>" |> Str.regexp) init_name 0
        && is_public init_name m_info
      then
        match t_var with
        | Some v ->
            (Condition.M.fold (fun _ s_trace list ->
                 match compare_var v s_trace with
                 | Some gv -> (0, AST.GlobalConstant gv) :: list
                 | None -> list))
              mem list
            |> (Condition.M.fold (fun _ s_trace list ->
                    List.rev_append (all_var 1000 s_trace) list))
                 init_mem
        | None ->
            (Condition.M.fold (fun _ s_trace list ->
                 List.rev_append (all_var 0 s_trace) list))
              init_mem list
      else list)
    summary []

let global_var_list class_name t_summary summary m_info e_info =
  let vars, mem = t_summary.Language.precond in
  let t_var =
    Condition.M.fold
      (fun symbol var find_var ->
        match var with
        | Condition.RH_Var var ->
            if Str.string_match (".*\\." ^ class_name |> Str.regexp) var 0 then
              Some (get_rh_name ~is_var:false symbol)
            else find_var
        | _ -> find_var)
      vars None
  in
  match t_var with
  | None ->
      if class_name = "Class" then find_class_file
      else
        let gvlist = find_global_var_list class_name None mem summary m_info in
        if gvlist = [] then find_enum_var_list class_name e_info else gvlist
  | Some x ->
      let target_variable =
        Condition.M.fold
          (fun symbol symbol_trace find_variable ->
            if get_rh_name ~is_var:false symbol = x then
              Condition.M.fold
                (fun trace_head _ trace_find_var ->
                  match trace_head with
                  | Condition.RH_Var var -> Some var
                  | _ -> trace_find_var)
                symbol_trace find_variable
            else find_variable)
          mem None
      in
      find_global_var_list class_name target_variable mem summary m_info

let mk_arg ~is_s param s =
  let param = if is_s then param else param |> List.tl in
  List.fold_left
    (fun params (i, v) ->
      match v with
      | Language.Var (typ, _) when typ = Language.None -> params
      | _ ->
          incr new_var;
          AST.
            {
              import = i;
              variable = (v, Some !new_var);
              field = FieldSet.S.empty;
              summary = s;
            }
          :: params)
    [] param
  |> List.rev

let get_field_map ret s_map =
  let c_name = AST.get_vinfo ret |> fst |> Language.get_class_name in
  List.fold_left
    (fun fm (_, fields) -> FieldSet.S.union fields fm)
    FieldSet.S.empty
    (try SetterMap.M.find c_name s_map with _ -> [])

let error_entry_func ee es m_info c_info =
  let param = (MethodInfo.M.find ee m_info).MethodInfo.formal_params in
  let f_arg = mk_arg ~is_s:(is_s_method ee m_info) param es in
  let import = get_package ee m_info c_info in
  let typ_list =
    if is_private_class import c_info then
      try IG.succ (c_info |> snd) import |> List.cons import
      with Invalid_argument _ -> [ import ]
    else [ import ]
  in
  List.fold_left
    (fun lst x ->
      ( AST.F
          {
            typ = x |> Str.split Regexp.dot |> List.rev |> List.hd;
            method_name = ee;
            import = x;
            summary = es;
          },
        f_arg )
      :: lst)
    [] typ_list

(* id is receiver variable *)
let get_void_func id ?(ee = "") ?(es = Language.empty_summary) m_info c_info
    s_map =
  if AST.is_id id then error_entry_func ee es m_info c_info
  else
    let var = AST.get_v id in
    let name =
      if var.import = "" then AST.get_vinfo id |> fst |> Language.get_class_name
      else
        get_class_name ~infer:false var.import
        |> String.split_on_char '.' |> List.rev |> List.hd
    in
    if name = "" || name = "String" then []
    else
      let setter_list =
        (try SetterMap.M.find name s_map with _ -> [])
        |> List.filter (fun (s, fields) ->
               is_private s m_info |> not
               && (FieldSet.S.subset var.field fields
                  || Str.string_match (".*Array\\.set" |> Str.regexp) s 0))
      in
      List.fold_left
        (fun lst (s, _) ->
          let f_arg =
            mk_arg ~is_s:(is_s_method s m_info)
              (MethodInfo.M.find s m_info).MethodInfo.formal_params var.summary
          in
          ( AST.F
              {
                typ = name;
                method_name = s;
                import = var.import;
                summary = var.summary;
              },
            f_arg )
          :: lst)
        [] setter_list

let get_ret_obj (class_package, class_name) m_info (c_info, ig) s_map =
  let full_class_name =
    if class_package = "" then class_name else class_package
  in
  let class_to_find =
    try IG.succ ig full_class_name |> List.cons full_class_name
    with Invalid_argument _ -> [ full_class_name ]
  in
  MethodInfo.M.fold
    (fun method_name _ method_list ->
      List.fold_left
        (fun init_list class_name_to_find ->
          if
            match_return_object class_name_to_find method_name m_info
            && is_private method_name m_info |> not
            && is_init_method method_name |> not
            && is_void_method method_name s_map |> not
          then
            (method_name, get_package method_name m_info (c_info, ig))
            :: init_list
          else init_list)
        method_list class_to_find)
    m_info []

let modify_summary id t_summary a_summary =
  let new_value =
    Value.M.add
      (AST.org_symbol "size" a_summary)
      (Value.Ge (Int (get_array_size id t_summary)))
      a_summary.Language.value
  in
  let new_mem_summary old_summary memory =
    Language.
      {
        relation = old_summary.relation;
        value = old_summary.value;
        precond = (old_summary.precond |> fst, memory);
        postcond = (old_summary.postcond |> fst, memory);
        args = old_summary.args;
      }
  in
  let new_this_summary old_summary values =
    let this_symbol = Condition.RH_Symbol (AST.org_symbol "this" old_summary) in
    let new_premem =
      Condition.M.find this_symbol (old_summary.precond |> snd)
      |> Condition.M.add
           (Condition.RH_Index (values |> fst |> fst))
           (Condition.RH_Symbol (values |> snd |> fst))
    in
    let new_postmem =
      Condition.M.find this_symbol (old_summary.postcond |> snd)
      |> Condition.M.add
           (Condition.RH_Index (values |> fst |> fst))
           (Condition.RH_Symbol (values |> snd |> fst))
    in
    Language.
      {
        relation = old_summary.relation;
        value =
          Value.M.add
            (values |> fst |> fst)
            (values |> fst |> snd)
            old_summary.value
          |> Value.M.add (values |> snd |> fst) (values |> snd |> snd);
        precond =
          ( old_summary.precond |> fst,
            Condition.M.add this_symbol new_premem (old_summary.precond |> snd)
          );
        postcond =
          ( old_summary.postcond |> fst,
            Condition.M.add this_symbol new_postmem (old_summary.postcond |> snd)
          );
        args = old_summary.args;
      }
  in
  let rec mk_new_summary new_summary summary =
    let tmp = AST.get_array_index id summary in
    if tmp |> fst |> fst = "" then (new_summary, summary)
    else
      let new_mem = AST.remove_array_index id (tmp |> fst |> fst) summary in
      mk_new_summary
        (new_this_summary new_summary tmp)
        (new_mem_summary summary new_mem)
  in
  mk_new_summary (new_value_summary a_summary new_value) t_summary |> fst

let satisfied_c_list id t_summary summary summary_list =
  if !Cmdline.basic_mode then
    List.fold_left
      (fun list (constructor, import) ->
        (0, constructor, Language.empty_summary, import) :: list)
      [] summary_list
  else
    List.fold_left
      (fun list (constructor, import) ->
        let check, summary = satisfied_c t_summary id constructor summary in
        if check then
          if is_array_init constructor then
            (0, constructor, modify_summary id t_summary summary, import)
            :: list
          else (0, constructor, summary, import) :: list
        else (1000, constructor, summary, import) :: list)
      [] summary_list

let get_cfunc constructor m_info =
  let cost, c, s, i = constructor in
  let t =
    if is_init_method c then
      c
      |> Str.replace_first (Str.regexp ".<init>") ""
      |> Regexp.global_rm (Str.regexp "(.*)$")
    else c |> Str.split Regexp.dot |> List.hd
  in
  let func = AST.F { typ = t; method_name = c; import = i; summary = s } in
  let arg =
    mk_arg ~is_s:(is_s_method c m_info)
      (MethodInfo.M.find c m_info).MethodInfo.formal_params s
  in
  (cost, (func, AST.Arg arg))

let get_cfuncs list m_info =
  List.fold_left
    (fun lst (cost, c, s, i) -> get_cfunc (cost, c, s, i) m_info :: lst)
    [] list

let get_c ret summary _ m_info c_info =
  let class_name = AST.get_vinfo ret |> fst |> Language.get_class_name in
  if class_name = "" then []
  else
    let id = AST.get_vinfo ret |> snd in
    let package = (AST.get_v ret).import in
    let summary_filtering list =
      List.filter
        (fun (_, c, _, _) -> is_public_or_default c m_info c_info)
        list
      |> List.filter (fun (_, c, _, _) ->
             is_recursive_param class_name c m_info |> not)
    in
    let s_list =
      get_clist (package, class_name) m_info c_info
      |> satisfied_c_list id (AST.get_v ret).summary summary
      |> summary_filtering
    in
    get_cfuncs s_list m_info

let get_ret_c ret summary m_info c_info s_map =
  let class_name = AST.get_vinfo ret |> fst |> Language.get_class_name in
  if class_name = "" || class_name = "String" then []
  else
    let id = AST.get_vinfo ret |> snd in
    let package = (AST.get_v ret).import in
    let summary_filtering list =
      List.filter
        (fun (_, c, _, _) -> is_public_or_default c m_info c_info)
        list
      |> List.filter (fun (_, c, _, _) ->
             is_recursive_param class_name c m_info |> not)
    in
    let s_list =
      get_ret_obj (package, class_name) m_info c_info s_map
      |> satisfied_c_list id (AST.get_v ret).summary summary
      |> summary_filtering
    in
    get_cfuncs s_list m_info

let get_inner_func f arg =
  let fname =
    (AST.get_func f).method_name |> Str.split Regexp.dollar |> List.rev
    |> List.hd
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
  let recv = AST.get_arg arg |> List.hd in
  let n_recv =
    AST.Variable
      {
        import = recv.import;
        variable =
          ( Var
              ( Object
                  ((AST.get_func f).method_name
                  |> Regexp.first_rm (Str.regexp ("\\$" ^ fname))),
                "con_outer" ),
            Some !outer );
        field = FieldSet.S.empty;
        summary = recv.summary;
      }
  in
  (n_recv, n_f, AST.Arg (AST.get_arg arg |> List.tl))

let cname_condition m_name m_info =
  match MethodInfo.M.find_opt m_name m_info with
  | Some info ->
      (info.MethodInfo.return <> "" && is_s_method m_name m_info)
      || is_init_method m_name
  | _ -> is_init_method m_name

let get_cname f = AST.ClassName (AST.get_func f).AST.typ

let get_arg_seq (args : AST.id list) =
  List.fold_left
    (fun s arg ->
      let x =
        List.fold_left (fun lst x -> AST.mk_const_arg x arg :: lst) [] s
      in
      if is_primitive arg then x
      else
        x
        |> List.rev_append
             (List.fold_left (fun lst x -> AST.mk_assign_arg x arg :: lst) [] s))
    [ AST.Skip ] args

let rec unroll ~assign_ground (cost, p) summary cg m_info c_info s_map e_info =
  match p with
  | _ when assign_ground -> unroll_void (cost, p)
  | AST.Seq (s1, s2) when AST.assign_ground s1 |> not ->
      let lst =
        unroll ~assign_ground (cost, s1) summary cg m_info c_info s_map e_info
      in
      List.fold_left
        (fun lst x -> (x |> fst, AST.Seq (x |> snd, s2)) :: lst)
        [] lst
  | Seq (s1, s2) when AST.assign_ground s2 |> not ->
      let lst =
        unroll ~assign_ground (cost, s2) summary cg m_info c_info s_map e_info
      in
      List.fold_left
        (fun lst x -> (x |> fst, AST.Seq (s1, x |> snd)) :: lst)
        [] lst
  | Const (x, _) when AST.const p ->
      let typ, id = AST.get_vinfo x in
      if is_primitive x then
        List.fold_left
          (fun lst x1 ->
            (cost + (x1 |> fst), AST.const_rule1 p (x1 |> snd)) :: lst)
          []
          (get_value typ id (AST.get_v x).summary)
      else
        let r3 =
          List.fold_left
            (fun lst x1 ->
              match x1 |> snd with
              | AST.Primitive _ -> lst
              | _ -> (cost + (x1 |> fst), AST.const_rule3 p) :: lst)
            []
            (get_value typ id (AST.get_v x).summary)
        in
        let r2 =
          List.fold_left
            (fun lst x1 ->
              (cost + (x1 |> fst), AST.const_rule2 p (x1 |> snd)) :: lst)
            []
            (global_var_list
               (Language.get_class_name (AST.get_vinfo x |> fst))
               (AST.get_v x).summary summary m_info e_info)
        in
        if is_receiver (AST.get_vinfo x |> snd) then r2
        else List.rev_append r3 r2
  | Assign (x0, _, _, _) when AST.fcall_in_assign p ->
      let field_map = get_field_map x0 s_map in
      List.rev_append
        (get_c x0 summary cg m_info c_info)
        (get_ret_c x0 summary m_info c_info s_map)
      |> List.fold_left
           (fun lst (c, (f, arg)) ->
             (cost + c, AST.fcall_in_assign_rule p field_map f arg) :: lst)
           []
  | Void (x, _, _) when AST.fcall1_in_void p || AST.fcall2_in_void p ->
      let lst = get_void_func x m_info c_info s_map in
      if lst = [] then []
      else
        List.fold_left
          (fun lst (f, arg) ->
            (cost, AST.fcall_in_void_rule p f (AST.Arg arg)) :: lst)
          [] lst
  | Assign (_, _, f, arg) when AST.recv_in_assign p ->
      if
        is_nested_class (AST.get_func f).import
        && is_s_class (AST.get_func f).import c_info |> not
        && is_init_method (AST.get_func f).method_name
      then (
        let recv, f, arg = get_inner_func f arg in
        let r2 = AST.recv_in_assign_rule2_1 p recv f arg in
        let r3 = AST.recv_in_assign_rule3_1 p recv f arg in
        incr outer;
        (cost, r2) :: [ (cost, r3) ])
      else if cname_condition (AST.get_func f).method_name m_info then
        [ (cost, get_cname f |> AST.recv_in_assign_rule1 p) ]
      else
        let r2 = AST.recv_in_assign_rule2 p "con_recv" !recv in
        let r3 = AST.recv_in_assign_rule3 p "con_recv" !recv in
        incr recv;
        (cost, r2) :: [ (cost, r3) ]
  | Void (_, f, _) when AST.recv_in_void p ->
      if cname_condition (AST.get_func f).method_name m_info then
        [ (cost, get_cname f |> AST.recv_in_void_rule1 p) ]
      else
        let r2 = AST.recv_in_void_rule2 p "con_recv" !recv in
        let r3 = AST.recv_in_void_rule3 p "con_recv" !recv in
        incr recv;
        (cost, r2) :: [ (cost, r3) ]
  | Assign (_, _, _, arg) when AST.arg_in_assign p ->
      let arg_seq =
        get_arg_seq
          (List.fold_left
             (fun lst x -> AST.Variable x :: lst)
             [] (arg |> AST.get_arg))
      in
      List.fold_left
        (fun lst x ->
          (cost, AST.arg_in_assign_rule p x (AST.Param (arg |> AST.get_arg)))
          :: lst)
        [] arg_seq
  | Void (_, _, arg) when AST.arg_in_void p ->
      let arg_seq =
        get_arg_seq
          (List.fold_left
             (fun lst x -> AST.Variable x :: lst)
             [] (arg |> AST.get_arg))
      in
      List.fold_left
        (fun lst x ->
          (cost, AST.arg_in_void_rule p x (AST.Param (arg |> AST.get_arg)))
          :: lst)
        [] arg_seq
  | _ -> [ (cost, p) ]

and unroll_void (cost, p) =
  match p with
  | _ when AST.ground p -> [ (cost, p) ]
  | AST.Seq _ when AST.void p ->
      (cost, AST.void_rule1 p)
      :: List.fold_left (fun lst x -> (cost, x) :: lst) [] (AST.void_rule2 p)
  | Seq (s1, s2) ->
      let ns1, ns2 =
        match AST.last_code s1 with
        | AST.Assign _ when AST.is_stmt s2 ->
            (AST.modify_last_assign s1, AST.Seq (AST.last_code s1, s2))
        | _ -> (s1, s2)
      in
      List.fold_left
        (fun l x ->
          List.fold_left
            (fun l2 y ->
              (cost + (x |> fst) + (y |> fst), AST.Seq (x |> snd, y |> snd))
              :: l2)
            l
            (unroll_void (cost, ns2)))
        []
        (unroll_void (cost, ns1))
  | _ -> [ (cost, p) ]

(* find error entry *)
let rec find_ee e_method e_summary cg summary call_prop_map m_info c_info =
  let propagation caller_method caller_preconds call_prop =
    let new_value, new_mem, check_match =
      satisfy e_method e_summary call_prop m_info
    in
    if !Cmdline.basic_mode then
      ErrorEntrySet.union caller_preconds
        (find_ee caller_method Language.empty_summary cg summary call_prop_map
           m_info c_info)
    else if check_match then
      let new_call_prop =
        new_mem_summary (new_value_summary call_prop new_value) new_mem
      in
      ErrorEntrySet.union caller_preconds
        (find_ee caller_method new_call_prop cg summary call_prop_map m_info
           c_info)
    else caller_preconds
  in
  if is_public_or_default e_method m_info c_info then
    ErrorEntrySet.add (e_method, e_summary) ErrorEntrySet.empty
  else
    let caller_list = CG.succ cg e_method in
    List.fold_left
      (fun set caller_method ->
        let caller_prop_list =
          match
            CallPropMap.M.find_opt (caller_method, e_method) call_prop_map
          with
          | None ->
              (* It is possible without any specific conditions *)
              find_ee caller_method Language.empty_summary cg summary
                call_prop_map m_info c_info
          | Some prop_list ->
              List.fold_left
                (fun caller_preconds call_prop ->
                  propagation caller_method caller_preconds call_prop)
                ErrorEntrySet.empty prop_list
        in
        ErrorEntrySet.union set caller_prop_list)
      ErrorEntrySet.empty caller_list

let pretty_format p =
  let i_format i = Str.replace_first Regexp.dollar "." i in
  let rec imports s set =
    match s with
    | AST.Seq (s1, s2) -> imports s1 set |> imports s2
    | Const (x, _) -> ImportSet.add (AST.get_v x).import set
    | Assign (x0, _, f, arg) ->
        List.fold_left
          (fun s (a : AST.var) -> ImportSet.add a.import s)
          set (arg |> AST.get_param)
        |> ImportSet.add (AST.get_v x0).import
        |> ImportSet.add (AST.get_func f).import
    | Void (_, f, arg) ->
        List.fold_left
          (fun s (a : AST.var) -> ImportSet.add a.import s)
          set (arg |> AST.get_param)
        |> ImportSet.add (AST.get_func f).import
    | _ -> set
  in
  let import =
    ImportSet.fold
      (fun i s ->
        if i = "" || Str.string_match (Str.regexp ".*Array$") i 0 then s
        else s ^ "import " ^ (i |> i_format) ^ ";\n")
      (imports p ImportSet.empty)
      ""
  in
  let start = "\n@Test\npublic void unitcon_test() throws Exception {\n" in
  let code = start ^ AST.code p ^ "}\n\n" in
  (import, code)

let priority_q queue =
  List.sort
    (fun p1 p2 ->
      let s1 = get_cost p1 in
      let s2 = get_cost p2 in
      compare ((s1 |> fst) + (s1 |> snd)) ((s2 |> fst) + (s2 |> snd)))
    queue

let rec mk_testcase queue summary cg m_info c_info s_map e_info =
  let queue = if !Cmdline.basic_mode then queue else priority_q queue in
  match queue with
  | (cost, p) :: tl ->
      if AST.ground p then [ (pretty_format p, tl) ]
      else
        mk_testcase
          (List.rev_append
             (unroll ~assign_ground:(AST.assign_ground p) (cost, p) summary cg
                m_info c_info s_map e_info
             |> List.rev)
             tl)
          summary cg m_info c_info s_map e_info
  | [] -> []

let mk_testcases ~is_start pkg_name queue (e_method, error_summary)
    (cg, summary, call_prop_map, m_info, c_info, s_map, e_info) =
  let apply_rule list =
    List.fold_left
      (fun lst (f, arg) ->
        (0, AST.fcall_in_void_rule (AST.Void (Id, Func, Arg [])) f (AST.Arg arg))
        :: lst)
      [] list
  in
  let init =
    if is_start then (
      pkg := pkg_name;
      ErrorEntrySet.fold
        (fun (ee, ee_s) init_list ->
          apply_rule (get_void_func AST.Id ~ee ~es:ee_s m_info c_info s_map)
          |> List.rev_append init_list)
        (find_ee e_method error_summary cg summary call_prop_map m_info c_info)
        [])
    else queue
  in
  let result = mk_testcase init summary cg m_info c_info s_map e_info in
  if result = [] then (("", ""), []) else List.hd result
