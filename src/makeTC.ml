module Relation = Language.Relation
module Value = Language.Value
module Condition = Language.Condition
module MethodInfo = Language.MethodInfo
module SummaryMap = Language.SummaryMap
module CallPropMap = Language.CallPropMap
module ClassInfo = Language.ClassInfo
module SetterMap = Language.SetterMap
module FieldMap = Language.FieldMap
module CG = Callgraph.G
module HG = Hierarchy.G

(* defining for constructor priority *)
type new_bool = T | F | DM

module ImportSet = Set.Make (struct
  type t = string

  let compare = compare
end)

module CodeSet = Set.Make (struct
  type t = string

  let compare = compare
end)

let outer = ref 0

let tc_num = ref 0

let z3ctx =
  Z3.mk_context
    [
      ("model", "true");
      ("proof", "true");
      ("dump_models", "true");
      ("unsat_core", "true");
    ]

let solver = Z3.Solver.mk_solver z3ctx None

let rec find_relation given_symbol relation =
  match Relation.M.find_opt given_symbol relation with
  | Some find_symbol -> find_relation find_symbol relation
  | None -> given_symbol

let get_rh_name ~is_var rh =
  if is_var then match rh with Condition.RH_Var v -> v | _ -> ""
  else match rh with Condition.RH_Symbol s -> s | _ -> ""

let find_variable head_symbol variables =
  match Condition.M.find_opt (Condition.RH_Symbol head_symbol) variables with
  | Some var -> get_rh_name ~is_var:true var
  | None -> ""

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

let more_find_head_symbol head_symbol _ memory =
  let is_head_symbol _ value =
    match value with
    | Condition.RH_Symbol s when head_symbol = s -> true
    | _ -> false
  in
  Condition.M.exists is_head_symbol memory

let get_symbol_list values =
  Value.M.fold (fun symbol _ symbol_list -> symbol :: symbol_list) values []

(* memory: Condition.mem *)
(* return: (callee_actual_symbol * head_symbol) list *)
(* if head = "" then this symbol can be any value *)
let get_head_symbol_list symbols (_, memory) =
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
  in
  let get_head_symbol symbol memory =
    Condition.M.fold
      (fun head_symbol trace head_list ->
        let head =
          find_real_head (get_rh_name ~is_var:false head_symbol) memory
        in
        Condition.M.fold
          (fun _ trace_tail head_list ->
            match trace_tail with
            | Condition.RH_Symbol s when symbol = s -> [ (symbol, head) ]
            | _ -> head_list)
          trace head_list)
      memory []
  in
  List.map
    (fun symbol ->
      try get_head_symbol symbol memory |> List.hd with _ -> (symbol, ""))
    symbols

(* variables: Condition.var *)
(* return: (callee_actual_symbol * head_symbol * param_index) list *)
(* if param_index = -1 then this symbol can be any value *)
let get_param_index_list head_symbol_list (variables, _) formal_params =
  let get_param_index head_symbol variables formal_params =
    let variable = find_variable head_symbol variables in
    let index =
      let rec get_index count params =
        match params with
        | hd :: tl -> (
            match hd |> snd with
            | Language.This _ -> get_index (count + 1) tl
            | Var (_, id) ->
                if id = variable then count else get_index (count + 1) tl)
        | [] -> -1
      in
      get_index 0 formal_params
    in
    index
  in
  List.map
    (fun (symbol, head_symbol) ->
      if head_symbol = "" then (symbol, head_symbol, -1)
      else
        let index = get_param_index head_symbol variables formal_params in
        (symbol, head_symbol, index))
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

let get_value_symbol_list ~is_init t_summary c_summary vs_list =
  let vs_list =
    if is_init then
      (*this, this*)
      let t_symbol, c_symbol = vs_list |> List.hd in
      let t_var, t_mem = t_summary.Language.precond in
      let c_var, c_mem = c_summary.Language.precond in
      let compare_t_mem =
        Condition.M.find_opt (Condition.RH_Symbol t_symbol) t_var
      in
      let compare_c_mem =
        Condition.M.find_opt (Condition.RH_Symbol c_symbol) c_var
      in
      match (compare_t_mem, compare_c_mem) with
      | None, _ | _, None -> [ (t_symbol, c_symbol) ]
      | Some t_id, Some c_id -> (
          let t_symbol =
            get_tail_symbol
              (t_id |> get_rh_name ~is_var:true)
              (Condition.RH_Symbol t_symbol) t_mem
          in
          let c_symbol =
            get_tail_symbol
              (c_id |> get_rh_name ~is_var:true)
              (Condition.RH_Symbol c_symbol) c_mem
          in
          let compare_t_mem = Condition.M.find_opt t_symbol t_mem in
          let compare_c_mem = Condition.M.find_opt c_symbol c_mem in
          match (compare_t_mem, compare_c_mem) with
          | None, _ -> []
          | _, None -> []
          | Some t, Some c ->
              Condition.M.fold
                (fun key sym sym_list ->
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
                    get_tail_symbol field_name sym t_mem
                    |> get_rh_name ~is_var:false
                  in
                  let tail_c_symbol =
                    get_tail_symbol field_name c_sym c_mem
                    |> get_rh_name ~is_var:false
                  in
                  (tail_t_symbol, tail_c_symbol) :: sym_list)
                t [])
    else vs_list
  in
  vs_list

let check_intersect_value_list ~is_init caller_prop callee_summary vs_list =
  let check_intersect_value caller_symbol callee_symbol =
    try
      let caller_value =
        Value.M.find caller_symbol caller_prop.Language.value
      in
      let callee_value =
        Value.M.find callee_symbol callee_summary.Language.value
      in
      match (caller_value, callee_value) with
      | Eq eq_v1, Eq eq_v2 ->
          if eq_v1 = eq_v2 then (caller_prop.Language.value, T)
          else (caller_prop.Language.value, F)
      | Eq eq_v, Neq neq_v | Neq neq_v, Eq eq_v ->
          if eq_v = neq_v then (caller_prop.Language.value, F)
          else (caller_prop.Language.value, T)
      | Eq eq_v, Le le_v | Le le_v, Eq eq_v -> (
          match (eq_v, le_v) with
          | Int eq_i, Int le_i
          | Long eq_i, Long le_i
          | Int eq_i, Long le_i
          | Long eq_i, Int le_i ->
              if eq_i <= le_i then (caller_prop.Language.value, T)
              else (caller_prop.Language.value, F)
          | Float eq_f, Float le_f
          | Double eq_f, Double le_f
          | Float eq_f, Double le_f
          | Double eq_f, Float le_f ->
              if eq_f <= le_f then (caller_prop.Language.value, T)
              else (caller_prop.Language.value, F)
          | _ -> failwith "not allowed type in eq, le")
      | Eq eq_v, Lt lt_v | Lt lt_v, Eq eq_v -> (
          match (eq_v, lt_v) with
          | Int eq_i, Int lt_i
          | Long eq_i, Long lt_i
          | Int eq_i, Long lt_i
          | Long eq_i, Int lt_i ->
              if eq_i < lt_i then (caller_prop.Language.value, T)
              else (caller_prop.Language.value, F)
          | Float eq_f, Float lt_f
          | Double eq_f, Double lt_f
          | Float eq_f, Double lt_f
          | Double eq_f, Float lt_f ->
              if eq_f < lt_f then (caller_prop.Language.value, T)
              else (caller_prop.Language.value, F)
          | _ -> failwith "not allowed type in eq, lt")
      | Eq eq_v, Ge ge_v | Ge ge_v, Eq eq_v -> (
          match (eq_v, ge_v) with
          | Int eq_i, Int ge_i
          | Long eq_i, Long ge_i
          | Int eq_i, Long ge_i
          | Long eq_i, Int ge_i ->
              if eq_i >= ge_i then (caller_prop.Language.value, T)
              else (caller_prop.Language.value, F)
          | Float eq_f, Float ge_f
          | Double eq_f, Double ge_f
          | Float eq_f, Double ge_f
          | Double eq_f, Float ge_f ->
              if eq_f >= ge_f then (caller_prop.Language.value, T)
              else (caller_prop.Language.value, F)
          | _ -> failwith "not allowed type in eq, ge")
      | Eq eq_v, Gt gt_v | Gt gt_v, Eq eq_v -> (
          match (eq_v, gt_v) with
          | Int eq_i, Int gt_i
          | Long eq_i, Long gt_i
          | Int eq_i, Long gt_i
          | Long eq_i, Int gt_i ->
              if eq_i > gt_i then (caller_prop.Language.value, T)
              else (caller_prop.Language.value, F)
          | Float eq_f, Float gt_f
          | Double eq_f, Double gt_f
          | Float eq_f, Double gt_f
          | Double eq_f, Float gt_f ->
              if eq_f > gt_f then (caller_prop.Language.value, T)
              else (caller_prop.Language.value, F)
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
                (caller_prop.Language.value, T)
              else (caller_prop.Language.value, F)
          | Float eq_f, Float btw_min_f, Float btw_max_f
          | Float eq_f, Float btw_min_f, Double btw_max_f
          | Float eq_f, Double btw_min_f, Float btw_max_f
          | Float eq_f, Double btw_min_f, Double btw_max_f
          | Double eq_f, Float btw_min_f, Float btw_max_f
          | Double eq_f, Float btw_min_f, Double btw_max_f
          | Double eq_f, Double btw_min_f, Float btw_max_f
          | Double eq_f, Double btw_min_f, Double btw_max_f ->
              if eq_f >= btw_min_f && eq_f <= btw_max_f then
                (caller_prop.Language.value, T)
              else (caller_prop.Language.value, F)
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
                (caller_prop.Language.value, T)
              else (caller_prop.Language.value, F)
          | Float eq_f, Float o_min_f, Float o_max_f
          | Float eq_f, Float o_min_f, Double o_max_f
          | Float eq_f, Double o_min_f, Float o_max_f
          | Float eq_f, Double o_min_f, Double o_max_f
          | Double eq_f, Float o_min_f, Float o_max_f
          | Double eq_f, Float o_min_f, Double o_max_f
          | Double eq_f, Double o_min_f, Float o_max_f
          | Double eq_f, Double o_min_f, Double o_max_f ->
              if eq_f < o_min_f && eq_f > o_max_f then
                (caller_prop.Language.value, T)
              else (caller_prop.Language.value, F)
          | _ -> failwith "not allowed type in eq, outside")
      | Le le_v, Ge ge_v | Ge ge_v, Le le_v -> (
          match (le_v, ge_v) with
          | Int le_i, Int ge_i
          | Long le_i, Long ge_i
          | Int le_i, Long ge_i
          | Long le_i, Int ge_i ->
              if le_i >= ge_i then (caller_prop.Language.value, T)
              else (caller_prop.Language.value, F)
          | Float le_f, Float ge_f
          | Double le_f, Double ge_f
          | Float le_f, Double ge_f
          | Double le_f, Float ge_f ->
              if le_f >= ge_f then (caller_prop.Language.value, T)
              else (caller_prop.Language.value, F)
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
              if l_i > g_i then (caller_prop.Language.value, T)
              else (caller_prop.Language.value, F)
          | Float l_f, Float g_f
          | Double l_f, Double g_f
          | Float l_f, Double g_f
          | Double l_f, Float g_f ->
              if l_f > g_f then (caller_prop.Language.value, T)
              else (caller_prop.Language.value, F)
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
              if le_i < btw_min_i then (caller_prop.Language.value, F)
              else (caller_prop.Language.value, T)
          | Float le_f, Float btw_min_f, Float _
          | Float le_f, Float btw_min_f, Double _
          | Double le_f, Double btw_min_f, Float _
          | Double le_f, Double btw_min_f, Double _
          | Float le_f, Double btw_min_f, Float _
          | Float le_f, Double btw_min_f, Double _
          | Double le_f, Float btw_min_f, Float _
          | Double le_f, Float btw_min_f, Double _ ->
              if le_f < btw_min_f then (caller_prop.Language.value, F)
              else (caller_prop.Language.value, T)
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
              if lt_i <= btw_min_i then (caller_prop.Language.value, F)
              else (caller_prop.Language.value, T)
          | Float lt_f, Float btw_min_f, Float _
          | Float lt_f, Float btw_min_f, Double _
          | Double lt_f, Double btw_min_f, Float _
          | Double lt_f, Double btw_min_f, Double _
          | Float lt_f, Double btw_min_f, Float _
          | Float lt_f, Double btw_min_f, Double _
          | Double lt_f, Float btw_min_f, Float _
          | Double lt_f, Float btw_min_f, Double _ ->
              if lt_f <= btw_min_f then (caller_prop.Language.value, F)
              else (caller_prop.Language.value, T)
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
              if ge_i > btw_max_i then (caller_prop.Language.value, F)
              else (caller_prop.Language.value, T)
          | Float ge_f, Float _, Float btw_max_f
          | Float ge_f, Double _, Float btw_max_f
          | Double ge_f, Float _, Double btw_max_f
          | Double ge_f, Double _, Double btw_max_f
          | Float ge_f, Float _, Double btw_max_f
          | Float ge_f, Double _, Double btw_max_f
          | Double ge_f, Float _, Float btw_max_f
          | Double ge_f, Double _, Float btw_max_f ->
              if ge_f > btw_max_f then (caller_prop.Language.value, F)
              else (caller_prop.Language.value, T)
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
              if gt_i >= btw_max_i then (caller_prop.Language.value, F)
              else (caller_prop.Language.value, T)
          | Float gt_f, Float _, Float btw_max_f
          | Float gt_f, Double _, Float btw_max_f
          | Double gt_f, Float _, Double btw_max_f
          | Double gt_f, Double _, Double btw_max_f
          | Float gt_f, Float _, Double btw_max_f
          | Float gt_f, Double _, Double btw_max_f
          | Double gt_f, Float _, Float btw_max_f
          | Double gt_f, Double _, Float btw_max_f ->
              if gt_f >= btw_max_f then (caller_prop.Language.value, F)
              else (caller_prop.Language.value, T)
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
                (caller_prop.Language.value, F)
              else (caller_prop.Language.value, T)
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
                (caller_prop.Language.value, F)
              else (caller_prop.Language.value, T)
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
                (caller_prop.Language.value, F)
              else (caller_prop.Language.value, T)
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
                (caller_prop.Language.value, F)
              else (caller_prop.Language.value, T)
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
          (caller_prop.Language.value, T)
    with Not_found -> (
      try
        let callee_value =
          Value.M.find callee_symbol callee_summary.Language.value
        in
        (Value.M.add caller_symbol callee_value caller_prop.Language.value, DM)
      with Not_found -> (
        try
          (* constructor prop propagation *)
          let caller_value =
            Value.M.find caller_symbol caller_prop.Language.value
          in
          ( Value.M.add callee_symbol caller_value callee_summary.Language.value,
            DM )
        with Not_found -> (caller_prop.Language.value, DM)))
  in
  let vs_list =
    get_value_symbol_list ~is_init caller_prop callee_summary vs_list
  in
  List.map
    (fun (caller_symbol, callee_symbol) ->
      check_intersect_value caller_symbol callee_symbol)
    vs_list

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

let new_value_summary old_summary new_value =
  Language.
    {
      relation = old_summary.relation;
      value = new_value;
      precond = old_summary.precond;
      postcond = old_summary.postcond;
      args = old_summary.args;
    }

let match_precond callee_method callee_summary call_prop method_info =
  let callee_method_info = MethodInfo.M.find callee_method method_info in
  let callee_params = callee_method_info.MethodInfo.formal_params in
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
  let intersect_value =
    let values_and_check =
      check_intersect_value_list ~is_init:false call_prop callee_summary
        value_symbol_list
    in
    let values = combine_value call_prop.Language.value values_and_check in
    let check = List.filter (fun (_, c) -> c = F) values_and_check in
    (values, check)
  in
  let values, check = intersect_value in
  if check = [] then (values, true) else (values, false)

let is_public s_method method_info =
  let s_method_info = MethodInfo.M.find s_method method_info in
  match s_method_info.MethodInfo.modifier with Public -> true | _ -> false

let is_nested_class name = String.contains name '$'

let is_normal_class class_name class_info =
  (* let class_name = Str.global_replace (Str.regexp "\\.") "$" class_name in *)
  match ClassInfo.M.find_opt class_name class_info with
  | Some typ -> (
      match typ.ClassInfo.class_type with
      | Language.Static | Language.Normal -> true
      | _ -> false)
  | None -> false

let is_static_class ~is_class name (class_info, _) =
  let class_name =
    if is_class then name
    else
      Regexp.global_rm_exp (Str.regexp "\\.<.*>(.*)$") name
      |> Regexp.global_rm_exp (Str.regexp "(.*)$")
  in
  match ClassInfo.M.find_opt class_name class_info with
  | Some typ -> (
      match typ.ClassInfo.class_type with Language.Static -> true | _ -> false)
  | None -> false

let is_private_class class_package class_info =
  let c_info = ClassInfo.M.find_opt class_package (class_info |> fst) in
  match c_info with
  | Some info -> (
      let class_type = info.ClassInfo.class_type in
      match class_type with Language.Private -> true | _ -> false)
  | None -> false

let is_static_method method_name method_info =
  let m_info = MethodInfo.M.find method_name method_info in
  m_info.MethodInfo.is_static

let is_init_method method_name =
  Str.string_match (".*\\.<init>" |> Str.regexp) method_name 0

let is_private method_name method_info =
  let info = MethodInfo.M.find method_name method_info in
  match info.MethodInfo.modifier with Private -> true | _ -> false

let is_public_or_default ~is_getter recv_package method_name method_info =
  let info = MethodInfo.M.find method_name method_info in
  let m_package =
    List.fold_left
      (fun found (import, var) ->
        match var with Language.This _ -> import | _ -> found)
      "" info.MethodInfo.formal_params
  in
  if is_getter then
    match info.MethodInfo.modifier with Public -> true | _ -> false
  else if m_package = "" then false
  else
    let name =
      Str.split Regexp.dot m_package
      |> List.rev |> List.hd
      |> Str.global_replace Regexp.dollar "\\$"
    in
    let s = name ^ "$" in
    let m_package = Regexp.global_rm_exp (Str.regexp s) m_package in
    if recv_package = m_package then
      match info.MethodInfo.modifier with
      | Default | Public -> true
      | _ -> false
    else match info.MethodInfo.modifier with Public -> true | _ -> false

let is_recursive_param parent_class method_name method_info =
  let info = MethodInfo.M.find method_name method_info in
  let this = Language.Object parent_class in
  List.fold_left
    (fun check (_, var) ->
      match var with
      | Language.Var (typ, _) when typ = this -> true
      | _ -> check)
    false info.MethodInfo.formal_params

let rec find_ps_method s_method source_summary call_graph summary call_prop_map
    method_info =
  if is_public s_method method_info then [ (s_method, source_summary) ]
  else
    let caller_list = CG.succ call_graph s_method in
    List.fold_left
      (fun list caller_method ->
        let caller_prop_list =
          match
            CallPropMap.M.find_opt (caller_method, s_method) call_prop_map
          with
          | None ->
              (* It is possible without any specific conditions *)
              (caller_method, Language.empty_summary) :: list
          | Some prop_list ->
              List.fold_left
                (fun caller_preconds call_prop ->
                  let new_value, check_match =
                    match_precond s_method source_summary call_prop method_info
                  in
                  if check_match then
                    let new_call_prop = new_value_summary call_prop new_value in
                    List.rev_append caller_preconds
                      (find_ps_method caller_method new_call_prop call_graph
                         summary call_prop_map method_info)
                  else caller_preconds)
                [] prop_list
        in
        List.rev_append list caller_prop_list)
      [] caller_list

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
      mem ""
  in
  let values = summary.Language.value in
  let default_value =
    match typ with
    | Language.Int -> Value.Eq (Int (Random.int 100))
    | Language.Long -> Value.Eq (Long (Random.int 100))
    | Language.Float -> Value.Eq (Float (Random.float 100.0))
    | Language.Double -> Value.Eq (Double (Random.float 100.0))
    | Language.Bool -> Value.Eq (Bool false)
    | Language.Char -> Value.Eq (Char 'x')
    | Language.String -> Value.Eq (String String.empty)
    | _ -> Value.Eq Null
  in
  let find_value =
    Value.M.fold
      (fun symbol value find_value ->
        if symbol = target_variable then value else find_value)
      values default_value
  in
  let value =
    match find_value with
    | Value.Eq v -> (
        match v with
        | Int i | Long i ->
            let var = Z3.Arithmetic.Integer.mk_const_s z3ctx id in
            let value = Z3.Arithmetic.Integer.mk_numeral_i z3ctx i in
            let z3exp = Z3.Boolean.mk_eq z3ctx var value in
            calc_z3 var [ z3exp ]
        | Float f | Double f ->
            let var = Z3.Arithmetic.Real.mk_const_s z3ctx id in
            let value =
              Z3.Arithmetic.Real.mk_numeral_s z3ctx (f |> string_of_float)
            in
            let z3exp = Z3.Boolean.mk_eq z3ctx var value in
            calc_z3 var [ z3exp ]
        | Bool b -> b |> string_of_bool
        | Char c -> String.make 1 c
        | String s -> s
        | Null -> "null"
        | _ -> failwith "not implemented eq")
    | Value.Neq v -> (
        match v with
        | Int i | Long i ->
            let var = Z3.Arithmetic.Integer.mk_const_s z3ctx id in
            let value = Z3.Arithmetic.Integer.mk_numeral_i z3ctx i in
            let z3exp =
              Z3.Boolean.mk_eq z3ctx var value |> Z3.Boolean.mk_not z3ctx
            in
            calc_z3 var [ z3exp ]
        | Float f | Double f ->
            let var = Z3.Arithmetic.Real.mk_const_s z3ctx id in
            let value =
              Z3.Arithmetic.Real.mk_numeral_s z3ctx (f |> string_of_float)
            in
            let z3exp =
              Z3.Boolean.mk_eq z3ctx var value |> Z3.Boolean.mk_not z3ctx
            in
            calc_z3 var [ z3exp ]
        | Bool b -> b |> not |> string_of_bool
        | String s -> "not " ^ s
        | Null -> "not null"
        | _ -> failwith "not implemented neq")
    | Value.Le v -> (
        match v with
        | Int i | Long i ->
            let var = Z3.Arithmetic.Integer.mk_const_s z3ctx id in
            let value = Z3.Arithmetic.Integer.mk_numeral_i z3ctx i in
            let z3exp = Z3.Arithmetic.mk_le z3ctx var value in
            calc_z3 var [ z3exp ]
        | Float f | Double f ->
            let var = Z3.Arithmetic.Real.mk_const_s z3ctx id in
            let value =
              Z3.Arithmetic.Real.mk_numeral_s z3ctx (f |> string_of_float)
            in
            let z3exp = Z3.Arithmetic.mk_le z3ctx var value in
            calc_z3 var [ z3exp ]
        | _ -> failwith "not implemented le")
    | Value.Lt v -> (
        match v with
        | Int i | Long i ->
            let var = Z3.Arithmetic.Integer.mk_const_s z3ctx id in
            let value = Z3.Arithmetic.Integer.mk_numeral_i z3ctx i in
            let z3exp = Z3.Arithmetic.mk_lt z3ctx var value in
            calc_z3 var [ z3exp ]
        | Float f | Double f ->
            let var = Z3.Arithmetic.Real.mk_const_s z3ctx id in
            let value =
              Z3.Arithmetic.Real.mk_numeral_s z3ctx (f |> string_of_float)
            in
            let z3exp = Z3.Arithmetic.mk_lt z3ctx var value in
            calc_z3 var [ z3exp ]
        | _ -> failwith "not implemented lt")
    | Value.Ge v -> (
        match v with
        | Int i | Long i ->
            let var = Z3.Arithmetic.Integer.mk_const_s z3ctx id in
            let value = Z3.Arithmetic.Integer.mk_numeral_i z3ctx i in
            let z3exp = Z3.Arithmetic.mk_ge z3ctx var value in
            calc_z3 var [ z3exp ]
        | Float f | Double f ->
            let var = Z3.Arithmetic.Real.mk_const_s z3ctx id in
            let value =
              Z3.Arithmetic.Real.mk_numeral_s z3ctx (f |> string_of_float)
            in
            let z3exp = Z3.Arithmetic.mk_ge z3ctx var value in
            calc_z3 var [ z3exp ]
        | _ -> failwith "not implemented ge")
    | Value.Gt v -> (
        match v with
        | Int i | Long i ->
            let var = Z3.Arithmetic.Integer.mk_const_s z3ctx id in
            let value = Z3.Arithmetic.Integer.mk_numeral_i z3ctx i in
            let z3exp = Z3.Arithmetic.mk_gt z3ctx var value in
            calc_z3 var [ z3exp ]
        | Float f | Double f ->
            let var = Z3.Arithmetic.Real.mk_const_s z3ctx id in
            let value =
              Z3.Arithmetic.Real.mk_numeral_s z3ctx (f |> string_of_float)
            in
            let z3exp = Z3.Arithmetic.mk_gt z3ctx var value in
            calc_z3 var [ z3exp ]
        | _ -> failwith "not implemented gt")
    | Value.Between (v1, v2) -> (
        match (v1, v2) with
        | Int i1, Int i2 | Long i1, Long i2 | Int i1, Long i2 | Long i1, Int i2
          ->
            let var = Z3.Arithmetic.Integer.mk_const_s z3ctx id in
            let value1 = Z3.Arithmetic.Integer.mk_numeral_i z3ctx i1 in
            let value2 = Z3.Arithmetic.Integer.mk_numeral_i z3ctx i2 in
            let z3exp1 = Z3.Arithmetic.mk_ge z3ctx var value1 in
            let z3exp2 = Z3.Arithmetic.mk_le z3ctx var value2 in
            calc_z3 var [ z3exp1; z3exp2 ]
        | Float f1, Float f2
        | Double f1, Double f2
        | Float f1, Double f2
        | Double f1, Float f2 ->
            let var = Z3.Arithmetic.Real.mk_const_s z3ctx id in
            let value1 =
              Z3.Arithmetic.Real.mk_numeral_s z3ctx (f1 |> string_of_float)
            in
            let value2 =
              Z3.Arithmetic.Real.mk_numeral_s z3ctx (f2 |> string_of_float)
            in
            let z3exp1 = Z3.Arithmetic.mk_ge z3ctx var value1 in
            let z3exp2 = Z3.Arithmetic.mk_le z3ctx var value2 in

            calc_z3 var [ z3exp1; z3exp2 ]
        | _ -> failwith "not implemented between")
    | Value.Outside (v1, v2) -> (
        match (v1, v2) with
        | Int i1, Int i2 | Long i1, Long i2 | Int i1, Long i2 | Long i1, Int i2
          ->
            let var = Z3.Arithmetic.Integer.mk_const_s z3ctx id in
            let value1 = Z3.Arithmetic.Integer.mk_numeral_i z3ctx i1 in
            let value2 = Z3.Arithmetic.Integer.mk_numeral_i z3ctx i2 in
            let z3exp1 = Z3.Arithmetic.mk_lt z3ctx var value1 in
            let z3exp2 = Z3.Arithmetic.mk_gt z3ctx var value2 in
            calc_z3 var [ z3exp1; z3exp2 ]
        | Float f1, Float f2
        | Double f1, Double f2
        | Float f1, Double f2
        | Double f1, Float f2 ->
            let var = Z3.Arithmetic.Real.mk_const_s z3ctx id in
            let value1 =
              Z3.Arithmetic.Real.mk_numeral_s z3ctx (f1 |> string_of_float)
            in
            let value2 =
              Z3.Arithmetic.Real.mk_numeral_s z3ctx (f2 |> string_of_float)
            in
            let z3exp1 = Z3.Arithmetic.mk_lt z3ctx var value1 in
            let z3exp2 = Z3.Arithmetic.mk_gt z3ctx var value2 in
            calc_z3 var [ z3exp1; z3exp2 ]
        | _ -> failwith "not implemented outside")
  in
  value

let get_field_value_map field_name value_map field_map value memory =
  Condition.M.fold
    (fun _ symbol old_field_map ->
      let field_symbol = get_tail_symbol field_name symbol memory in
      let field_value =
        Value.M.find (field_symbol |> get_rh_name ~is_var:false) value
      in
      FieldMap.M.add field_name field_value old_field_map)
    value_map field_map

let rec collect_field m_symbol c_symbol m_value c_value m_mem c_mem field_map =
  try
    let next_m_symbol = Condition.M.find m_symbol m_mem in
    let next_c_symbol = Condition.M.find c_symbol c_mem in
    let is_m_field =
      if Condition.M.cardinal next_m_symbol > 1 then true else false
    in
    let is_c_field =
      if Condition.M.cardinal next_c_symbol > 1 then true else false
    in
    match (is_m_field, is_c_field) with
    | false, false ->
        let m = Condition.M.find Condition.RH_Any next_m_symbol in
        let c = Condition.M.find Condition.RH_Any next_c_symbol in
        collect_field m c m_value c_value m_mem c_mem field_map
    | true, false ->
        let field_name, field_symbol =
          Condition.M.fold
            (fun field symbol field_symbol ->
              match field with
              | Condition.RH_Var v -> (v, symbol)
              | _ -> field_symbol)
            next_m_symbol ("", Condition.RH_Any)
        in
        let next_m_symbol = Condition.M.find field_symbol m_mem in
        get_field_value_map field_name next_m_symbol field_map m_value m_mem
    | false, true -> field_map
    | true, true ->
        let m_field_name, m_field_symbol =
          Condition.M.fold
            (fun field symbol field_symbol ->
              match field with
              | Condition.RH_Var v -> (v, symbol)
              | _ -> field_symbol)
            next_m_symbol ("", Condition.RH_Any)
        in
        let next_m_symbol = Condition.M.find m_field_symbol m_mem in
        let c_field_name, c_field_symbol =
          Condition.M.fold
            (fun field symbol field_symbol ->
              match field with
              | Condition.RH_Var v when v = m_field_name -> (v, symbol)
              | _ -> field_symbol)
            next_c_symbol ("", Condition.RH_Any)
        in
        let next_c_symbol = Condition.M.find c_field_symbol c_mem in
        let m_field_map =
          get_field_value_map m_field_name next_m_symbol FieldMap.M.empty
            m_value m_mem
        in
        let c_field_map =
          get_field_value_map c_field_name next_c_symbol FieldMap.M.empty
            c_value c_mem
        in
        FieldMap.M.fold
          (fun field m_value old_field_map ->
            let c_value = FieldMap.M.find_opt field c_field_map in
            match c_value with
            | Some value when value = m_value -> old_field_map
            | _ -> FieldMap.M.add field m_value old_field_map)
          m_field_map field_map
  with _ -> field_map

let get_class_name ~infer method_name =
  if infer then Regexp.global_rm_exp ("\\..+(.*)" |> Str.regexp) method_name
  else Regexp.global_rm_exp ("(.*)" |> Str.regexp) method_name

let get_setter_list constructor field_map method_info setter_map =
  let class_name = get_class_name ~infer:false constructor in
  let setter_list = try SetterMap.M.find class_name setter_map with _ -> [] in
  let rec find_then_remove_field setter_list field_map =
    match setter_list with
    | (method_name, change_field) :: tl ->
        let check =
          List.fold_left
            (fun check field ->
              match FieldMap.M.find_opt field field_map with
              | None -> false
              | _ -> check)
            true change_field
        in
        if check then
          let field_map =
            List.fold_left
              (fun old_field_map field -> FieldMap.M.remove field old_field_map)
              field_map change_field
          in
          find_then_remove_field tl field_map |> List.cons method_name
        else find_then_remove_field tl field_map
    | _ -> []
  in
  let rec all_setter setter_list =
    match setter_list with
    | (method_name, _) :: tl -> all_setter tl |> List.cons method_name
    | _ -> []
  in
  all_setter setter_list
  |> List.filter (fun setter -> is_private setter method_info |> not)
(* find_then_remove_field setter_list field_map
   |> List.filter (fun setter -> is_private setter method_info |> not) *)

let get_setter constructor id method_summary constructor_summary method_info
    setter_map =
  if constructor_summary = Language.empty_summary then
    ( FieldMap.M.empty,
      get_setter_list constructor FieldMap.M.empty method_info setter_map )
  else
    let m_pre_var, m_pre_mem = method_summary.Language.precond in
    let m_pre_value = method_summary.Language.value in
    let c_post_var, c_post_mem = constructor_summary.Language.postcond in
    let c_post_value = constructor_summary.Language.value in
    let m_id_symbol = get_id_symbol id m_pre_var m_pre_mem in
    let c_this_symbol = get_id_symbol "this" c_post_var c_post_mem in
    (* need_setter_field:
       The setter field map that must be met.
       This value is got from the method summary.*)
    let need_setter_field =
      collect_field m_id_symbol c_this_symbol m_pre_value c_post_value m_pre_mem
        c_post_mem FieldMap.M.empty
    in
    ( need_setter_field,
      get_setter_list constructor need_setter_field method_info setter_map )

let check_correct_constructor method_summary id candidate_constructor summary =
  let constructor_summarys = SummaryMap.M.find candidate_constructor summary in
  let method_symbols, method_memory = method_summary.Language.precond in
  let id = if id = "gen1" then "this" else id in
  let target_symbol =
    get_id_symbol id method_symbols method_memory |> get_rh_name ~is_var:false
  in
  if target_symbol = "" then (true, constructor_summarys |> List.hd, 0)
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
          ( check_intersect_value_list ~is_init:true method_summary c_summary
              [ (target_symbol, c_target_symbol) ],
            c_summary ))
        constructor_summarys
    in
    List.fold_left
      (fun check_value (check_summary, c_summary) ->
        let check = List.filter (fun (_, c) -> c = F) check_summary in
        let t_count =
          List.filter (fun (_, c) -> c = T) check_summary |> List.length
        in
        let new_values = combine_value c_summary.Language.value check_summary in
        let new_c_summary = new_value_summary c_summary new_values in
        if check = [] then (true, new_c_summary, t_count) else check_value)
      (false, Language.empty_summary, 0)
      check_summarys

let remove_same_name c_list =
  let get_same_one target list =
    List.filter
      (fun (c_name, _, _) ->
        let class_name = get_class_name ~infer:true c_name in
        target = class_name)
      list
    |> List.hd
  in
  List.fold_left
    (fun new_list (c, _, _) ->
      let name = get_class_name ~infer:true c in
      let one = get_same_one name c_list in
      if List.mem one new_list then new_list else one :: new_list)
    [] c_list
  |> List.rev

let get_recv_package t_method (class_info, _) =
  let class_name = get_class_name ~infer:true t_method in
  let full_class_name =
    ClassInfo.M.fold
      (fun full_name _ find_name ->
        let name = Str.split Regexp.dot full_name |> List.rev |> List.hd in
        if class_name = name then
          let name = Str.global_replace Regexp.dollar "\\$" name in
          let s = name ^ "$" in
          Regexp.global_rm_exp (Str.regexp s) full_name
        else find_name)
      class_info ""
  in
  full_class_name

let match_constructor_name class_name method_name =
  let class_name = Str.split Regexp.dot class_name |> List.rev |> List.hd in
  let class_name = Str.global_replace Regexp.dollar "\\$" class_name in
  Str.string_match (class_name ^ "\\.<init>" |> Str.regexp) method_name 0

let match_return_object class_name method_name method_info =
  let class_name = Str.split Regexp.dot class_name |> List.rev |> List.hd in
  let info = MethodInfo.M.find method_name method_info in
  let return = info.MethodInfo.return in
  Str.string_match (Str.regexp class_name) return 0

let is_java_io_class class_name =
  if class_name = "PrintStream" || class_name = "InputStream" then true
  else false

let is_file_class class_name = if class_name = "File" then true else false

let is_class_class class_name = if class_name = "Class" then true else false

let is_graphics_class class_name =
  if Str.string_match ("Graphics" ^ "[0-9]*" |> Str.regexp) class_name 0 then
    true
  else false

let file_code = "File gen_file = new File(\"unitgen_file\");\n"

let create_file_code file_name = file_name ^ ".createNewFile();\n"

let image_code =
  "BufferedImage gen_image = new BufferedImage(100, 100, \
   BufferedImage.TYPE_INT_RGB);\n"

let create_graphics_code graphics_name = graphics_name ^ ".createGraphics();\n"

let class_code = "Object gen_obj = new Object();\n"

let get_class_code obj_name = obj_name ^ ".getClass();\n"

let get_java_package_normal_class class_name =
  let import_array_list = "java.util.ArrayList" in
  let import_hash_map = "java.util.HashMap" in
  let import_file = "java.io.File" in
  let import_input = "java.io.FileInputStream" in
  if class_name = "Collection" || class_name = "List" then
    ("ArrayList", [ import_array_list ])
  else if class_name = "Map" || class_name = "HashMap" then
    ("HashMap", [ import_hash_map ])
  else if class_name = "Object" then ("Object", [])
  else if class_name = "File" then ("File(\"unitgen_file\")", [ import_file ])
  else if class_name = "PrintStream" then
    ("PrintStream(gen_file)", [ import_file ])
  else if class_name = "InputStream" then
    ("FileInputStream(gen_file)", [ import_file; import_input ])
  else ("null", [])

let get_constructor_list (class_package, class_name) method_info
    (class_info, hierarchy_graph) =
  let full_class_name =
    if class_package = "" then class_name else class_package
  in
  let class_to_find =
    try HG.succ hierarchy_graph full_class_name |> List.cons full_class_name
    with Invalid_argument _ -> [ full_class_name ]
  in
  MethodInfo.M.fold
    (fun method_name _ method_list ->
      List.fold_left
        (fun init_list class_name_to_find ->
          if
            is_normal_class class_name_to_find class_info
            && is_private method_name method_info |> not
            && match_constructor_name class_name_to_find method_name
          then method_name :: init_list
          else init_list)
        method_list class_to_find)
    method_info []

let get_class_initializer_list class_name target_summary method_info =
  let variables, mem = target_summary.Language.precond in
  let target_variable =
    Condition.M.fold
      (fun symbol variable find_variable ->
        let symbol = get_rh_name ~is_var:false symbol in
        match variable with
        | Condition.RH_Var var ->
            if Str.string_match (".*\\." ^ class_name |> Str.regexp) var 0 then
              symbol
            else find_variable
        | _ -> find_variable)
      variables ""
  in
  let target_variable =
    Condition.M.fold
      (fun symbol symbol_trace find_variable ->
        let symbol = get_rh_name ~is_var:false symbol in
        if symbol = target_variable then
          Condition.M.fold
            (fun trace_head _ trace_find_var ->
              match trace_head with
              | Condition.RH_Var var -> var
              | _ -> trace_find_var)
            symbol_trace find_variable
        else find_variable)
      mem ""
  in
  MethodInfo.M.fold
    (fun init_name _ find_init ->
      if Str.string_match (class_name ^ "\\.<clinit>" |> Str.regexp) init_name 0
      then
        Condition.M.fold
          (fun _ symbol_trace find_init ->
            Condition.M.fold
              (fun trace_head _ trace_find_init ->
                match trace_head with
                | Condition.RH_Var var when var = target_variable ->
                    class_name ^ "." ^ var
                | _ -> trace_find_init)
              symbol_trace find_init)
          mem ""
      else find_init)
    method_info ""

let rec get_array_type typ =
  match typ with
  | Language.Int -> "int"
  | Long -> "long"
  | Float -> "float"
  | Double -> "double"
  | Bool -> "boolean"
  | Char -> "char"
  | String -> "String"
  | Object name -> name
  | Array typ -> get_array_type typ ^ "[]"
  | _ -> failwith "not allowed type"

let get_array_constructor typ size =
  match typ with
  | Language.Int -> "int"
  | Long -> "long"
  | Float -> "float"
  | Double -> "double"
  | Bool -> "boolean"
  | Char -> "char"
  | String -> "String"
  | Object name -> name
  | Array typ -> get_array_type typ ^ "[" ^ (size |> string_of_int) ^ "]"
  | _ -> failwith "not allowed type"

let sort_constructor_list constructor_list method_info =
  List.sort
    (fun (c1, _, k1) (c2, _, k2) ->
      if compare k1 k2 <> 0 then compare k2 k1
      else
        let c1_info = MethodInfo.M.find c1 method_info in
        let c1_formal = c1_info.MethodInfo.formal_params |> List.length in
        let c2_info = MethodInfo.M.find c2 method_info in
        let c2_formal = c2_info.MethodInfo.formal_params |> List.length in
        compare c1_formal c2_formal)
    constructor_list

let replace_nested_symbol str = Str.global_replace Regexp.dollar "." str

let replace_null id old_code =
  let candidate =
    [
      ("(" ^ id ^ ")", "(null)");
      ("(" ^ id ^ ", ", "(null, ");
      (", " ^ id ^ ",", ", null,");
      (", " ^ id ^ ")", ", null)");
    ]
  in
  List.fold_left
    (fun modified_code (c, rc) ->
      let mc = Str.replace_first (c |> Str.regexp) rc old_code in
      if mc <> old_code then mc else modified_code)
    old_code candidate

let this_is_null summary =
  let s_var, s_mem = summary.Language.precond in
  let this_symbol = get_id_symbol "this" s_var s_mem in
  let find_this_value =
    Value.M.find_opt
      (this_symbol |> get_rh_name ~is_var:false)
      summary.Language.value
  in
  match find_this_value with
  | Some value -> (
      match value with
      | Eq e_val -> ( match e_val with Null -> true | _ -> false)
      | _ -> false)
  | None -> false

let get_constructor_import constructor_info =
  let rec nested_import constructor_import =
    if String.contains constructor_import '$' then
      let new_import =
        Str.replace_first ("\\$.*" |> Str.regexp) "" constructor_import
      in
      let next_constructor_import =
        Str.replace_first Regexp.dollar "." constructor_import
      in
      nested_import next_constructor_import |> List.cons new_import
    else [ constructor_import ]
  in
  let constructor_import =
    List.fold_left
      (fun this_import param ->
        match param with import, Language.This _ -> import | _ -> this_import)
      "" constructor_info.MethodInfo.formal_params
  in
  nested_import constructor_import

let get_static_constructor t_method class_info =
  let class_name = get_class_name ~infer:true t_method in
  let full_class_name =
    ClassInfo.M.fold
      (fun full_name _ find_name ->
        let name = Str.split Regexp.dot full_name |> List.rev |> List.hd in
        if class_name = name then full_name else find_name)
      class_info ""
  in
  (class_name, full_class_name)

let get_init_constructor t_method method_info =
  let class_name = get_class_name ~infer:true t_method in
  let c_info = MethodInfo.M.find t_method method_info in
  let constructor_import =
    List.fold_left
      (fun this_import param ->
        match param with import, Language.This _ -> import | _ -> this_import)
      "" c_info.MethodInfo.formal_params
  in
  (class_name, constructor_import)

let mk_setter_format setter method_info =
  let m_info = MethodInfo.M.find setter method_info in
  let formal_params = m_info.MethodInfo.formal_params in
  let setter_statement =
    let param_list =
      List.fold_left
        (fun param_code (_, param) ->
          match param with
          | Language.This _ -> param_code
          | Language.Var (_, id) -> param_code ^ ", " ^ id)
        "" formal_params
    in
    let param_list = Regexp.global_rm_exp Regexp.start_bm2 param_list in
    let setter_statement =
      Str.split Regexp.dot setter
      |> List.tl |> List.hd
      |> Regexp.global_rm_exp (Str.regexp "(.*)$")
    in
    setter_statement ^ "(" ^ param_list ^ ")"
  in
  (setter_statement, formal_params)

let get_setter_code constructor id method_summary constructor_summary
    method_info setter_map =
  let met_field_map, setter_list =
    get_setter constructor id method_summary constructor_summary method_info
      setter_map
  in
  let met_value_map =
    FieldMap.M.fold
      (fun s value map -> Value.M.add s value map)
      met_field_map Value.M.empty
  in
  let new_summary = new_value_summary constructor_summary met_value_map in
  let iter_params params =
    List.fold_left
      (fun list (import, var) ->
        match var with
        | Language.This _ -> list
        | _ -> ((import, var), new_summary) :: list)
      [] params
  in
  List.fold_left
    (fun list setter ->
      let statement, params = mk_setter_format setter method_info in
      let statement = id ^ "." ^ statement ^ ";\n" in
      let new_mk_var_list = iter_params params in
      (statement, new_mk_var_list) :: list)
    [] setter_list

(* statement data structure: code * import * mk_var_list *)
let get_defined_statement class_package class_name id target_summary method_info
    setter_map old_code old_import old_var_list =
  let class_initializer =
    get_class_initializer_list class_name target_summary method_info
  in
  let class_name = class_name |> replace_nested_symbol in
  if class_initializer = "" then
    let normal_class_name, import = get_java_package_normal_class class_name in
    if is_java_io_class class_name then
      [
        ( file_code
          ^ create_file_code "gen_file"
          ^ class_name ^ " " ^ id ^ " = new " ^ normal_class_name ^ ";\n"
          ^ old_code,
          import |> List.rev_append old_import,
          old_var_list );
      ]
    else if is_file_class class_name then
      [
        ( class_name ^ " " ^ id ^ " = new " ^ normal_class_name ^ ";\n"
          ^ create_file_code id ^ old_code,
          import |> List.rev_append old_import,
          old_var_list );
      ]
    else if is_class_class class_name then
      [
        ( class_code ^ class_name ^ " " ^ id ^ " = " ^ get_class_code "gen_obj"
          ^ old_code,
          import |> List.rev_append old_import,
          old_var_list );
      ]
    else if is_graphics_class class_name then
      [
        ( image_code ^ class_name ^ " " ^ id ^ " = "
          ^ create_graphics_code "gen_image"
          ^ old_code,
          [ "java.awt.image.BufferedImage"; class_package ]
          |> List.rev_append old_import,
          old_var_list );
      ]
    else if normal_class_name = "null" then
      let old_code = replace_null id old_code in
      [ (old_code, old_import, old_var_list) ]
    else
      let setter_code_list =
        get_setter_code normal_class_name id target_summary
          Language.empty_summary method_info setter_map
      in
      List.fold_left
        (fun list (setter, var_list) ->
          ( class_name ^ " " ^ id ^ " = new " ^ normal_class_name ^ "();\n"
            ^ setter ^ old_code,
            import |> List.rev_append old_import,
            List.rev_append var_list old_var_list )
          :: list)
        [
          ( class_name ^ " " ^ id ^ " = null;\n" ^ old_code,
            old_import,
            old_var_list );
          ( class_name ^ " " ^ id ^ " = new " ^ normal_class_name ^ "();\n"
            ^ old_code,
            import |> List.rev_append old_import,
            old_var_list );
        ]
        setter_code_list
  else
    [
      ( class_name ^ " " ^ id ^ " = " ^ class_initializer ^ ";\n" ^ old_code,
        old_import |> List.cons class_package,
        old_var_list );
    ]

let get_return_object (class_package, class_name) method_info
    (_, hierarchy_graph) =
  let full_class_name =
    if class_package = "" then class_name else class_package
  in
  let class_to_find =
    try HG.succ hierarchy_graph full_class_name |> List.cons full_class_name
    with Invalid_argument _ -> [ full_class_name ]
  in
  MethodInfo.M.fold
    (fun method_name _ method_list ->
      List.fold_left
        (fun init_list class_name_to_find ->
          if
            is_static_method method_name method_info
            && match_return_object class_name_to_find method_name method_info
          then method_name :: init_list
          else init_list)
        method_list class_to_find)
    method_info []

let get_one_constructor ~is_getter ~origin_private constructor class_package
    class_name id target_summary method_info class_info setter_map old_code
    old_import old_var_list =
  if constructor |> fst = "null" then
    let old_code = replace_null id old_code in
    [ (old_code, old_import, old_var_list) ]
  else
    let constr_statement = constructor |> fst in
    let class_name =
      if origin_private then
        constr_statement |> replace_nested_symbol
        |> Str.replace_first (Str.regexp ".<init>") ""
        |> Regexp.global_rm_exp (Str.regexp "(.*)$")
      else class_name
    in
    let constructor_info = MethodInfo.M.find constr_statement method_info in
    let constructor_params = constructor_info.MethodInfo.formal_params in
    let constr_class_name =
      List.fold_left
        (fun find (import, param) ->
          match param with Language.This _ -> import | _ -> find)
        "" constructor_params
    in
    let constructor_summary = constructor |> snd in
    let setter_code_list =
      get_setter_code class_name id target_summary constructor_summary
        method_info setter_map
    in
    let constr_statement =
      let param_list =
        List.fold_left
          (fun param_code (_, param) ->
            match param with
            | Language.This _ -> param_code
            | Language.Var (_, id) -> param_code ^ ", " ^ id)
          "" constructor_params
      in
      let param_list = Regexp.global_rm_exp Regexp.start_bm2 param_list in
      let constr_statement =
        Str.replace_first (Str.regexp ".<init>") "" constr_statement
        |> Regexp.global_rm_exp (Str.regexp "(.*)$")
      in
      constr_statement ^ "(" ^ param_list ^ ")"
    in
    let constructor_import = get_constructor_import constructor_info in
    let constr_statement =
      if
        is_nested_class constr_class_name
        && is_static_class ~is_class:true constr_class_name class_info
      then replace_nested_symbol constr_statement
      else constr_statement
    in
    if this_is_null constructor_summary then
      let code = class_name ^ " " ^ id ^ " = null;\n" in
      let import =
        if origin_private then constructor_import |> List.rev_append old_import
        else
          constructor_import |> List.cons class_package
          |> List.rev_append old_import
      in
      [ (code ^ old_code, import, old_var_list) ]
    else if List.length constructor_params = 1 then
      let constr_statement = constr_statement |> replace_nested_symbol in
      let code =
        if is_getter then
          class_name ^ " " ^ id ^ " = " ^ constr_statement ^ ";\n"
        else class_name ^ " " ^ id ^ " = new " ^ constr_statement ^ ";\n"
      in
      let import =
        if origin_private then constructor_import |> List.rev_append old_import
        else
          constructor_import |> List.cons class_package
          |> List.rev_append old_import
      in
      List.fold_left
        (fun list (setter, var_list) ->
          ( code ^ setter ^ old_code,
            import,
            List.rev_append var_list old_var_list )
          :: list)
        [ (code ^ old_code, import, old_var_list) ]
        setter_code_list
    else if
      is_nested_class constr_class_name
      && is_static_class ~is_class:true constr_class_name class_info |> not
    then
      let constr_statement, constructor_params =
        let this = List.hd constructor_params in
        let outer_import, outer_var = List.tl constructor_params |> List.hd in
        let constr_statement, outer =
          match outer_var with
          | Language.Var (typ, id) ->
              let constr_statement =
                Str.replace_first (Str.regexp_string id) "" constr_statement
                |> Str.replace_first (Str.regexp "(, ") "("
                |> Str.replace_first (Str.regexp "^.*\\$") ""
              in
              outer := !outer + 1;
              ( constr_statement,
                ( outer_import,
                  Language.Var (typ, "outer" ^ (!outer |> string_of_int)) ) )
          | _ -> ("", (outer_import, outer_var))
        in
        let params_tl = List.tl constructor_params |> List.tl in
        (constr_statement, params_tl |> List.cons outer |> List.cons this)
      in
      let code =
        (class_name |> replace_nested_symbol)
        ^ " " ^ id ^ " = outer" ^ (!outer |> string_of_int) ^ ".new "
        ^ constr_statement ^ ";\n"
      in
      let import =
        if origin_private then constructor_import |> List.rev_append old_import
        else
          constructor_import |> List.cons class_package
          |> List.rev_append old_import
      in
      let constructor_params =
        constructor_params |> List.tl
        |> List.map (fun p -> (p, constructor_summary))
      in
      List.fold_left
        (fun list (setter, var_list) ->
          ( code ^ setter ^ old_code,
            import,
            List.rev_append constructor_params old_var_list
            |> List.rev_append var_list )
          :: list)
        [
          ( code ^ old_code,
            import,
            constructor_params |> List.rev_append old_var_list );
        ]
        setter_code_list
    else if
      is_nested_class constr_class_name
      && is_static_class ~is_class:true constr_class_name class_info
    then
      let constr_statement, constructor_params =
        let this = List.hd constructor_params in
        let params_tl = List.tl constructor_params in
        (constr_statement, params_tl |> List.cons this)
      in
      let code =
        if is_getter then
          (class_name |> replace_nested_symbol)
          ^ " " ^ id ^ " = " ^ constr_statement ^ ";\n"
        else
          (class_name |> replace_nested_symbol)
          ^ " " ^ id ^ " = new " ^ constr_statement ^ ";\n"
      in
      let import =
        if origin_private then constructor_import |> List.rev_append old_import
        else
          constructor_import |> List.cons class_package
          |> List.rev_append old_import
      in
      let constructor_params =
        constructor_params |> List.tl
        |> List.map (fun p -> (p, constructor_summary))
      in
      List.fold_left
        (fun list (setter, var_list) ->
          ( code ^ setter ^ old_code,
            import,
            List.rev_append constructor_params old_var_list
            |> List.rev_append var_list )
          :: list)
        [
          ( code ^ old_code,
            import,
            constructor_params |> List.rev_append old_var_list );
        ]
        setter_code_list
    else
      let code =
        if is_getter then
          class_name ^ " " ^ id ^ " = " ^ constr_statement ^ ";\n"
        else class_name ^ " " ^ id ^ " = new " ^ constr_statement ^ ";\n"
      in
      let import =
        if origin_private then constructor_import |> List.rev_append old_import
        else
          constructor_import |> List.cons class_package
          |> List.rev_append old_import
      in
      let constructor_params =
        if is_getter then
          constructor_params |> List.map (fun p -> (p, constructor_summary))
        else
          constructor_params |> List.tl
          |> List.map (fun p -> (p, constructor_summary))
      in
      List.fold_left
        (fun list (setter, var_list) ->
          ( code ^ setter ^ old_code,
            import,
            List.rev_append constructor_params old_var_list
            |> List.rev_append var_list )
          :: list)
        [
          ( code ^ old_code,
            import,
            constructor_params |> List.rev_append old_var_list );
        ]
        setter_code_list

let get_many_constructor ~is_getter constr_summary_list class_package class_name
    id target_summary method_info class_info setter_map code import var_list =
  let constructor_list =
    sort_constructor_list constr_summary_list method_info
  in
  let constructor_list =
    if Str.string_match (Str.regexp "gen") id 0 then constructor_list
    else ("null", Language.empty_summary, 0) :: constructor_list
  in
  let is_origin_private = is_private_class class_package class_info in
  List.fold_left
    (fun list constructor ->
      let c, s, _ = constructor in
      let constructor = (c, s) in
      let new_list =
        get_one_constructor ~is_getter ~origin_private:is_origin_private
          constructor class_package class_name id target_summary method_info
          class_info setter_map code import var_list
      in
      List.rev_append new_list list)
    [] constructor_list

let get_constructor (class_package, class_name) id target_summary recv_package
    summary method_info class_info setter_map code import var_list =
  let constr_summary_list =
    get_constructor_list (class_package, class_name) method_info class_info
  in
  let is_getter, constr_summary_list =
    let java_package, _ = get_java_package_normal_class class_name in
    if java_package = "null" && constr_summary_list = [] then
      ( true,
        get_return_object (class_package, class_name) method_info class_info )
    else (false, constr_summary_list)
  in
  let constr_summary_list =
    List.fold_left
      (fun list constructor ->
        let check, summary, count =
          check_correct_constructor target_summary id constructor summary
        in
        if check then (constructor, summary, count) :: list else list)
      [] constr_summary_list
  in
  let constr_summary_list =
    List.filter
      (fun (c, _, _) ->
        is_public_or_default ~is_getter recv_package c method_info)
      constr_summary_list
    |> List.filter (fun (c, _, _) ->
           is_recursive_param class_name c method_info |> not)
    |> remove_same_name
  in
  if constr_summary_list = [] then
    get_defined_statement class_package class_name id target_summary method_info
      setter_map code import var_list
  else
    get_many_constructor ~is_getter constr_summary_list class_package class_name
      id target_summary method_info class_info setter_map code import var_list

let get_statement param target_summary r_package summary method_info class_info
    setter_map old_code old_import old_var_list =
  match param |> snd with
  | Language.This typ -> (
      match typ with
      | Int ->
          get_constructor ("", "int") "gen1" target_summary r_package summary
            method_info class_info setter_map old_code old_import old_var_list
      | Long ->
          get_constructor ("", "long") "gen1" target_summary r_package summary
            method_info class_info setter_map old_code old_import old_var_list
      | Float ->
          get_constructor ("", "float") "gen1" target_summary r_package summary
            method_info class_info setter_map old_code old_import old_var_list
      | Double ->
          get_constructor ("", "double") "gen1" target_summary r_package summary
            method_info class_info setter_map old_code old_import old_var_list
      | Bool ->
          get_constructor ("", "bool") "gen1" target_summary r_package summary
            method_info class_info setter_map old_code old_import old_var_list
      | Char ->
          get_constructor ("", "char") "gen1" target_summary r_package summary
            method_info class_info setter_map old_code old_import old_var_list
      | String ->
          get_constructor
            (param |> fst, "String")
            "gen1" target_summary r_package summary method_info class_info
            setter_map old_code old_import old_var_list
      | Object name ->
          get_constructor
            (param |> fst, name)
            "gen1" target_summary r_package summary method_info class_info
            setter_map old_code old_import old_var_list
      | _ -> failwith "not allowed type this")
  | Language.Var (typ, id) -> (
      match typ with
      | Int ->
          let stm =
            "int " ^ id ^ " = " ^ get_value typ id target_summary ^ ";\n"
          in
          [ (stm ^ old_code, old_import, old_var_list) ]
      | Long ->
          let stm =
            "long " ^ id ^ " = " ^ get_value typ id target_summary ^ ";\n"
          in
          [ (stm ^ old_code, old_import, old_var_list) ]
      | Float ->
          let stm =
            "float " ^ id ^ " = " ^ get_value typ id target_summary ^ ";\n"
          in
          [ (stm ^ old_code, old_import, old_var_list) ]
      | Double ->
          let stm =
            "double " ^ id ^ " = " ^ get_value typ id target_summary ^ ";\n"
          in
          [ (stm ^ old_code, old_import, old_var_list) ]
      | Bool ->
          let get_boolean = get_value typ id target_summary in
          let get_boolean =
            match int_of_string_opt get_boolean with
            | Some i -> if i = 0 then "false" else "true"
            | _ -> get_boolean
          in
          let stm = "boolean " ^ id ^ " = " ^ get_boolean ^ ";\n" in
          [ (stm ^ old_code, old_import, old_var_list) ]
      | Char ->
          let stm =
            "char " ^ id ^ " = \'" ^ get_value typ id target_summary ^ "\';\n"
          in
          [ (stm ^ old_code, old_import, old_var_list) ]
      | String ->
          let get_string = get_value typ id target_summary in
          let get_string =
            if get_string = "null" then get_string
            else if Str.string_match (Str.regexp "^not ") get_string 0 then
              let get_string = Regexp.global_rm_exp Regexp.space get_string in
              "\"" ^ get_string ^ "\""
            else "\"" ^ get_string ^ "\""
          in
          [
            ( "String " ^ id ^ " = " ^ get_string ^ ";\n" ^ old_code,
              [ param |> fst ] |> List.rev_append old_import,
              old_var_list );
          ]
      | Object name ->
          get_constructor
            (param |> fst, name)
            id target_summary r_package summary method_info class_info
            setter_map old_code old_import old_var_list
      | Array _ ->
          (* TODO: implement array constructor *)
          let array_type = get_array_type typ in
          let array_constructor = get_array_constructor typ 5 in
          [
            ( array_type ^ " " ^ id ^ " = new " ^ array_constructor ^ ";\n"
              ^ old_code,
              [ param |> fst ] |> List.rev_append old_import,
              old_var_list );
          ]
      | _ -> failwith ("not allowed type var" ^ id))

let pretty_tc_format all_param =
  let imports =
    let import_set =
      all_param |> snd
      |> List.fold_left
           (fun set import ->
             ImportSet.add (import |> replace_nested_symbol) set)
           ImportSet.empty
    in
    ImportSet.fold
      (fun import stm ->
        if import = "" then stm else stm ^ "import " ^ import ^ ";\n")
      import_set ""
  in
  let start = imports ^ "\n@Test\npublic void test() throws Exception {\n" in
  let param_code =
    all_param |> fst
    |> Str.split (Str.regexp "\n")
    |> List.fold_left
         (fun code_list code ->
           if List.mem code code_list then code_list else code :: code_list)
         []
    |> List.rev
  in
  let codes =
    List.fold_left (fun code param -> code ^ param ^ "\n") start param_code
  in
  codes ^ "}\n\n"

let make_tc_file code import =
  let tc_file_name =
    String.concat "" [ "unitgen_test_"; !tc_num |> string_of_int; ".java" ]
  in
  let oc = open_out (Filename.concat !Cmdline.out_dir tc_file_name) in
  pretty_tc_format (code, import) |> output_string oc;
  flush_all ();
  tc_num := !tc_num + 1

let rec all_statement ps candidate r_package summary method_info class_info
    setter_map =
  match candidate with
  | (code, import, mk_var_list) :: tl -> (
      match mk_var_list with
      | (p, t_summary) :: var_tl ->
          let state_list =
            get_statement p t_summary r_package summary method_info class_info
              setter_map code import var_tl
            |> List.rev
          in
          let state_list = List.rev_append state_list tl in
          all_statement ps state_list r_package summary method_info class_info
            setter_map
      | [] ->
          make_tc_file code import;
          all_statement ps tl r_package summary method_info class_info
            setter_map)
  | [] -> []

let find_all_parameter ps_method ps_method_summary summary method_info
    class_info setter_map =
  let ps_method_info = MethodInfo.M.find ps_method method_info in
  let ps_method_params = ps_method_info.MethodInfo.formal_params in
  let params = List.map (fun p -> (p, ps_method_summary)) ps_method_params in
  let r_package = get_recv_package ps_method class_info in
  let execute_ps id ps_method =
    let ps_info = MethodInfo.M.find ps_method method_info in
    let ps_params = ps_info.MethodInfo.formal_params in
    let str_params =
      List.fold_left
        (fun str_params variable ->
          match variable |> snd with
          | Language.Var (_, id) -> str_params ^ ", " ^ id
          | _ -> str_params)
        "" ps_params
      |> Regexp.global_rm_exp Regexp.start_bm2
    in
    let str_params = "(" ^ str_params ^ ")" in
    let ps_method =
      Str.split Regexp.dot ps_method
      |> List.tl |> List.hd
      |> Str.split (Str.regexp "(")
      |> List.hd
      |> Regexp.global_rm_exp (Str.regexp "<init>")
    in
    id ^ ps_method ^ str_params
  in
  let execute_init_ps id class_name ps_method =
    let ps_info = MethodInfo.M.find ps_method method_info in
    let ps_params = ps_info.MethodInfo.formal_params in
    let str_params =
      List.fold_left
        (fun str_params variable ->
          match variable |> snd with
          | Language.Var (_, id) -> str_params ^ ", " ^ id
          | _ -> str_params)
        "" ps_params
      |> Regexp.global_rm_exp Regexp.start_bm2
    in
    let str_params = "(" ^ str_params ^ ")" in
    class_name ^ " " ^ id ^ " = new " ^ class_name ^ str_params
  in
  let id, import =
    if is_static_method ps_method method_info then
      get_static_constructor ps_method (class_info |> fst)
    else if is_init_method ps_method then
      get_init_constructor ps_method method_info
    else ("gen1", "")
  in
  let codes =
    let ps_statement, params =
      if is_init_method ps_method then
        (execute_init_ps "gen1" id ps_method, params |> List.tl)
      else (execute_ps (id ^ ".") ps_method, params)
    in
    let ps_statement = ps_statement ^ ";" in
    all_statement ps_method
      [ (ps_statement, [ import ], params) ]
      r_package summary method_info class_info setter_map
  in
  codes

let mk_testcases s_method error_summary call_graph summary call_prop_map
    method_info class_info setter_map =
  let ps_methods =
    find_ps_method s_method error_summary call_graph summary call_prop_map
      method_info
  in
  let code_set =
    List.fold_left
      (fun codes (ps_method, ps_method_summary) ->
        find_all_parameter ps_method ps_method_summary summary method_info
          class_info setter_map
        |> List.fold_left (fun set new_code -> CodeSet.add new_code set) codes)
      CodeSet.empty ps_methods
  in
  CodeSet.fold (fun code tests -> tests ^ code) code_set ""
