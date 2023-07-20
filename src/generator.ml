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
module AST = Language.AST

(* defining for constructor priority.
   if Range is wide then Range set 100 *)
type domain = Top | Range of int

type t = {
  code : AST.t;
  import : string list;
  variable : ((string * Language.variable) * Language.summary) list;
  score : int;
  recv_package : string;
}

module ImportSet = Set.Make (struct
  type t = string

  let compare = compare
end)

let outer = ref 0

let getter = ref 0

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

(* return last condition *)
let condition partial func = failwith "not implemented"

let point value =
  (* if value = top then 100, value range > 10 then 10, otherwise value range*)
  failwith "not implemented"

let score t_summary p_summary partial =
  (* partial.variable size + sum(card) *)
  let length = partial.variable |> List.length in
  failwith "not implemented"

let rec find_relation given_symbol relation =
  match Relation.M.find_opt given_symbol relation with
  | Some find_symbol -> find_relation find_symbol relation
  | None -> given_symbol

let get_rh_name ~is_var rh =
  if is_var then match rh with Condition.RH_Var v -> v | _ -> ""
  else match rh with Condition.RH_Symbol s -> s | _ -> ""

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

(* memory: Condition.mem *)
(* return: (callee_actual_symbol * head_symbol) list *)
(* if head = "" then this symbol can be any value *)
let get_head_symbol_list symbols (_, memory) =
  List.map
    (fun symbol ->
      try get_head_symbol symbol memory |> List.hd with _ -> (symbol, ""))
    symbols

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
        (Value.M.add caller_symbol callee_value caller_prop.Language.value, true)
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

let satisfy callee_method callee_summary call_prop method_info =
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
      check_intersect ~is_init:false call_prop callee_summary value_symbol_list
    in
    let values = combine_value call_prop.Language.value values_and_check in
    let check = List.filter (fun (_, c) -> c = false) values_and_check in
    (values, check)
  in
  let values, check = intersect_value in
  if check = [] then (values, true) else (values, false)

let new_value_summary old_summary new_value =
  Language.
    {
      relation = old_summary.relation;
      value = new_value;
      precond = old_summary.precond;
      postcond = old_summary.postcond;
      args = old_summary.args;
    }

let replace_nested_symbol str = Str.global_replace Regexp.dollar "." str

let is_nested_class name = String.contains name '$'

let is_normal_class class_name class_info =
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
  match ClassInfo.M.find_opt class_package (class_info |> fst) with
  | Some info -> (
      let class_type = info.ClassInfo.class_type in
      match class_type with Language.Private -> true | _ -> false)
  | None -> false

let is_static_method m_name method_info =
  match MethodInfo.M.find_opt m_name method_info with
  | None -> false
  | Some m -> m.MethodInfo.is_static

let is_private m_name method_info =
  match (MethodInfo.M.find m_name method_info).MethodInfo.modifier with
  | Private -> true
  | _ -> false

let is_public m_name method_info =
  match (MethodInfo.M.find m_name method_info).MethodInfo.modifier with
  | Public -> true
  | _ -> false

let is_init_method method_name =
  Str.string_match (".*\\.<init>" |> Str.regexp) method_name 0

let get_class_name ~infer method_name =
  if infer then Regexp.global_rm_exp ("\\..+(.*)" |> Str.regexp) method_name
  else Regexp.global_rm_exp ("(.*)" |> Str.regexp) method_name

let get_package formal_params =
  List.fold_left
    (fun found (import, var) ->
      match var with Language.This _ -> import | _ -> found)
    "" formal_params

(* e.g., java.util. --> not contain class name *)
let get_import t_method (class_info, _) =
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

let is_test_file file_name =
  Str.string_match (Str.regexp ".*/test/.*") file_name 0

let is_public_or_default ~is_getter recv_package method_name method_info =
  let info = MethodInfo.M.find method_name method_info in
  let is_test_file =
    (* If this method is a method in the test file,
       don't use it even if the modifier is public*)
    is_test_file info.MethodInfo.filename
  in
  let m_package = get_package info.MethodInfo.formal_params in
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
    if Str.string_match (Str.regexp m_package) recv_package 0 then
      match info.MethodInfo.modifier with
      | Default | Protected | Public -> true
      | _ -> false
    else
      match info.MethodInfo.modifier with
      | Public when not is_test_file -> true
      | _ -> false

let is_recursive_param parent_class method_name method_info =
  let info = MethodInfo.M.find method_name method_info in
  let this = Language.Object parent_class in
  List.fold_left
    (fun check (_, var) ->
      match var with
      | Language.Var (typ, _) when typ = this -> true
      | _ -> check)
    false info.MethodInfo.formal_params

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
    | Language.Int -> [ "0"; "1"; "-1"; "100"; "-100" ]
    | Language.Long -> [ "0"; "1"; "-1"; "100"; "-100" ]
    | Language.Float -> [ "0.0"; "1.0"; "-1.0"; "100.0"; "-100.0" ]
    | Language.Double -> [ "0.0"; "1.0"; "-1.0"; "100.0"; "-100.0" ]
    | Language.Bool -> [ "false"; "true" ]
    | Language.Char -> [ "x" ]
    | Language.String -> [ "" ]
    | _ -> [ "null" ]
  in
  default_value

let not_found_value = function Value.Eq None -> true | _ -> false

let calc_value id = function
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
      | Int i1, Int i2 | Long i1, Long i2 | Int i1, Long i2 | Long i1, Int i2 ->
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
      | Int i1, Int i2 | Long i1, Long i2 | Int i1, Long i2 | Long i1, Int i2 ->
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
  let default_values = default_value_list typ in
  let find_value =
    Value.M.fold
      (fun symbol value find_value ->
        if symbol = target_variable then value else find_value)
      values (Value.Eq None)
  in
  if not_found_value find_value then default_values
  else [ calc_value id find_value ]

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

let get_setter_list constructor method_info setter_map =
  let class_name = get_class_name ~infer:false constructor in
  let setter_list = try SetterMap.M.find class_name setter_map with _ -> [] in
  let rec filter_setter setter_list =
    match setter_list with
    | (method_name, change_field) :: tl ->
        if List.length change_field < 3 then
          filter_setter tl |> List.cons method_name
        else filter_setter tl
    | _ -> []
  in
  filter_setter setter_list
  |> List.filter (fun setter -> is_private setter method_info |> not)

let get_setter constructor id method_summary c_summary method_info setter_map =
  if c_summary = Language.empty_summary then
    (FieldMap.M.empty, get_setter_list constructor method_info setter_map)
  else
    let m_pre_var, m_pre_mem = method_summary.Language.precond in
    let m_pre_value = method_summary.Language.value in
    let c_post_var, c_post_mem = c_summary.Language.postcond in
    let c_post_value = c_summary.Language.value in
    let m_id_symbol = get_id_symbol id m_pre_var m_pre_mem in
    let c_this_symbol = get_id_symbol "this" c_post_var c_post_mem in
    (* need_setter_field:
       The setter field map that must be met.
       This value is got from the method summary.*)
    let need_setter_field =
      collect_field m_id_symbol c_this_symbol m_pre_value c_post_value m_pre_mem
        c_post_mem FieldMap.M.empty
    in
    (need_setter_field, get_setter_list constructor method_info setter_map)

let mk_params_format params =
  let params =
    List.fold_left
      (fun param_code (_, param) ->
        match param with
        | Language.This _ -> param_code
        | Language.Var (_, id) -> param_code ^ ", " ^ id)
      "" params
  in
  let params = Regexp.global_rm_exp Regexp.start_bm2 params in
  "(" ^ params ^ ")"

let satisfied_c method_summary id candidate_constructor summary =
  let c_summarys = SummaryMap.M.find candidate_constructor summary in
  let method_symbols, method_memory = method_summary.Language.precond in
  let id = if id = "gen1" then "this" else id in
  let target_symbol =
    get_id_symbol id method_symbols method_memory |> get_rh_name ~is_var:false
  in
  if target_symbol = "" then (true, c_summarys |> List.hd, 0)
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
        let t_count =
          List.filter (fun (_, c) -> c = true) check_summary |> List.length
        in
        let new_values = combine_value c_summary.Language.value check_summary in
        let new_c_summary = new_value_summary c_summary new_values in
        if check = [] then (true, new_c_summary, t_count) else check_value)
      (false, Language.empty_summary, 0)
      check_summarys

let remove_same_name c_list =
  let get_same_one target list =
    List.filter
      (fun (c_name, _, _, _) ->
        let class_name = get_class_name ~infer:true c_name in
        target = class_name)
      list
    |> List.hd
  in
  List.fold_left
    (fun new_list (c, _, _, _) ->
      let name = get_class_name ~infer:true c in
      let one = get_same_one name c_list in
      if List.mem one new_list then new_list else one :: new_list)
    [] c_list
  |> List.rev

let get_static_constructor t_method class_info =
  let class_name = get_class_name ~infer:true t_method in
  let full_class_name =
    ClassInfo.M.fold
      (fun full_name _ find_name ->
        let name = Str.split Regexp.dot full_name |> List.rev |> List.hd in
        if class_name = name then full_name else find_name)
      class_info ""
  in
  (Some (class_name |> replace_nested_symbol), full_class_name)

let get_init_constructor t_method method_info =
  let c_info = MethodInfo.M.find t_method method_info in
  let c_import = get_package c_info.MethodInfo.formal_params in
  (None, c_import)

(* e.g., java.util.Date --> contain class name *)
let get_package_from_method t_method (class_info, _) =
  let class_name = get_class_name ~infer:true t_method in
  let full_class_name =
    ClassInfo.M.fold
      (fun full_name _ find_name ->
        let name = Str.split Regexp.dot full_name |> List.rev |> List.hd in
        if class_name = name then full_name else find_name)
      class_info ""
  in
  full_class_name

let get_constructor_import c_info =
  let rec nested_import c_import =
    if String.contains c_import '$' then
      let new_import = Str.replace_first ("\\$.*" |> Str.regexp) "" c_import in
      let next_c_import = Str.replace_first Regexp.dollar "." c_import in
      nested_import next_c_import |> List.cons new_import
    else [ c_import ]
  in
  let c_import = get_package c_info.MethodInfo.formal_params in
  nested_import c_import

let match_constructor_name class_name method_name =
  let class_name = Str.split Regexp.dot class_name |> List.rev |> List.hd in
  let class_name = Str.global_replace Regexp.dollar "\\$" class_name in
  Str.string_match (class_name ^ "\\.<init>" |> Str.regexp) method_name 0

let match_return_object class_name method_name method_info =
  let class_name = Str.split Regexp.dot class_name |> List.rev |> List.hd in
  let info = MethodInfo.M.find method_name method_info in
  let return = info.MethodInfo.return in
  Str.string_match (Str.regexp class_name) return 0

let mk_getter_var getter_method getter_summary method_info class_info =
  let class_name = get_class_name ~infer:true getter_method in
  let import = get_package_from_method getter_method class_info in
  let var_name = "gen_get" ^ (!getter |> string_of_int) in
  getter := !getter + 1;
  let var = Language.Var (Object class_name, var_name) in
  let info = MethodInfo.M.find getter_method method_info in
  let getter_statement =
    Str.split Regexp.dot getter_method
    |> List.tl |> List.hd
    |> Regexp.global_rm_exp (Str.regexp "(.*)$")
  in
  ( Some ((import, var), getter_summary),
    getter_statement,
    info.MethodInfo.formal_params )

let is_java_io_class class_name =
  if class_name = "PrintStream" || class_name = "InputStream" then true
  else false

let is_file_class class_name = if class_name = "File" then true else false

let is_class_class class_name = if class_name = "Class" then true else false

let is_graphics_class class_name =
  if Str.string_match ("Graphics" ^ "[0-9]*" |> Str.regexp) class_name 0 then
    true
  else false

let file_code =
  AST.Stmt
    ( Language.Var (Object "File", "con_file"),
      NewCreate
        ( {
            id = None;
            method_name = "File";
            args = Constant [ "\"unitcon_file\"" ];
          },
          SETNT ) )

let create_file_code file_name =
  AST.Setter
    ( file_name,
      { id = None; method_name = "createNewFile"; args = Constant [] },
      SETEmpty )

let image_code =
  AST.Stmt
    ( Language.Var (Object "BufferedImage", "con_image"),
      NewCreate
        ( {
            id = None;
            method_name = "BufferedImage";
            args = Constant [ "100"; "100"; "BufferedImage.TYPE_INT_RGB" ];
          },
          SETNT ) )

let create_graphics_code g_name =
  AST.Setter
    ( g_name,
      { id = None; method_name = "createGraphics"; args = Constant [] },
      SETEmpty )

let class_code =
  AST.Stmt
    ( Language.Var (Object "Object", "con_obj"),
      NewCreate
        ({ id = None; method_name = "Object"; args = Constant [] }, SETNT) )

let get_class_code obj_name =
  AST.Setter
    ( obj_name,
      { id = None; method_name = "getClass"; args = Constant [] },
      SETEmpty )

let get_java_package_class class_name =
  if class_name = "Collection" || class_name = "List" then
    ("ArrayList", [ "java.util.ArrayList" ])
  else if class_name = "Map" || class_name = "HashMap" then
    ("HashMap", [ "java.util.HashMap" ])
  else if class_name = "Object" then ("Object", [])
  else if class_name = "File" then ("File", [ "java.io.File" ])
  else if class_name = "PrintStream" then ("PrintStream", [ "java.io.File" ])
  else if class_name = "InputStream" then
    ( "FileInputStream",
      [ "java.io.File"; "java.io.InputStream"; "java.io.FileInputStream" ] )
  else if is_graphics_class class_name then
    ("BufferedImage", [ "java.awt.image.BufferedImage" ])
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
          then (method_name, class_package) :: init_list
          else init_list)
        method_list class_to_find)
    method_info []

let find_global_var_list c_name t_var mem summary =
  let all_var s_trace =
    Condition.M.fold
      (fun head _ gvar_list ->
        match head with
        | Condition.RH_Var var -> (c_name ^ "." ^ var) :: gvar_list
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
    (fun init_name init_mem list ->
      if Str.string_match (c_name ^ "\\.<clinit>" |> Str.regexp) init_name 0
      then
        match t_var with
        | Some v ->
            (Condition.M.fold (fun _ s_trace list ->
                 match compare_var v s_trace with
                 | Some gv -> gv :: list
                 | None -> list))
              mem list
        | None ->
            (Condition.M.fold (fun _ s_trace list ->
                 List.rev_append (all_var s_trace) list))
              init_mem list
      else list)
    summary []

let get_global_var_list class_name t_summary summary =
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
  | None -> find_global_var_list class_name None mem summary
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
      find_global_var_list class_name target_variable mem summary

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

let sort_constructor_list c_list method_info =
  List.sort
    (fun (c1, _, k1, _) (c2, _, k2, _) ->
      if compare k1 k2 <> 0 then compare k2 k1
      else
        let c1_info = MethodInfo.M.find c1 method_info in
        let c1_formal = c1_info.MethodInfo.formal_params |> List.length in
        let c2_info = MethodInfo.M.find c2 method_info in
        let c2_formal = c2_info.MethodInfo.formal_params |> List.length in
        compare c1_formal c2_formal)
    c_list

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

let mk_setter_format setter method_info =
  let m_info = MethodInfo.M.find setter method_info in
  let setter_statement =
    Str.split Regexp.dot setter
    |> List.tl |> List.hd
    |> Regexp.global_rm_exp (Str.regexp "(.*)$")
  in
  (setter_statement, m_info.MethodInfo.formal_params)

let is_receiver id =
  let new_id1 = Str.replace_first (Str.regexp "gen") "" id in
  let new_id2 = Str.replace_first (Str.regexp "gen_get") "" id in
  let new_id3 = Str.replace_first (Str.regexp "outer") "" id in
  match
    ( int_of_string_opt new_id1,
      int_of_string_opt new_id2,
      int_of_string_opt new_id3 )
  with
  | None, None, None -> false
  | _, _, _ -> true

let primitive class_name import id partial =
  let code =
    AST.modify_stnt
      (Stmt (Language.Var (Object class_name, id), Primitive Null))
      partial.code
  in
  [
    {
      code = AST.TestCase (AST.MStmt (STNT, code), AST.get_ee partial.code);
      import;
      variable = partial.variable;
      score = partial.score;
      recv_package = partial.recv_package;
    };
  ]

let global_var class_name import id t_summary method_info partial =
  let g = get_global_var_list class_name t_summary method_info in
  (List.fold_left (fun list gv ->
       let code =
         AST.modify_stnt
           (Stmt (Language.Var (Object class_name, id), GV gv))
           partial.code
       in
       {
         code = AST.TestCase (AST.MStmt (STNT, code), AST.get_ee partial.code);
         import = partial.import |> List.cons import;
         variable = partial.variable;
         score = partial.score;
         recv_package = partial.recv_package;
       }
       :: list))
    [] g

let get_setter_code constructor id method_summary c_summary method_info
    setter_map =
  if is_receiver id then [ (AST.SETEmpty, []) ]
  else
    let met_field_map, setter_list =
      get_setter constructor id method_summary c_summary method_info setter_map
    in
    let met_value_map =
      FieldMap.M.fold
        (fun s value map -> Value.M.add s value map)
        met_field_map Value.M.empty
    in
    let new_summary = new_value_summary c_summary met_value_map in
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
        let m, params = mk_setter_format setter method_info in
        let s =
          AST.Setter
            (id, { id = None; method_name = m; args = Param params }, SETNT)
        in
        (s, iter_params params) :: list)
      [ (AST.SETEmpty, []) ]
      setter_list

(* statement data structure: code * import * mk_var_list *)
let get_defined_statement class_package class_name id t_summary method_info
    setter_map partial =
  let class_name = class_name |> replace_nested_symbol in
  let nc_name, import = get_java_package_class class_name in
  if is_java_io_class class_name then
    let code =
      AST.modify_stnt
        (Stmt
           ( Language.Var (Object class_name, id),
             NewCreate
               ( {
                   id = None;
                   method_name = nc_name;
                   args = Constant [ "con_file" ];
                 },
                 SETNT ) ))
        partial.code
    in
    let ee = AST.get_ee partial.code in
    let code =
      AST.TestCase
        ( AST.modify_stnt file_code (AST.TestCase (AST.MStmt (STNT, code), ee)),
          ee )
      |> AST.modify_setnt
           (Language.Var (Object "File", "con_file"))
           (create_file_code "con_file")
    in
    [
      {
        code = AST.TestCase (AST.MStmt (STNT, code), ee);
        import = import |> List.rev_append partial.import;
        variable = partial.variable;
        score = partial.score;
        recv_package = partial.recv_package;
      };
    ]
  else if is_file_class class_name then
    let ee = AST.get_ee partial.code in
    let code =
      AST.TestCase (AST.modify_stnt file_code partial.code, ee)
      |> AST.modify_setnt
           (Language.Var (Object "File", "con_file"))
           (create_file_code "con_file")
    in
    [
      {
        code = AST.TestCase (AST.MStmt (STNT, code), ee);
        import = import |> List.rev_append partial.import;
        variable = partial.variable;
        score = partial.score;
        recv_package = partial.recv_package;
      };
    ]
  else if is_class_class class_name then
    let ee = AST.get_ee partial.code in
    let code =
      AST.TestCase (AST.modify_stnt class_code partial.code, ee)
      |> AST.modify_setnt
           (Language.Var (Object "Object", "con_obj"))
           (get_class_code "con_obj")
    in
    [
      {
        code = AST.TestCase (AST.MStmt (STNT, code), ee);
        import = import |> List.rev_append partial.import;
        variable = partial.variable;
        score = partial.score;
        recv_package = partial.recv_package;
      };
    ]
  else if is_graphics_class class_name then
    let ee = AST.get_ee partial.code in
    let code =
      AST.TestCase (AST.modify_stnt image_code partial.code, ee)
      |> AST.modify_setnt
           (Language.Var (Object "BufferedImage", "con_image"))
           (create_graphics_code "con_image")
    in
    [
      {
        code = AST.TestCase (AST.MStmt (STNT, code), ee);
        import =
          import |> List.cons class_package |> List.rev_append partial.import;
        variable = partial.variable;
        score = partial.score;
        recv_package = partial.recv_package;
      };
    ]
  else if nc_name = "null" then primitive class_name partial.import id partial
  else
    let setter_code_list =
      try
        get_setter_code nc_name id t_summary Language.empty_summary method_info
          setter_map
      with _ -> []
    in
    let ee = AST.get_ee partial.code in
    let new_code =
      AST.Stmt
        ( Language.Var (Object class_name, id),
          NewCreate
            ({ id = None; method_name = nc_name; args = Constant [] }, SETNT) )
    in
    let new_tc =
      AST.TestCase (AST.MStmt (STNT, AST.modify_stnt new_code partial.code), ee)
    in
    (* TODO: current setter, var_list is not wanted format *)
    List.fold_left
      (fun list (setter, var_list) ->
        let code =
          AST.modify_setnt (Language.Var (Object class_name, id)) setter new_tc
        in
        {
          code = AST.TestCase (code, ee);
          import = import |> List.rev_append partial.import;
          variable = List.rev_append var_list partial.variable;
          score = partial.score;
          recv_package = partial.recv_package;
        }
        :: list)
      (primitive class_name partial.import id partial
      |> List.cons
           {
             code = new_tc;
             import = import |> List.rev_append partial.import;
             variable = partial.variable;
             score = partial.score;
             recv_package = partial.recv_package;
           })
      setter_code_list

let get_return_object (class_package, class_name) method_info
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
          if match_return_object class_name_to_find method_name method_info then
            ( method_name,
              get_package_from_method method_name (class_info, hierarchy_graph)
            )
            :: init_list
          else init_list)
        method_list class_to_find)
    method_info []

let get_new_code id_var get_var m m_params code =
  let c_method = AST.{ id = None; method_name = m; args = Param m_params } in
  match get_var with
  | Some x ->
      AST.modify_stnt
        (Stmt (id_var, GetCreate (x |> fst |> snd, c_method, SETEmpty)))
        code
  | None -> AST.modify_stnt (Stmt (id_var, NewCreate (c_method, SETNT))) code

let get_one_constructor ~is_getter ~origin_private constructor class_package
    class_name id t_summary method_info class_info setter_map partial =
  let c, s, i = constructor in
  if c = "null" then
    primitive class_name (List.cons i partial.import) id partial
  else
    let c_statement = c in
    let class_name =
      if origin_private then
        c_statement |> replace_nested_symbol
        |> Str.replace_first (Str.regexp ".<init>") ""
        |> Regexp.global_rm_exp (Str.regexp "(.*)$")
      else class_name
    in
    let c_info = MethodInfo.M.find c_statement method_info in
    let c_params = c_info.MethodInfo.formal_params in
    let c_class_name = get_package c_params in
    let c_summary = s in
    let setter_code_list =
      get_setter_code class_name id t_summary c_summary method_info setter_map
    in
    let c_statement =
      Str.replace_first (Str.regexp ".<init>") "" c_statement
      |> Regexp.global_rm_exp (Str.regexp "(.*)$")
    in
    let c_import = get_constructor_import c_info in
    let import =
      let c_import = if is_getter then List.cons i c_import else c_import in
      if origin_private then c_import |> List.rev_append partial.import
      else c_import |> List.cons class_package |> List.rev_append partial.import
    in
    let c_statement =
      if
        is_nested_class c_class_name
        && is_static_class ~is_class:true c_class_name class_info
      then replace_nested_symbol c_statement
      else c_statement
    in
    if this_is_null c_summary then primitive class_name import id partial
    else if is_static_method c method_info then
      (* don't remove the first parameter because first parameter is not this. *)
      let get_var, m, m_params =
        if is_getter then mk_getter_var c s method_info class_info
        else (None, c_statement, c_params)
      in
      let id_var = Language.Var (Object class_name, id) in
      let new_code = get_new_code id_var get_var m m_params partial.code in
      let new_tc =
        AST.TestCase (AST.MStmt (STNT, new_code), AST.get_ee partial.code)
      in
      let new_var = c_params |> List.map (fun p -> (p, c_summary)) in
      let variable = List.rev_append new_var partial.variable in
      List.fold_left
        (fun list (setter, var_list) ->
          let code = AST.modify_setnt id_var setter new_tc in
          {
            code = AST.TestCase (code, AST.get_ee partial.code);
            import;
            variable = List.rev_append var_list variable;
            score = partial.score;
            recv_package = partial.recv_package;
          }
          :: list)
        [] setter_code_list
    else if List.length c_params = 1 then
      (* method only have this (receiver variable) *)
      let get_var, m, m_params =
        if is_getter then mk_getter_var c s method_info class_info
        else (None, c_statement, c_params)
      in
      let id_var = Language.Var (Object class_name, id) in
      let new_code = get_new_code id_var get_var m m_params partial.code in
      let new_tc =
        AST.TestCase (AST.MStmt (STNT, new_code), AST.get_ee partial.code)
      in
      let variable =
        match get_var with
        | Some x -> x :: partial.variable
        | _ -> partial.variable
      in
      List.fold_left
        (fun list (setter, var_list) ->
          let code = AST.modify_setnt id_var setter new_tc in
          {
            code = AST.TestCase (code, AST.get_ee partial.code);
            import;
            variable = List.rev_append var_list variable;
            score = partial.score;
            recv_package = partial.recv_package;
          }
          :: list)
        [] setter_code_list
    else if
      is_nested_class c_class_name
      && is_static_class ~is_class:true c_class_name class_info |> not
    then
      (* generation format: new Outer().new Inner(); *)
      let c_statement, c_params =
        let outer_import, outer_var = List.tl c_params |> List.hd in
        let c_statement, outer =
          match outer_var with
          | Language.Var (typ, _) ->
              outer := !outer + 1;
              ( c_statement |> Str.replace_first (Str.regexp "^.*\\$") "",
                ( outer_import,
                  Language.Var (typ, "outer" ^ (!outer |> string_of_int)) ) )
          | _ -> ("", (outer_import, outer_var))
        in
        (c_statement, List.tl c_params |> List.tl |> List.cons outer)
      in
      let id_var = Language.Var (Object class_name, id) in
      let new_code =
        get_new_code id_var
          (Some
             ( ("", Language.Var (None, "outer" ^ (!outer |> string_of_int))),
               Language.empty_summary ))
          ("new " ^ c_statement) (List.tl c_params) partial.code
      in
      let new_tc =
        AST.TestCase (AST.MStmt (STNT, new_code), AST.get_ee partial.code)
      in
      let c_params = c_params |> List.map (fun p -> (p, c_summary)) in
      List.fold_left
        (fun list (setter, var_list) ->
          let code = AST.modify_setnt id_var setter new_tc in
          {
            code = AST.TestCase (code, AST.get_ee partial.code);
            import;
            variable =
              List.rev_append c_params partial.variable
              |> List.rev_append var_list;
            score = partial.score;
            recv_package = partial.recv_package;
          }
          :: list)
        [] setter_code_list
    else if
      is_nested_class c_class_name
      && is_static_class ~is_class:true c_class_name class_info
    then
      (* generation format: new Outer.Inner(); *)
      let id_var = Language.Var (Object class_name, id) in
      let new_code =
        get_new_code id_var None c_statement c_params partial.code
      in
      let new_tc =
        AST.TestCase (AST.MStmt (STNT, new_code), AST.get_ee partial.code)
      in
      let c_params =
        c_params |> List.tl |> List.map (fun p -> (p, c_summary))
      in
      List.fold_left
        (fun list (setter, var_list) ->
          let code = AST.modify_setnt id_var setter new_tc in
          {
            code = AST.TestCase (code, AST.get_ee partial.code);
            import;
            variable =
              List.rev_append c_params partial.variable
              |> List.rev_append var_list;
            score = partial.score;
            recv_package = partial.recv_package;
          }
          :: list)
        [] setter_code_list
    else
      (* generation format: new Normal(...); *)
      let get_var, m, m_params =
        if is_getter then mk_getter_var c s method_info class_info
        else (None, c_statement, c_params)
      in
      let id_var = Language.Var (Object class_name, id) in
      let new_code = get_new_code id_var get_var m m_params partial.code in
      let new_tc =
        AST.TestCase (AST.MStmt (STNT, new_code), AST.get_ee partial.code)
      in
      let variable =
        if is_getter then m_params |> List.map (fun p -> (p, c_summary))
        else m_params |> List.tl |> List.map (fun p -> (p, c_summary))
      in
      let variable =
        match get_var with Some x -> x :: variable | _ -> variable
      in
      List.fold_left
        (fun list (setter, var_list) ->
          let code = AST.modify_setnt id_var setter new_tc in
          {
            code = AST.TestCase (code, AST.get_ee partial.code);
            import;
            variable =
              List.rev_append variable partial.variable
              |> List.rev_append var_list;
            score = partial.score;
            recv_package = partial.recv_package;
          }
          :: list)
        [] setter_code_list

let get_many_constructor ~is_getter c_summary_list class_package class_name id
    t_summary method_info class_info setter_map partial =
  let c_list = sort_constructor_list c_summary_list method_info in
  let c_list =
    if Str.string_match (Str.regexp "gen") id 0 then c_list
    else ("null", Language.empty_summary, 0, class_package) :: c_list
  in
  List.fold_left
    (fun list constructor ->
      let c, s, _, i = constructor in
      let constructor = (c, s, i) in
      let new_list =
        get_one_constructor ~is_getter
          ~origin_private:(is_private_class class_package class_info)
          constructor class_package class_name id t_summary method_info
          class_info setter_map partial
      in
      List.rev_append new_list list)
    [] c_list
  |> List.rev

let satisfied_c_list id t_summary summary summary_list =
  List.fold_left
    (fun list (constructor, import) ->
      let check, summary, count =
        satisfied_c t_summary id constructor summary
      in
      if check then (constructor, summary, count, import) :: list else list)
    [] summary_list

let get_constructor (class_package, class_name) id t_summary summary method_info
    class_info setter_map partial =
  let summary_filtering typ list =
    List.filter
      (fun (c, _, _, _) ->
        is_public_or_default ~is_getter:typ partial.recv_package c method_info)
      list
    |> List.filter (fun (c, _, _, _) ->
           is_recursive_param class_name c method_info |> not)
    |> remove_same_name
  in
  let c_summary_list =
    get_constructor_list (class_package, class_name) method_info class_info
    |> satisfied_c_list id t_summary summary
    |> summary_filtering false
  in
  let g_summary_list =
    get_return_object (class_package, class_name) method_info class_info
    |> satisfied_c_list id t_summary summary
    |> summary_filtering true
  in
  if c_summary_list = [] && g_summary_list = [] then
    get_defined_statement class_package class_name id t_summary method_info
      setter_map partial
  else if c_summary_list = [] then
    get_many_constructor ~is_getter:true g_summary_list class_package class_name
      id t_summary method_info class_info setter_map partial
  else
    get_many_constructor ~is_getter:false c_summary_list class_package
      class_name id t_summary method_info class_info setter_map partial

let get_statement param t_summary summary method_info class_info setter_map
    old_partial =
  match param |> snd with
  | Language.This typ -> (
      match typ with
      | Int ->
          get_constructor ("", "int") "gen1" t_summary summary method_info
            class_info setter_map old_partial
      | Long ->
          get_constructor ("", "long") "gen1" t_summary summary method_info
            class_info setter_map old_partial
      | Float ->
          get_constructor ("", "float") "gen1" t_summary summary method_info
            class_info setter_map old_partial
      | Double ->
          get_constructor ("", "double") "gen1" t_summary summary method_info
            class_info setter_map old_partial
      | Bool ->
          get_constructor ("", "bool") "gen1" t_summary summary method_info
            class_info setter_map old_partial
      | Char ->
          get_constructor ("", "char") "gen1" t_summary summary method_info
            class_info setter_map old_partial
      | String ->
          get_constructor
            (param |> fst, "String")
            "gen1" t_summary summary method_info class_info setter_map
            old_partial
      | Object name ->
          get_constructor
            (param |> fst, name)
            "gen1" t_summary summary method_info class_info setter_map
            old_partial
      | _ -> failwith "not allowed type this")
  | Language.Var (typ, id) -> (
      let values = get_value typ id t_summary in
      match typ with
      | Int | Long ->
          List.fold_left
            (fun list value ->
              let code =
                AST.modify_stnt
                  (Stmt (param |> snd, Primitive (Z (value |> int_of_string))))
                  old_partial.code
              in
              {
                code =
                  AST.TestCase
                    (AST.MStmt (STNT, code), AST.get_ee old_partial.code);
                import = old_partial.import;
                variable = old_partial.variable;
                score = old_partial.score;
                recv_package = old_partial.recv_package;
              }
              :: list)
            [] values
      | Float | Double ->
          List.fold_left
            (fun list value ->
              let code =
                AST.modify_stnt
                  (Stmt (param |> snd, Primitive (R (value |> float_of_string))))
                  old_partial.code
              in
              {
                code =
                  AST.TestCase
                    (AST.MStmt (STNT, code), AST.get_ee old_partial.code);
                import = old_partial.import;
                variable = old_partial.variable;
                score = old_partial.score;
                recv_package = old_partial.recv_package;
              }
              :: list)
            [] values
      | Bool ->
          List.fold_left
            (fun list value ->
              let value =
                match int_of_string_opt value with
                | Some i -> if i = 0 then false else true
                | _ -> value |> bool_of_string
              in
              let code =
                AST.modify_stnt
                  (Stmt (param |> snd, Primitive (B value)))
                  old_partial.code
              in
              {
                code =
                  AST.TestCase
                    (AST.MStmt (STNT, code), AST.get_ee old_partial.code);
                import = old_partial.import;
                variable = old_partial.variable;
                score = old_partial.score;
                recv_package = old_partial.recv_package;
              }
              :: list)
            [] values
      | Char ->
          List.fold_left
            (fun list value ->
              let code =
                AST.modify_stnt
                  (Stmt (param |> snd, Primitive (C value.[0])))
                  old_partial.code
              in
              {
                code =
                  AST.TestCase
                    (AST.MStmt (STNT, code), AST.get_ee old_partial.code);
                import = old_partial.import;
                variable = old_partial.variable;
                score = old_partial.score;
                recv_package = old_partial.recv_package;
              }
              :: list)
            [] values
      | String ->
          List.fold_left
            (fun list value ->
              let code =
                if value = "null" then
                  AST.modify_stnt
                    (Stmt (param |> snd, Primitive Null))
                    old_partial.code
                else
                  AST.modify_stnt
                    (Stmt (param |> snd, Primitive (S value)))
                    old_partial.code
              in
              {
                code =
                  AST.TestCase
                    (AST.MStmt (STNT, code), AST.get_ee old_partial.code);
                import = [ param |> fst ] |> List.rev_append old_partial.import;
                variable = old_partial.variable;
                score = old_partial.score;
                recv_package = old_partial.recv_package;
              }
              :: list)
            [] values
      | Object name ->
          get_constructor
            (param |> fst, name)
            id t_summary summary method_info class_info setter_map old_partial
      | Array _ ->
          (* TODO: implement array constructor *)
          (* let array_type = get_array_type typ in
             let array_constructor = get_array_constructor typ 5 in
             array_type ^ " " ^ id ^ " = new " ^ array_constructor ^ ";\n"
                   ^ old_partial.code; *)
          [
            {
              code = old_partial.code;
              import = [ param |> fst ] |> List.rev_append old_partial.import;
              variable = old_partial.variable;
              score = old_partial.score;
              recv_package = old_partial.recv_package;
            };
          ]
      | None -> [ old_partial ])

let pretty_tc_format all_param =
  let imports =
    let import_set =
      all_param |> fst
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
  let start = "\n@Test\npublic void unitcon_test() throws Exception {\n" in
  let codes = start ^ (all_param |> snd |> AST.testcase_code) ^ "}\n\n" in
  (imports, codes)

let rec all_statement candidate summary method_info class_info setter_map =
  match candidate with
  | partial :: tl -> (
      match partial.variable with
      | (p, t_summary) :: var_tl ->
          let state_list =
            get_statement p t_summary summary method_info class_info setter_map
              {
                code = partial.code;
                import = partial.import;
                variable = var_tl;
                score = partial.score;
                recv_package = partial.recv_package;
              }
            |> List.rev
          in
          all_statement
            (List.rev_append state_list tl)
            summary method_info class_info setter_map
      | [] ->
          [
            ( pretty_tc_format (partial.import, partial.code |> AST.remove_nt),
              tl );
          ])
  | [] -> []

(* find error entry *)
let rec find_ee e_method e_summary callgraph summary call_prop_map method_info =
  let propagation caller_method caller_preconds call_prop =
    let new_value, check_match =
      satisfy e_method e_summary call_prop method_info
    in
    if check_match then
      let new_call_prop = new_value_summary call_prop new_value in
      List.rev_append caller_preconds
        (find_ee caller_method new_call_prop callgraph summary call_prop_map
           method_info)
    else caller_preconds
  in
  if is_public e_method method_info then [ (e_method, e_summary) ]
  else
    let caller_list = CG.succ callgraph e_method in
    List.fold_left
      (fun list caller_method ->
        let caller_prop_list =
          match
            CallPropMap.M.find_opt (caller_method, e_method) call_prop_map
          with
          | None ->
              (* It is possible without any specific conditions *)
              find_ee caller_method Language.empty_summary callgraph summary
                call_prop_map method_info
          | Some prop_list ->
              List.fold_left
                (fun caller_preconds call_prop ->
                  propagation caller_method caller_preconds call_prop)
                [] prop_list
        in
        List.rev_append list caller_prop_list)
      [] caller_list

let init_stm ee_method ee_method_summary method_info class_info =
  let f_params =
    (MethodInfo.M.find ee_method method_info).MethodInfo.formal_params
  in
  let id, import =
    if is_static_method ee_method method_info then
      get_static_constructor ee_method (class_info |> fst)
    else if is_init_method ee_method then
      get_init_constructor ee_method method_info
    else (Some "gen1", "")
  in
  let e =
    if is_init_method ee_method then Str.split Regexp.dot ee_method |> List.hd
    else
      Str.split Regexp.dot ee_method
      |> List.tl |> List.hd
      |> Str.split (Str.regexp "(")
      |> List.hd
  in
  {
    code = AST.TestCase (STNT, { id; method_name = e; args = Param f_params });
    import = [ import ];
    variable = List.map (fun p -> (p, ee_method_summary)) f_params;
    score = 0;
    recv_package = get_import ee_method class_info;
  }

let mk_testcases ~is_start queue (e_method, error_summary)
    (callgraph, summary, call_prop_map, method_info, class_info, setter_map) =
  let init_stm_queue =
    if is_start then
      find_ee e_method error_summary callgraph summary call_prop_map method_info
      |> List.map (fun (ee, ee_s) -> init_stm ee ee_s method_info class_info)
    else queue
  in
  let result =
    all_statement init_stm_queue summary method_info class_info setter_map
  in
  if result = [] then (("", ""), []) else List.hd result
