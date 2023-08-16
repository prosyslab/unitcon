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
module IG = Inheritance.G
module AST = Language.AST

(* defining for constructor priority.
   if Range is wide then Range set 100 *)
type domain = Top | Range of (Value.value * Value.value) | Bot

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

let point value =
  match value with
  | Value.Eq _ -> 1.0
  | Neq _ | Le _ | Lt _ | Ge _ | Gt _ -> Float.div 1.0 100.0
  | Between (l, u) -> (
      match (l, u) with
      | Int l, Int u | Int l, Long u | Long l, Int u | Long l, Long u ->
          if u - l + 1 > 100 then Float.div 1.0 100.0
          else 1 / (u - l + 1) |> float_of_int
      | Float l, Float u
      | Float l, Double u
      | Double l, Float u
      | Double l, Double u ->
          if Float.add (Float.sub u l) 1.0 > 100.0 then Float.div 1.0 100.0
          else Float.div 1.0 (Float.add (Float.sub u l) 1.0)
      | _ -> 0.0)
  | Outside (u, l) -> (
      match (u, l) with
      | Int u, Int l | Int u, Long l | Long u, Int l | Long u, Long l ->
          if l - u + 1 > 100 then 1.0 else (l - u + 1) / 100 |> float_of_int
      | Float u, Float l
      | Float u, Double l
      | Double u, Float l
      | Double u, Double l ->
          if Float.add (Float.sub l u) 1.0 > 100.0 then 1.0
          else Float.div (Float.add (Float.sub l u) 1.0) 100.0
      | _ -> 0.0)

(* # of non-terminal for p + sum(point) *)
let match_score p =
  let rec summary_score s =
    match s with
    | AST.Assign (_, _, func, _) -> (
        match func with
        | AST.F f ->
            Value.M.fold
              (fun _ value accum -> Float.add (point value) accum)
              f.summary.Language.value 0.0
        | _ -> 0.0)
    | Void (_, func, _) -> (
        match func with
        | AST.F f ->
            Value.M.fold
              (fun _ value accum -> Float.add (point value) accum)
              f.summary.Language.value 0.0
        | _ -> 0.0)
    | Seq (s1, s2) -> Float.add (summary_score s1) (summary_score s2)
    | _ -> 0.0
  in
  summary_score p

let get_score p =
  let length = AST.count_nt p in
  let point = match_score p in
  (length, point)

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
          match Condition.M.find_opt (Condition.RH_Index field_name) sym with
          | Some idx_s -> get_tail_symbol field_name idx_s memory
          | None -> (
              match Condition.M.find_opt Condition.RH_Any sym with
              | Some any_sym -> get_tail_symbol field_name any_sym memory
              | None -> symbol)))
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

let is_primitive x =
  match AST.get_vinfo x |> fst with
  | Int | Long | Float | Double | Bool | Char | String -> true
  | _ -> false

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
  match (MethodInfo.M.find m_name m_info).MethodInfo.modifier with
  | Private -> true
  | _ -> false

let is_public m_name m_info =
  match (MethodInfo.M.find m_name m_info).MethodInfo.modifier with
  | Public -> true
  | _ -> false

let is_init_method method_name =
  Str.string_match (".*\\.<init>" |> Str.regexp) method_name 0

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
  let p_package = get_package_from_param info.MethodInfo.formal_params in
  let m_package = get_package_from_method method_name c_info in
  let package = if p_package = "" then m_package else p_package in
  let name =
    try
      Str.split Regexp.dot package
      |> List.rev |> List.hd
      |> Str.global_replace Regexp.dollar "\\$"
    with _ -> ""
  in
  let s = name ^ "$" in
  let package = Regexp.global_rm (Str.regexp s) package in
  if Str.string_match (Str.regexp package) package 0 then
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
        ]
    | Float | Double ->
        [
          AST.Primitive (R 1.0);
          AST.Primitive (R 0.0);
          AST.Primitive (R (-1.0));
          AST.Primitive (R 100.0);
          AST.Primitive (R (-100.0));
        ]
    | Bool -> [ AST.Primitive (B false); AST.Primitive (B true) ]
    | Char -> [ AST.Primitive (C 'x') ]
    | String -> [ AST.Primitive (S ""); AST.Primitive (S "string") ]
    | _ -> [ AST.Null ]
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
          AST.Primitive (Z (calc_z3 var [ z3exp ] |> int_of_string))
      | Float f | Double f ->
          let var = Z3.Arithmetic.Real.mk_const_s z3ctx id in
          let value =
            Z3.Arithmetic.Real.mk_numeral_s z3ctx (f |> string_of_float)
          in
          let z3exp = Z3.Boolean.mk_eq z3ctx var value in
          AST.Primitive (R (calc_z3 var [ z3exp ] |> float_of_string))
      | Bool b -> AST.Primitive (B b)
      | Char c -> AST.Primitive (C c)
      | String s -> AST.Primitive (S s)
      | Null -> AST.Null
      | _ -> failwith "not implemented eq")
  | Value.Neq v -> (
      match v with
      | Int i | Long i ->
          let var = Z3.Arithmetic.Integer.mk_const_s z3ctx id in
          let value = Z3.Arithmetic.Integer.mk_numeral_i z3ctx i in
          let z3exp =
            Z3.Boolean.mk_eq z3ctx var value |> Z3.Boolean.mk_not z3ctx
          in
          AST.Primitive (Z (calc_z3 var [ z3exp ] |> int_of_string))
      | Float f | Double f ->
          let var = Z3.Arithmetic.Real.mk_const_s z3ctx id in
          let value =
            Z3.Arithmetic.Real.mk_numeral_s z3ctx (f |> string_of_float)
          in
          let z3exp =
            Z3.Boolean.mk_eq z3ctx var value |> Z3.Boolean.mk_not z3ctx
          in
          AST.Primitive (R (calc_z3 var [ z3exp ] |> float_of_string))
      | Bool b -> AST.Primitive (B (b |> not))
      | String s -> AST.Primitive (S ("not_" ^ s))
      | Null -> AST.Primitive (S "not")
      | _ -> failwith "not implemented neq")
  | Value.Le v -> (
      match v with
      | Int i | Long i ->
          let var = Z3.Arithmetic.Integer.mk_const_s z3ctx id in
          let value = Z3.Arithmetic.Integer.mk_numeral_i z3ctx i in
          let z3exp = Z3.Arithmetic.mk_le z3ctx var value in
          AST.Primitive (Z (calc_z3 var [ z3exp ] |> int_of_string))
      | Float f | Double f ->
          let var = Z3.Arithmetic.Real.mk_const_s z3ctx id in
          let value =
            Z3.Arithmetic.Real.mk_numeral_s z3ctx (f |> string_of_float)
          in
          let z3exp = Z3.Arithmetic.mk_le z3ctx var value in
          AST.Primitive (R (calc_z3 var [ z3exp ] |> float_of_string))
      | _ -> failwith "not implemented le")
  | Value.Lt v -> (
      match v with
      | Int i | Long i ->
          let var = Z3.Arithmetic.Integer.mk_const_s z3ctx id in
          let value = Z3.Arithmetic.Integer.mk_numeral_i z3ctx i in
          let z3exp = Z3.Arithmetic.mk_lt z3ctx var value in
          AST.Primitive (Z (calc_z3 var [ z3exp ] |> int_of_string))
      | Float f | Double f ->
          let var = Z3.Arithmetic.Real.mk_const_s z3ctx id in
          let value =
            Z3.Arithmetic.Real.mk_numeral_s z3ctx (f |> string_of_float)
          in
          let z3exp = Z3.Arithmetic.mk_lt z3ctx var value in
          AST.Primitive (R (calc_z3 var [ z3exp ] |> float_of_string))
      | _ -> failwith "not implemented lt")
  | Value.Ge v -> (
      match v with
      | Int i | Long i ->
          let var = Z3.Arithmetic.Integer.mk_const_s z3ctx id in
          let value = Z3.Arithmetic.Integer.mk_numeral_i z3ctx i in
          let z3exp = Z3.Arithmetic.mk_ge z3ctx var value in
          AST.Primitive (Z (calc_z3 var [ z3exp ] |> int_of_string))
      | Float f | Double f ->
          let var = Z3.Arithmetic.Real.mk_const_s z3ctx id in
          let value =
            Z3.Arithmetic.Real.mk_numeral_s z3ctx (f |> string_of_float)
          in
          let z3exp = Z3.Arithmetic.mk_ge z3ctx var value in
          AST.Primitive (R (calc_z3 var [ z3exp ] |> float_of_string))
      | _ -> failwith "not implemented ge")
  | Value.Gt v -> (
      match v with
      | Int i | Long i ->
          let var = Z3.Arithmetic.Integer.mk_const_s z3ctx id in
          let value = Z3.Arithmetic.Integer.mk_numeral_i z3ctx i in
          let z3exp = Z3.Arithmetic.mk_gt z3ctx var value in
          AST.Primitive (Z (calc_z3 var [ z3exp ] |> int_of_string))
      | Float f | Double f ->
          let var = Z3.Arithmetic.Real.mk_const_s z3ctx id in
          let value =
            Z3.Arithmetic.Real.mk_numeral_s z3ctx (f |> string_of_float)
          in
          let z3exp = Z3.Arithmetic.mk_gt z3ctx var value in
          AST.Primitive (R (calc_z3 var [ z3exp ] |> float_of_string))
      | _ -> failwith "not implemented gt")
  | Value.Between (v1, v2) -> (
      match (v1, v2) with
      | Int i1, Int i2 | Long i1, Long i2 | Int i1, Long i2 | Long i1, Int i2 ->
          let var = Z3.Arithmetic.Integer.mk_const_s z3ctx id in
          let value1 = Z3.Arithmetic.Integer.mk_numeral_i z3ctx i1 in
          let value2 = Z3.Arithmetic.Integer.mk_numeral_i z3ctx i2 in
          let z3exp1 = Z3.Arithmetic.mk_ge z3ctx var value1 in
          let z3exp2 = Z3.Arithmetic.mk_le z3ctx var value2 in
          AST.Primitive (Z (calc_z3 var [ z3exp1; z3exp2 ] |> int_of_string))
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
          AST.Primitive (R (calc_z3 var [ z3exp1; z3exp2 ] |> float_of_string))
      | _ -> failwith "not implemented between")
  | Value.Outside (v1, v2) -> (
      match (v1, v2) with
      | Int i1, Int i2 | Long i1, Long i2 | Int i1, Long i2 | Long i1, Int i2 ->
          let var = Z3.Arithmetic.Integer.mk_const_s z3ctx id in
          let value1 = Z3.Arithmetic.Integer.mk_numeral_i z3ctx i1 in
          let value2 = Z3.Arithmetic.Integer.mk_numeral_i z3ctx i2 in
          let z3exp1 = Z3.Arithmetic.mk_lt z3ctx var value1 in
          let z3exp2 = Z3.Arithmetic.mk_gt z3ctx var value2 in
          AST.Primitive (Z (calc_z3 var [ z3exp1; z3exp2 ] |> int_of_string))
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
          AST.Primitive (R (calc_z3 var [ z3exp1; z3exp2 ] |> float_of_string))
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

let get_setter_list constructor m_info setter_map =
  let class_name = get_class_name ~infer:false constructor in
  (try SetterMap.M.find class_name setter_map with _ -> [])
  |> List.filter (fun setter -> is_private setter m_info |> not)

let get_setter constructor id method_summary c_summary m_info setter_map =
  if c_summary = Language.empty_summary then
    (FieldMap.M.empty, get_setter_list constructor m_info setter_map)
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
    (need_setter_field, get_setter_list constructor m_info setter_map)

let satisfied_c method_summary id candidate_constructor summary =
  let c_summarys = SummaryMap.M.find candidate_constructor summary in
  let method_symbols, method_memory = method_summary.Language.precond in
  let id = if id = "gen1" then "this" else id in
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
  let class_name = Str.split Regexp.dot class_name |> List.rev |> List.hd in
  let class_name = Str.global_replace Regexp.dollar "\\$" class_name in
  Str.string_match (class_name ^ "\\.<init>" |> Str.regexp) method_name 0

let match_return_object class_name method_name m_info =
  let class_name = Str.split Regexp.dot class_name |> List.rev |> List.hd in
  let c_method =
    try Str.split Regexp.dot method_name |> List.hd with _ -> ""
  in
  let info = MethodInfo.M.find method_name m_info in
  let return = info.MethodInfo.return in
  Str.string_match (Str.regexp class_name) return 0 && c_method <> return

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

let find_global_var_list c_name t_var mem summary m_info =
  let all_var s_trace =
    Condition.M.fold
      (fun head _ gvar_list ->
        match head with
        | Condition.RH_Var var ->
            AST.GlobalConstant (c_name ^ "." ^ var) :: gvar_list
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
                 | Some gv -> AST.GlobalConstant gv :: list
                 | None -> list))
              mem list
        | None ->
            (Condition.M.fold (fun _ s_trace list ->
                 List.rev_append (all_var s_trace) list))
              init_mem list
      else list)
    summary []

let global_var_list class_name t_summary summary m_info =
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
  | None -> find_global_var_list class_name None mem summary m_info
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

let mk_setter_format setter m_info =
  let m_info = MethodInfo.M.find setter m_info in
  let setter_statement =
    Str.split Regexp.dot setter
    |> List.tl |> List.hd
    |> Regexp.global_rm (Str.regexp "(.*)$")
  in
  (setter_statement, m_info.MethodInfo.formal_params)

let is_receiver id =
  let new_id1 = Str.replace_first (Str.regexp "con_recv") "" id in
  let new_id2 = Str.replace_first (Str.regexp "con_outer") "" id in
  if new_id1 = "" || new_id2 = "" then true else false

let mk_arg ~is_s param s =
  let param = if is_s then param else param |> List.tl in
  List.map
    (fun (i, v) ->
      incr new_var;
      AST.{ import = i; variable = (v, Some !new_var); summary = s })
    param

(* id is receiver variable *)
let get_void_func id ?(ee = "") ?(es = Language.empty_summary) m_info c_info
    s_map =
  if AST.is_id id then
    let param = (MethodInfo.M.find ee m_info).MethodInfo.formal_params in
    let f_arg = mk_arg ~is_s:(is_s_method ee m_info) param es in
    let import = get_package_from_method ee c_info in
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
  else
    let var = AST.get_v id in
    let name =
      get_class_name ~infer:false var.import
      |> String.split_on_char '.' |> List.rev |> List.hd
    in
    let setter_list =
      try SetterMap.M.find name s_map
      with _ -> [] |> List.filter (fun (s, _) -> is_private s m_info |> not)
    in
    List.map
      (fun (s, _) ->
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
          f_arg ))
      setter_list

let get_ret_obj (class_package, class_name) m_info (c_info, ig) =
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
          then
            (method_name, get_package_from_method method_name (c_info, ig))
            :: init_list
          else init_list)
        method_list class_to_find)
    m_info []

let satisfied_c_list id t_summary summary summary_list =
  if !Cmdline.basic_mode then
    List.fold_left
      (fun list (constructor, import) ->
        (constructor, Language.empty_summary, import) :: list)
      [] summary_list
  else
    List.fold_left
      (fun list (constructor, import) ->
        let check, summary = satisfied_c t_summary id constructor summary in
        if check then (constructor, summary, import) :: list else list)
      [] summary_list

let get_cfunc constructor m_info =
  let c, s, i = constructor in
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
  (func, AST.Arg arg)

let get_cfuncs list m_info =
  List.fold_left
    (fun lst (c, s, i) -> get_cfunc (c, s, i) m_info :: lst)
    [] list

let get_c ret summary m_info c_info =
  let class_name = AST.get_vinfo ret |> fst |> Language.get_class_name in
  if class_name = "" then []
  else
    let id = AST.get_vinfo ret |> snd in
    let package = (AST.get_v ret).import in
    let summary_filtering list =
      List.filter (fun (c, _, _) -> is_public_or_default c m_info c_info) list
      |> List.filter (fun (c, _, _) ->
             is_recursive_param class_name c m_info |> not)
    in
    let s_list =
      get_clist (package, class_name) m_info c_info
      |> satisfied_c_list id (AST.get_v ret).summary summary
      |> summary_filtering
    in
    get_cfuncs s_list m_info

let get_ret_c ret summary m_info c_info =
  let class_name = AST.get_vinfo ret |> fst |> Language.get_class_name in
  if class_name = "" then []
  else
    let id = AST.get_vinfo ret |> snd in
    let package = (AST.get_v ret).import in
    let summary_filtering list =
      List.filter (fun (c, _, _) -> is_public_or_default c m_info c_info) list
      |> List.filter (fun (c, _, _) ->
             is_recursive_param class_name c m_info |> not)
    in
    let s_list =
      get_ret_obj (package, class_name) m_info c_info
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

let rec unroll p summary m_info c_info s_map =
  match p with
  | AST.Seq _ when AST.void p -> [ AST.void_rule1 p; AST.void_rule2 p ]
  | Seq (s1, s2) when AST.ground s1 |> not ->
      let lst = unroll s1 summary m_info c_info s_map in
      List.map (fun x -> AST.Seq (x, s2)) lst
  | Seq (s1, s2) when AST.ground s2 |> not -> (
      match AST.last_code s1 with
      | AST.Assign (x0, x1, f, arg)
        when AST.void (AST.Seq (AST.Assign (x0, x1, f, arg), s2)) ->
          let lst =
            unroll (AST.Seq (AST.last_code s1, s2)) summary m_info c_info s_map
          in
          List.map (fun x -> AST.Seq (AST.modify_last_assign s1, x)) lst
      | _ ->
          let lst = unroll s2 summary m_info c_info s_map in
          List.map (fun x -> AST.Seq (s1, x)) lst)
  | Const (x, _) when AST.const p ->
      let typ, id = AST.get_vinfo x in
      if is_primitive x then
        List.fold_left
          (fun lst x1 -> AST.const_rule1 p x1 :: lst)
          []
          (get_value typ id (AST.get_v x).summary)
      else
        let r3 =
          List.fold_left
            (fun lst x1 ->
              match x1 with
              | AST.Primitive _ -> lst
              | _ -> AST.const_rule3 p :: lst)
            []
            (get_value typ id (AST.get_v x).summary)
        in
        let r2 =
          List.fold_left
            (fun lst x1 -> AST.const_rule2 p x1 :: lst)
            []
            (global_var_list
               (Language.get_class_name (AST.get_vinfo x |> fst))
               (AST.get_v x).summary summary m_info)
        in
        if is_receiver (AST.get_vinfo x |> snd) then r2
        else List.rev_append r3 r2
  | Assign (x0, _, _, _) when AST.fcall_in_assign p ->
      List.rev_append
        (get_c x0 summary m_info c_info)
        (get_ret_c x0 summary m_info c_info)
      |> List.map (fun x -> AST.fcall_in_assign_rule p (x |> fst) (x |> snd))
  | Void (x, _, _) when AST.fcall1_in_void p || AST.fcall2_in_void p ->
      get_void_func x m_info c_info s_map
      |> List.fold_left
           (fun lst (f, arg) -> AST.fcall_in_void_rule p f (AST.Arg arg) :: lst)
           []
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
        r2 :: [ r3 ])
      else if cname_condition (AST.get_func f).method_name m_info then
        [ get_cname f |> AST.recv_in_assign_rule1 p ]
      else
        let r2 = AST.recv_in_assign_rule2 p "con_recv" !recv in
        let r3 = AST.recv_in_assign_rule3 p "con_recv" !recv in
        incr recv;
        r2 :: [ r3 ]
  | Void (_, f, _) when AST.recv_in_void p ->
      if cname_condition (AST.get_func f).method_name m_info then
        [ get_cname f |> AST.recv_in_void_rule1 p ]
      else
        let r2 = AST.recv_in_void_rule2 p "con_recv" !recv in
        let r3 = AST.recv_in_void_rule3 p "con_recv" !recv in
        incr recv;
        r2 :: [ r3 ]
  | Assign (_, _, _, arg) when AST.arg_in_assign p ->
      let arg_seq =
        get_arg_seq (List.map (fun x -> AST.Variable x) (arg |> AST.get_arg))
      in
      List.map
        (fun x -> AST.arg_in_assign_rule p x (AST.Param (arg |> AST.get_arg)))
        arg_seq
  | Void (_, _, arg) when AST.arg_in_void p ->
      let arg_seq =
        get_arg_seq (List.map (fun x -> AST.Variable x) (arg |> AST.get_arg))
      in
      List.map
        (fun x -> AST.arg_in_void_rule p x (AST.Param (arg |> AST.get_arg)))
        arg_seq
  (* | AST.Stmt -> [ AST.Skip ] *)
  | _ -> [ p ]

(* find error entry *)
let rec find_ee e_method e_summary cg summary call_prop_map m_info =
  let propagation caller_method caller_preconds call_prop =
    let new_value, check_match = satisfy e_method e_summary call_prop m_info in
    if !Cmdline.basic_mode then
      ErrorEntrySet.union caller_preconds
        (find_ee caller_method Language.empty_summary cg summary call_prop_map
           m_info)
    else if check_match then
      let new_call_prop = new_value_summary call_prop new_value in
      ErrorEntrySet.union caller_preconds
        (find_ee caller_method new_call_prop cg summary call_prop_map m_info)
    else caller_preconds
  in
  if is_public e_method m_info then
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
                call_prop_map m_info
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
      let s1 = get_score p1 in
      let s2 = get_score p2 in
      if compare (s1 |> fst) (s2 |> fst) <> 0 then
        compare (s1 |> fst) (s2 |> fst)
      else compare (s2 |> snd) (s1 |> snd))
    queue

let rec mk_testcase queue summary m_info c_info s_map =
  let queue = priority_q queue in
  match queue with
  | p :: tl ->
      if AST.ground p then [ (pretty_format p, tl) ]
      else
        mk_testcase
          (List.rev_append
             (unroll p summary m_info c_info s_map |> List.rev)
             tl)
          summary m_info c_info s_map
  | [] -> []

let mk_testcases ~is_start queue (e_method, error_summary)
    (cg, summary, call_prop_map, m_info, c_info, s_map) =
  let apply_rule list =
    List.fold_left
      (fun lst (func, arg) ->
        AST.fcall_in_void_rule (AST.Void (Id, Func, Arg [])) func (AST.Arg arg)
        :: lst)
      [] list
  in
  let init =
    if is_start then
      ErrorEntrySet.fold
        (fun (ee, ee_s) init_list ->
          apply_rule (get_void_func AST.Id ~ee ~es:ee_s m_info c_info s_map)
          |> List.rev_append init_list)
        (find_ee e_method error_summary cg summary call_prop_map m_info)
        []
    else queue
  in
  let result = mk_testcase init summary m_info c_info s_map in
  if result = [] then (("", ""), []) else List.hd result
