module Relation = Language.Relation
module Value = Language.Value
module Condition = Language.Condition
module MethodInfo = Language.MethodInfo
module SummaryMap = Language.SummaryMap
module CallPropMap = Language.CallPropMap
module ClassTypeInfo = Language.ClassTypeInfo
module CG = Callgraph.G
module HG = Hierarchy.G

module ImportSet = Set.Make (struct
  type t = string

  let compare = compare
end)

let z3ctx =
  Z3.mk_context
    [
      ("model", "true");
      ("proof", "true");
      ("dump_models", "true");
      ("unsat_core", "true");
    ]

let solver = Z3.Solver.mk_solver z3ctx None

let rm_exp exp str = Str.global_replace exp "" str

let rec find_relation given_symbol relation =
  match Relation.M.find_opt given_symbol relation with
  | Some find_symbol -> find_relation find_symbol relation
  | None -> given_symbol

let get_symbol_list values =
  Value.M.fold (fun symbol _ symbol_list -> symbol :: symbol_list) values []

(* memory: Condition.mem *)
(* return: (callee_actual_symbol * head_symbol) list *)
(* if head = "" then this symbol can be any value *)
let get_head_symbol_list symbols (_, memory) =
  let get_head_symbol symbol memory =
    Condition.M.fold
      (fun head trace head_list ->
        let head = match head with Condition.RH_Symbol s -> s | _ -> "" in
        Condition.M.fold
          (fun _ trace_tail head_list ->
            match trace_tail with
            | Condition.RH_Symbol s when symbol = s ->
                (symbol, head) :: head_list
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
    let variable =
      match Condition.M.find (Condition.RH_Symbol head_symbol) variables with
      | Condition.RH_Var v -> v
      | _ -> ""
    in
    let index =
      let rec get_index count params =
        match params with
        | hd :: tl -> (
            match hd |> snd with
            | Language.This _ -> get_index (count + 1) tl
            | Var (_, id) ->
                if id = variable then count else get_index (count + 1) tl)
        | [] -> failwith "not found param"
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

let check_intersect_value_list caller_prop callee_summary value_symbol_list =
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
          if eq_v1 = eq_v2 then (caller_prop.Language.value, true)
          else (caller_prop.Language.value, false)
      | Eq eq_v, Neq neq_v | Neq neq_v, Eq eq_v ->
          if eq_v = neq_v then (caller_prop.Language.value, false)
          else (caller_prop.Language.value, true)
      | Eq eq_v, Le le_v | Le le_v, Eq eq_v -> (
          match (eq_v, le_v) with
          | Int eq_int, Int le_int
          | Long eq_int, Long le_int
          | Int eq_int, Long le_int
          | Long eq_int, Int le_int ->
              if eq_int <= le_int then (caller_prop.Language.value, true)
              else (caller_prop.Language.value, false)
          | Float eq_float, Float le_float
          | Double eq_float, Double le_float
          | Float eq_float, Double le_float
          | Double eq_float, Float le_float ->
              if eq_float <= le_float then (caller_prop.Language.value, true)
              else (caller_prop.Language.value, false)
          | _ -> failwith "not allowed type in eq, le")
      | Eq eq_v, Lt lt_v | Lt lt_v, Eq eq_v -> (
          match (eq_v, lt_v) with
          | Int eq_int, Int lt_int
          | Long eq_int, Long lt_int
          | Int eq_int, Long lt_int
          | Long eq_int, Int lt_int ->
              if eq_int < lt_int then (caller_prop.Language.value, true)
              else (caller_prop.Language.value, false)
          | Float eq_float, Float lt_float
          | Double eq_float, Double lt_float
          | Float eq_float, Double lt_float
          | Double eq_float, Float lt_float ->
              if eq_float < lt_float then (caller_prop.Language.value, true)
              else (caller_prop.Language.value, false)
          | _ -> failwith "not allowed type in eq, lt")
      | Eq eq_v, Ge ge_v | Ge ge_v, Eq eq_v -> (
          match (eq_v, ge_v) with
          | Int eq_int, Int ge_int
          | Long eq_int, Long ge_int
          | Int eq_int, Long ge_int
          | Long eq_int, Int ge_int ->
              if eq_int >= ge_int then (caller_prop.Language.value, true)
              else (caller_prop.Language.value, false)
          | Float eq_float, Float ge_float
          | Double eq_float, Double ge_float
          | Float eq_float, Double ge_float
          | Double eq_float, Float ge_float ->
              if eq_float >= ge_float then (caller_prop.Language.value, true)
              else (caller_prop.Language.value, false)
          | _ -> failwith "not allowed type in eq, ge")
      | Eq eq_v, Gt gt_v | Gt gt_v, Eq eq_v -> (
          match (eq_v, gt_v) with
          | Int eq_int, Int gt_int
          | Long eq_int, Long gt_int
          | Int eq_int, Long gt_int
          | Long eq_int, Int gt_int ->
              if eq_int > gt_int then (caller_prop.Language.value, true)
              else (caller_prop.Language.value, false)
          | Float eq_float, Float gt_float
          | Double eq_float, Double gt_float
          | Float eq_float, Double gt_float
          | Double eq_float, Float gt_float ->
              if eq_float > gt_float then (caller_prop.Language.value, true)
              else (caller_prop.Language.value, false)
          | _ -> failwith "not allowed type in eq, gt")
      | Eq eq_v, Between (btw_min, btw_max)
      | Between (btw_min, btw_max), Eq eq_v -> (
          match (eq_v, btw_min, btw_max) with
          | Int eq_int, Int btw_min_int, Int btw_max_int
          | Int eq_int, Int btw_min_int, Long btw_max_int
          | Int eq_int, Long btw_min_int, Int btw_max_int
          | Int eq_int, Long btw_min_int, Long btw_max_int
          | Long eq_int, Int btw_min_int, Int btw_max_int
          | Long eq_int, Int btw_min_int, Long btw_max_int
          | Long eq_int, Long btw_min_int, Int btw_max_int
          | Long eq_int, Long btw_min_int, Long btw_max_int ->
              if eq_int >= btw_min_int && eq_int <= btw_max_int then
                (caller_prop.Language.value, true)
              else (caller_prop.Language.value, false)
          | Float eq_float, Float btw_min_float, Float btw_max_float
          | Float eq_float, Float btw_min_float, Double btw_max_float
          | Float eq_float, Double btw_min_float, Float btw_max_float
          | Float eq_float, Double btw_min_float, Double btw_max_float
          | Double eq_float, Float btw_min_float, Float btw_max_float
          | Double eq_float, Float btw_min_float, Double btw_max_float
          | Double eq_float, Double btw_min_float, Float btw_max_float
          | Double eq_float, Double btw_min_float, Double btw_max_float ->
              if eq_float >= btw_min_float && eq_float <= btw_max_float then
                (caller_prop.Language.value, true)
              else (caller_prop.Language.value, false)
          | _ -> failwith "not allowed type in eq, between")
      | Eq eq_v, Outside (out_min, out_max)
      | Outside (out_min, out_max), Eq eq_v -> (
          match (eq_v, out_min, out_max) with
          | Int eq_int, Int out_min_int, Int out_max_int
          | Int eq_int, Int out_min_int, Long out_max_int
          | Int eq_int, Long out_min_int, Int out_max_int
          | Int eq_int, Long out_min_int, Long out_max_int
          | Long eq_int, Int out_min_int, Int out_max_int
          | Long eq_int, Int out_min_int, Long out_max_int
          | Long eq_int, Long out_min_int, Int out_max_int
          | Long eq_int, Long out_min_int, Long out_max_int ->
              if eq_int < out_min_int && eq_int > out_max_int then
                (caller_prop.Language.value, true)
              else (caller_prop.Language.value, false)
          | Float eq_float, Float out_min_float, Float out_max_float
          | Float eq_float, Float out_min_float, Double out_max_float
          | Float eq_float, Double out_min_float, Float out_max_float
          | Float eq_float, Double out_min_float, Double out_max_float
          | Double eq_float, Float out_min_float, Float out_max_float
          | Double eq_float, Float out_min_float, Double out_max_float
          | Double eq_float, Double out_min_float, Float out_max_float
          | Double eq_float, Double out_min_float, Double out_max_float ->
              if eq_float < out_min_float && eq_float > out_max_float then
                (caller_prop.Language.value, true)
              else (caller_prop.Language.value, false)
          | _ -> failwith "not allowed type in eq, outside")
      | Le le_v, Ge ge_v | Ge ge_v, Le le_v -> (
          match (le_v, ge_v) with
          | Int le_int, Int ge_int
          | Long le_int, Long ge_int
          | Int le_int, Long ge_int
          | Long le_int, Int ge_int ->
              if le_int >= ge_int then (caller_prop.Language.value, true)
              else (caller_prop.Language.value, false)
          | Float le_float, Float ge_float
          | Double le_float, Double ge_float
          | Float le_float, Double ge_float
          | Double le_float, Float ge_float ->
              if le_float >= ge_float then (caller_prop.Language.value, true)
              else (caller_prop.Language.value, false)
          | _ -> failwith "not allowed type in le, ge")
      | Le l_v, Gt g_v
      | Lt l_v, Ge g_v
      | Lt l_v, Gt g_v
      | Ge g_v, Lt l_v
      | Gt g_v, Le l_v
      | Gt g_v, Lt l_v -> (
          match (l_v, g_v) with
          | Int l_int, Int g_int
          | Long l_int, Long g_int
          | Int l_int, Long g_int
          | Long l_int, Int g_int ->
              if l_int > g_int then (caller_prop.Language.value, true)
              else (caller_prop.Language.value, false)
          | Float l_float, Float g_float
          | Double l_float, Double g_float
          | Float l_float, Double g_float
          | Double l_float, Float g_float ->
              if l_float > g_float then (caller_prop.Language.value, true)
              else (caller_prop.Language.value, false)
          | _ -> failwith "not allowed type in le, ge")
      | Le le_v, Between (btw_min, btw_max)
      | Between (btw_min, btw_max), Le le_v -> (
          match (le_v, btw_min, btw_max) with
          | Int le_int, Int btw_min_int, Int _
          | Int le_int, Int btw_min_int, Long _
          | Long le_int, Long btw_min_int, Int _
          | Long le_int, Long btw_min_int, Long _
          | Int le_int, Long btw_min_int, Int _
          | Int le_int, Long btw_min_int, Long _
          | Long le_int, Int btw_min_int, Int _
          | Long le_int, Int btw_min_int, Long _ ->
              if le_int < btw_min_int then (caller_prop.Language.value, false)
              else (caller_prop.Language.value, true)
          | Float le_float, Float btw_min_float, Float _
          | Float le_float, Float btw_min_float, Double _
          | Double le_float, Double btw_min_float, Float _
          | Double le_float, Double btw_min_float, Double _
          | Float le_float, Double btw_min_float, Float _
          | Float le_float, Double btw_min_float, Double _
          | Double le_float, Float btw_min_float, Float _
          | Double le_float, Float btw_min_float, Double _ ->
              if le_float < btw_min_float then
                (caller_prop.Language.value, false)
              else (caller_prop.Language.value, true)
          | _ -> failwith "not allowed type in le, between")
      | Lt lt_v, Between (btw_min, btw_max)
      | Between (btw_min, btw_max), Lt lt_v -> (
          match (lt_v, btw_min, btw_max) with
          | Int lt_int, Int btw_min_int, Int _
          | Int lt_int, Int btw_min_int, Long _
          | Long lt_int, Long btw_min_int, Int _
          | Long lt_int, Long btw_min_int, Long _
          | Int lt_int, Long btw_min_int, Int _
          | Int lt_int, Long btw_min_int, Long _
          | Long lt_int, Int btw_min_int, Int _
          | Long lt_int, Int btw_min_int, Long _ ->
              if lt_int <= btw_min_int then (caller_prop.Language.value, false)
              else (caller_prop.Language.value, true)
          | Float lt_float, Float btw_min_float, Float _
          | Float lt_float, Float btw_min_float, Double _
          | Double lt_float, Double btw_min_float, Float _
          | Double lt_float, Double btw_min_float, Double _
          | Float lt_float, Double btw_min_float, Float _
          | Float lt_float, Double btw_min_float, Double _
          | Double lt_float, Float btw_min_float, Float _
          | Double lt_float, Float btw_min_float, Double _ ->
              if lt_float <= btw_min_float then
                (caller_prop.Language.value, false)
              else (caller_prop.Language.value, true)
          | _ -> failwith "not allowed type in lt, between")
      | Ge ge_v, Between (btw_min, btw_max)
      | Between (btw_min, btw_max), Ge ge_v -> (
          match (ge_v, btw_min, btw_max) with
          | Int ge_int, Int _, Int btw_max_int
          | Int ge_int, Long _, Int btw_max_int
          | Long ge_int, Int _, Long btw_max_int
          | Long ge_int, Long _, Long btw_max_int
          | Int ge_int, Int _, Long btw_max_int
          | Int ge_int, Long _, Long btw_max_int
          | Long ge_int, Int _, Int btw_max_int
          | Long ge_int, Long _, Int btw_max_int ->
              if ge_int > btw_max_int then (caller_prop.Language.value, false)
              else (caller_prop.Language.value, true)
          | Float ge_float, Float _, Float btw_max_float
          | Float ge_float, Double _, Float btw_max_float
          | Double ge_float, Float _, Double btw_max_float
          | Double ge_float, Double _, Double btw_max_float
          | Float ge_float, Float _, Double btw_max_float
          | Float ge_float, Double _, Double btw_max_float
          | Double ge_float, Float _, Float btw_max_float
          | Double ge_float, Double _, Float btw_max_float ->
              if ge_float > btw_max_float then
                (caller_prop.Language.value, false)
              else (caller_prop.Language.value, true)
          | _ -> failwith "not allowed type in ge, between")
      | Gt gt_v, Between (btw_min, btw_max)
      | Between (btw_min, btw_max), Gt gt_v -> (
          match (gt_v, btw_min, btw_max) with
          | Int gt_int, Int _, Int btw_max_int
          | Int gt_int, Long _, Int btw_max_int
          | Long gt_int, Int _, Long btw_max_int
          | Long gt_int, Long _, Long btw_max_int
          | Int gt_int, Int _, Long btw_max_int
          | Int gt_int, Long _, Long btw_max_int
          | Long gt_int, Int _, Int btw_max_int
          | Long gt_int, Long _, Int btw_max_int ->
              if gt_int >= btw_max_int then (caller_prop.Language.value, false)
              else (caller_prop.Language.value, true)
          | Float gt_float, Float _, Float btw_max_float
          | Float gt_float, Double _, Float btw_max_float
          | Double gt_float, Float _, Double btw_max_float
          | Double gt_float, Double _, Double btw_max_float
          | Float gt_float, Float _, Double btw_max_float
          | Float gt_float, Double _, Double btw_max_float
          | Double gt_float, Float _, Float btw_max_float
          | Double gt_float, Double _, Float btw_max_float ->
              if gt_float >= btw_max_float then
                (caller_prop.Language.value, false)
              else (caller_prop.Language.value, true)
          | _ -> failwith "not allowed type in gt, between")
      | Between (caller_min, caller_max), Between (callee_min, callee_max) -> (
          match (caller_min, caller_max, callee_min, callee_max) with
          | ( Int caller_min_int,
              Int caller_max_int,
              Int callee_min_int,
              Int callee_max_int )
          | ( Int caller_min_int,
              Int caller_max_int,
              Int callee_min_int,
              Long callee_max_int )
          | ( Int caller_min_int,
              Int caller_max_int,
              Long callee_min_int,
              Int callee_max_int )
          | ( Int caller_min_int,
              Long caller_max_int,
              Int callee_min_int,
              Int callee_max_int )
          | ( Int caller_min_int,
              Int caller_max_int,
              Long callee_min_int,
              Long callee_max_int )
          | ( Int caller_min_int,
              Long caller_max_int,
              Int callee_min_int,
              Long callee_max_int )
          | ( Int caller_min_int,
              Long caller_max_int,
              Long callee_min_int,
              Int callee_max_int )
          | ( Int caller_min_int,
              Long caller_max_int,
              Long callee_min_int,
              Long callee_max_int )
          | ( Long caller_min_int,
              Int caller_max_int,
              Int callee_min_int,
              Int callee_max_int )
          | ( Long caller_min_int,
              Int caller_max_int,
              Int callee_min_int,
              Long callee_max_int )
          | ( Long caller_min_int,
              Int caller_max_int,
              Long callee_min_int,
              Int callee_max_int )
          | ( Long caller_min_int,
              Long caller_max_int,
              Int callee_min_int,
              Int callee_max_int )
          | ( Long caller_min_int,
              Int caller_max_int,
              Long callee_min_int,
              Long callee_max_int )
          | ( Long caller_min_int,
              Long caller_max_int,
              Int callee_min_int,
              Long callee_max_int )
          | ( Long caller_min_int,
              Long caller_max_int,
              Long callee_min_int,
              Int callee_max_int )
          | ( Long caller_min_int,
              Long caller_max_int,
              Long callee_min_int,
              Long callee_max_int ) ->
              if
                caller_max_int < callee_min_int
                || callee_max_int < caller_min_int
              then (caller_prop.Language.value, false)
              else (caller_prop.Language.value, true)
          | ( Float caller_min_float,
              Float caller_max_float,
              Float callee_min_float,
              Float callee_max_float )
          | ( Float caller_min_float,
              Float caller_max_float,
              Float callee_min_float,
              Double callee_max_float )
          | ( Float caller_min_float,
              Float caller_max_float,
              Double callee_min_float,
              Float callee_max_float )
          | ( Float caller_min_float,
              Double caller_max_float,
              Float callee_min_float,
              Float callee_max_float )
          | ( Float caller_min_float,
              Float caller_max_float,
              Double callee_min_float,
              Double callee_max_float )
          | ( Float caller_min_float,
              Double caller_max_float,
              Float callee_min_float,
              Double callee_max_float )
          | ( Float caller_min_float,
              Double caller_max_float,
              Double callee_min_float,
              Float callee_max_float )
          | ( Float caller_min_float,
              Double caller_max_float,
              Double callee_min_float,
              Double callee_max_float )
          | ( Double caller_min_float,
              Float caller_max_float,
              Float callee_min_float,
              Float callee_max_float )
          | ( Double caller_min_float,
              Float caller_max_float,
              Float callee_min_float,
              Double callee_max_float )
          | ( Double caller_min_float,
              Float caller_max_float,
              Double callee_min_float,
              Float callee_max_float )
          | ( Double caller_min_float,
              Double caller_max_float,
              Float callee_min_float,
              Float callee_max_float )
          | ( Double caller_min_float,
              Float caller_max_float,
              Double callee_min_float,
              Double callee_max_float )
          | ( Double caller_min_float,
              Double caller_max_float,
              Float callee_min_float,
              Double callee_max_float )
          | ( Double caller_min_float,
              Double caller_max_float,
              Double callee_min_float,
              Float callee_max_float )
          | ( Double caller_min_float,
              Double caller_max_float,
              Double callee_min_float,
              Double callee_max_float ) ->
              if
                caller_max_float < callee_min_float
                || callee_max_float < caller_min_float
              then (caller_prop.Language.value, false)
              else (caller_prop.Language.value, true)
          | _ -> failwith "not allowed type in between, between")
      | Between (btw_min, btw_max), Outside (out_min, out_max)
      | Outside (out_min, out_max), Between (btw_min, btw_max) -> (
          match (btw_min, btw_max, out_min, out_max) with
          | Int btw_min_int, Int btw_max_int, Int out_min_int, Int out_max_int
          | Int btw_min_int, Int btw_max_int, Int out_min_int, Long out_max_int
          | Int btw_min_int, Int btw_max_int, Long out_min_int, Int out_max_int
          | Int btw_min_int, Long btw_max_int, Int out_min_int, Int out_max_int
          | Int btw_min_int, Int btw_max_int, Long out_min_int, Long out_max_int
          | Int btw_min_int, Long btw_max_int, Int out_min_int, Long out_max_int
          | Int btw_min_int, Long btw_max_int, Long out_min_int, Int out_max_int
          | ( Int btw_min_int,
              Long btw_max_int,
              Long out_min_int,
              Long out_max_int )
          | Long btw_min_int, Int btw_max_int, Int out_min_int, Int out_max_int
          | Long btw_min_int, Int btw_max_int, Int out_min_int, Long out_max_int
          | Long btw_min_int, Int btw_max_int, Long out_min_int, Int out_max_int
          | Long btw_min_int, Long btw_max_int, Int out_min_int, Int out_max_int
          | ( Long btw_min_int,
              Int btw_max_int,
              Long out_min_int,
              Long out_max_int )
          | ( Long btw_min_int,
              Long btw_max_int,
              Int out_min_int,
              Long out_max_int )
          | ( Long btw_min_int,
              Long btw_max_int,
              Long out_min_int,
              Int out_max_int )
          | ( Long btw_min_int,
              Long btw_max_int,
              Long out_min_int,
              Long out_max_int ) ->
              if out_min_int <= btw_min_int && out_max_int >= btw_max_int then
                (caller_prop.Language.value, false)
              else (caller_prop.Language.value, true)
          | ( Float btw_min_float,
              Float btw_max_float,
              Float out_min_float,
              Float out_max_float )
          | ( Float btw_min_float,
              Float btw_max_float,
              Float out_min_float,
              Double out_max_float )
          | ( Float btw_min_float,
              Float btw_max_float,
              Double out_min_float,
              Float out_max_float )
          | ( Float btw_min_float,
              Double btw_max_float,
              Float out_min_float,
              Float out_max_float )
          | ( Float btw_min_float,
              Float btw_max_float,
              Double out_min_float,
              Double out_max_float )
          | ( Float btw_min_float,
              Double btw_max_float,
              Float out_min_float,
              Double out_max_float )
          | ( Float btw_min_float,
              Double btw_max_float,
              Double out_min_float,
              Float out_max_float )
          | ( Float btw_min_float,
              Double btw_max_float,
              Double out_min_float,
              Double out_max_float )
          | ( Double btw_min_float,
              Float btw_max_float,
              Float out_min_float,
              Float out_max_float )
          | ( Double btw_min_float,
              Float btw_max_float,
              Float out_min_float,
              Double out_max_float )
          | ( Double btw_min_float,
              Float btw_max_float,
              Double out_min_float,
              Float out_max_float )
          | ( Double btw_min_float,
              Double btw_max_float,
              Float out_min_float,
              Float out_max_float )
          | ( Double btw_min_float,
              Float btw_max_float,
              Double out_min_float,
              Double out_max_float )
          | ( Double btw_min_float,
              Double btw_max_float,
              Float out_min_float,
              Double out_max_float )
          | ( Double btw_min_float,
              Double btw_max_float,
              Double out_min_float,
              Float out_max_float )
          | ( Double btw_min_float,
              Double btw_max_float,
              Double out_min_float,
              Double out_max_float ) ->
              if
                btw_min_float <= out_min_float && btw_max_float >= out_max_float
              then (caller_prop.Language.value, false)
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
      with Not_found -> (caller_prop.Language.value, true))
  in
  List.map
    (fun (caller_symbol, callee_symbol) ->
      check_intersect_value caller_symbol callee_symbol)
    value_symbol_list

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
      check_intersect_value_list call_prop callee_summary value_symbol_list
    in
    let values =
      List.fold_left
        (fun prop_values (prop_value, _) ->
          Value.M.merge
            (fun _ v1 v2 ->
              match (v1, v2) with
              | None, None -> None
              | Some _, _ -> v1
              | None, Some _ -> v2)
            prop_values prop_value)
        call_prop.Language.value values_and_check
    in
    let check = List.filter (fun (_, c) -> c = false) values_and_check in
    (values, check)
  in
  let values, check = intersect_value in
  if List.length check <> 0 then (values, false) else (values, true)

let is_public s_method method_info =
  let s_method_info = MethodInfo.M.find s_method method_info in
  match s_method_info.MethodInfo.modifier with Public -> true | _ -> false

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
          | None -> list
          | Some prop_list ->
              List.fold_left
                (fun caller_preconds call_prop ->
                  let new_value, check_match =
                    match_precond s_method source_summary call_prop method_info
                  in
                  if check_match then
                    let old_call_prop = call_prop in
                    let new_call_prop =
                      Language.
                        {
                          relation = old_call_prop.relation;
                          value = new_value;
                          precond = old_call_prop.precond;
                          postcond = old_call_prop.postcond;
                          args = old_call_prop.args;
                        }
                    in
                    List.rev_append
                      (find_ps_method caller_method new_call_prop call_graph
                         summary call_prop_map method_info)
                      caller_preconds
                  else caller_preconds)
                [] prop_list
        in
        list @ caller_prop_list)
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
        let symbol = match symbol with Condition.RH_Symbol s -> s | _ -> "" in
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
    | Language.Int -> Value.Eq (Int 0)
    | Language.Long -> Value.Eq (Long 0)
    | Language.Float -> Value.Eq (Float 0.0)
    | Language.Double -> Value.Eq (Double 0.0)
    | Language.Bool -> Value.Eq (Bool false)
    | Language.Char -> Value.Eq (Char 'x')
    | Language.String -> Value.Eq (String "string")
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

let check_correct_constructor method_summary id candidate_constructor summary =
  let constructor_summarys = SummaryMap.M.find candidate_constructor summary in
  let method_symbols, method_memory = method_summary.Language.precond in
  let target_symbol =
    Condition.M.fold
      (fun symbol precond_id target ->
        let symbol = match symbol with Condition.RH_Symbol s -> s | _ -> "" in
        match precond_id with
        | Condition.RH_Var pre_id when pre_id = id -> symbol
        | _ -> target)
      method_symbols ""
  in
  if target_symbol = "" then (true, constructor_summarys |> List.hd)
  else
    let target_symbol =
      Condition.M.fold
        (fun symbol trace target ->
          let symbol =
            match symbol with Condition.RH_Symbol s -> s | _ -> ""
          in
          if symbol = target_symbol then
            Condition.M.fold
              (fun _ trace_tail find_target ->
                match trace_tail with
                | Condition.RH_Symbol s -> s
                | _ -> find_target)
              trace target
          else target)
        method_memory ""
    in
    let target_symbol =
      find_relation target_symbol method_summary.Language.relation
    in
    let check_summarys =
      List.map
        (fun c_summary ->
          let c_target_symbol =
            Condition.M.fold
              (fun symbol p_id target ->
                let symbol =
                  match symbol with Condition.RH_Symbol s -> s | _ -> ""
                in
                match p_id with
                | Condition.RH_Var pre_id when pre_id = "this" -> symbol
                | _ -> target)
              (c_summary.Language.postcond |> fst)
              ""
          in
          ( check_intersect_value_list method_summary c_summary
              [ (target_symbol, c_target_symbol) ],
            c_summary ))
        constructor_summarys
    in
    List.fold_left
      (fun check_value (check_summary, c_summary) ->
        let check = List.filter (fun (_, c) -> c = false) check_summary in
        if List.length check <> 0 then check_value else (true, c_summary))
      ( false,
        Language.
          {
            relation = Relation.M.empty;
            value = Value.M.empty;
            precond = (Condition.M.empty, Condition.M.empty);
            postcond = (Condition.M.empty, Condition.M.empty);
            args = [];
          } )
      check_summarys

let is_normal_class class_name class_type_info =
  match ClassTypeInfo.M.find_opt class_name class_type_info with
  | Some typ -> (
      match typ with Language.Static | Language.Normal -> true | _ -> false)
  | None -> true

let is_private method_name method_info =
  let info = MethodInfo.M.find method_name method_info in
  match info.MethodInfo.modifier with Private -> true | _ -> false

let match_constructor_name class_name method_name =
  Str.string_match (class_name ^ "\\.<init>" |> Str.regexp) method_name 0

let get_constructor_list class_name method_info (class_info, hierarchy_graph) =
  let class_to_find =
    try HG.succ hierarchy_graph class_name |> List.cons class_name
    with Invalid_argument _ -> [ class_name ]
  in
  MethodInfo.M.fold
    (fun method_name _ method_list ->
      List.fold_left
        (fun init_list class_name_to_find ->
          if is_normal_class class_name_to_find class_info then
            if match_constructor_name class_name_to_find method_name then
              method_name :: init_list
            else init_list
          else init_list)
        method_list class_to_find)
    method_info []

let get_class_initializer_list class_name target_summary method_info =
  let variables, mem = target_summary.Language.precond in
  let target_variable =
    Condition.M.fold
      (fun symbol variable find_variable ->
        let symbol = match symbol with Condition.RH_Symbol s -> s | _ -> "" in
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
        let symbol = match symbol with Condition.RH_Symbol s -> s | _ -> "" in
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
    (fun (k1, _) (k2, _) ->
      let k1_info = MethodInfo.M.find k1 method_info in
      let k1_formal = k1_info.MethodInfo.formal_params |> List.length in
      let k2_info = MethodInfo.M.find k2 method_info in
      let k2_formal = k2_info.MethodInfo.formal_params |> List.length in
      compare k1_formal k2_formal)
    constructor_list

let rec get_statement param target_summary summary method_info class_info =
  let get_constructor class_name id target_summary summary method_info =
    let constr_summary_list =
      get_constructor_list class_name method_info class_info
    in
    let constr_summary_list =
      List.fold_left
        (fun list constructor ->
          let check, summary =
            check_correct_constructor target_summary id constructor summary
          in
          if check then (constructor, summary) :: list else list)
        [] constr_summary_list
    in
    if List.length constr_summary_list = 0 then
      let class_initializer =
        get_class_initializer_list class_name target_summary method_info
      in
      if class_initializer = "" then
        (class_name ^ " " ^ id ^ " = new " ^ class_name ^ "();", [])
      else (class_name ^ " " ^ id ^ " = " ^ class_initializer ^ ";", [])
    else
      let constructor =
        sort_constructor_list constr_summary_list method_info |> List.hd |> fst
      in
      let constructor_info = MethodInfo.M.find constructor method_info in
      let constructor_params = constructor_info.MethodInfo.formal_params in
      let constructor_summary = List.hd constr_summary_list |> snd in
      let constructor =
        let param_list =
          List.fold_left
            (fun param_code (_, param) ->
              match param with
              | Language.This _ -> param_code
              | Language.Var (_, id) -> param_code ^ ", " ^ id)
            "" constructor_params
        in
        let param_list = rm_exp (Str.regexp "^, ") param_list in
        let constructor =
          Str.replace_first (Str.regexp ".<init>") "" constructor
          |> rm_exp (Str.regexp "(.*)$")
        in
        constructor ^ "(" ^ param_list ^ ")"
      in
      let constructor_import =
        List.fold_left
          (fun this_import param ->
            match param with
            | import, Language.This _ -> import
            | _ -> this_import)
          "" constructor_info.formal_params
      in
      if List.length constructor_params = 1 then
        ( class_name ^ " " ^ id ^ " = new " ^ constructor ^ ";",
          [ constructor_import ] )
      else
        let code, import_list =
          List.fold_left_map
            (fun constructor_code param ->
              let import, code =
                get_statement param constructor_summary summary method_info
                  class_info
              in
              (code ^ "\n" ^ constructor_code, import))
            (class_name ^ " " ^ id ^ " = new " ^ constructor ^ ";")
            (List.tl constructor_params)
        in
        (code, import_list |> List.flatten |> List.cons constructor_import)
  in
  match param |> snd with
  | Language.This typ -> (
      match typ with
      | Int ->
          let code, import_list =
            get_constructor "int" "gen1" target_summary summary method_info
          in
          ((param |> fst) :: import_list, code)
      | Long ->
          let code, import_list =
            get_constructor "long" "gen1" target_summary summary method_info
          in
          ((param |> fst) :: import_list, code)
      | Float ->
          let code, import_list =
            get_constructor "float" "gen1" target_summary summary method_info
          in
          ((param |> fst) :: import_list, code)
      | Double ->
          let code, import_list =
            get_constructor "double" "gen1" target_summary summary method_info
          in
          ((param |> fst) :: import_list, code)
      | Bool ->
          let code, import_list =
            get_constructor "bool" "gen1" target_summary summary method_info
          in
          ((param |> fst) :: import_list, code)
      | Char ->
          let code, import_list =
            get_constructor "char" "gen1" target_summary summary method_info
          in
          ((param |> fst) :: import_list, code)
      | String ->
          let code, import_list =
            get_constructor "String" "gen1" target_summary summary method_info
          in
          ((param |> fst) :: import_list, code)
      | Object name ->
          let code, import_list =
            get_constructor name "gen1" target_summary summary method_info
          in
          ((param |> fst) :: import_list, code)
      | _ -> failwith "not allowed type this")
  | Language.Var (typ, id) -> (
      match typ with
      | Int ->
          ( [ param |> fst ],
            "int " ^ id ^ " = " ^ get_value typ id target_summary ^ ";" )
      | Long ->
          ( [ param |> fst ],
            "long " ^ id ^ " = " ^ get_value typ id target_summary ^ ";" )
      | Float ->
          ( [ param |> fst ],
            "float " ^ id ^ " = " ^ get_value typ id target_summary ^ ";" )
      | Double ->
          ( [ param |> fst ],
            "double " ^ id ^ " = " ^ get_value typ id target_summary ^ ";" )
      | Bool ->
          ( [ param |> fst ],
            "boolean " ^ id ^ " = " ^ get_value typ id target_summary ^ ";" )
      | Char ->
          ( [ param |> fst ],
            "char " ^ id ^ " = \'" ^ get_value typ id target_summary ^ "\';" )
      | String ->
          ( [ param |> fst ],
            "String " ^ id ^ " = \"" ^ get_value typ id target_summary ^ "\";"
          )
      | Object name ->
          let code, import_list =
            get_constructor name id target_summary summary method_info
          in
          ((param |> fst) :: import_list, code)
      | Array _ ->
          (* TODO: implement array constructor *)
          let array_type = get_array_type typ in
          let array_constructor = get_array_constructor typ 5 in
          ( [ param |> fst ],
            array_type ^ " " ^ id ^ " = new " ^ array_constructor ^ ";" )
      | _ -> failwith ("not allowed type var" ^ id))

let mk_testcase all_param ps_method method_info =
  let imports =
    let import_set =
      List.fold_left
        (fun set (import_list, _) ->
          List.fold_left
            (fun _set import -> ImportSet.add import _set)
            set import_list)
        ImportSet.empty all_param
    in
    ImportSet.fold
      (fun import stm ->
        if import = "" then stm else stm ^ "import " ^ import ^ ";\n")
      import_set ""
  in
  let start = imports ^ "\n@Test\npublic void test() {\n" in
  let codes =
    List.fold_left (fun code (_, param) -> code ^ param ^ "\n") start all_param
  in
  let execute_ps id ps_method =
    let ps_info = MethodInfo.M.find ps_method method_info in
    let ps_params = ps_info.MethodInfo.formal_params in
    let str_params =
      List.fold_left
        (fun str_params variable ->
          match variable |> snd with
          | Language.Var (_, id) -> str_params ^ "," ^ id
          | _ -> str_params)
        "" ps_params
      |> rm_exp (Str.regexp "^,")
    in
    let str_params = "(" ^ str_params ^ ")" in
    let ps_method =
      Str.split (Str.regexp "\\.") ps_method
      |> List.tl |> List.hd
      |> Str.split (Str.regexp "(")
      |> List.hd
      |> rm_exp (Str.regexp "init")
    in
    id ^ ps_method ^ str_params
  in

  codes ^ execute_ps "gen1." ps_method ^ ";\n}\n\n"

let find_all_parameter ps_method ps_method_summary summary method_info
    class_info =
  let ps_method_info = MethodInfo.M.find ps_method method_info in
  let ps_method_params = ps_method_info.MethodInfo.formal_params in
  let param_codes =
    List.map
      (fun param ->
        get_statement param ps_method_summary summary method_info class_info)
      ps_method_params
  in
  mk_testcase param_codes ps_method method_info

let mk_testcases s_method error_summary call_graph summary call_prop_map
    method_info class_info =
  let ps_methods =
    try
      find_ps_method s_method error_summary call_graph summary call_prop_map
        method_info
    with _ -> [ ("", Language.empty_summary) ]
  in
  List.fold_left
    (fun tests (ps_method, ps_method_summary) ->
      tests
      ^
      try
        find_all_parameter ps_method ps_method_summary summary method_info
          class_info
      with _ -> "")
    "" ps_methods
