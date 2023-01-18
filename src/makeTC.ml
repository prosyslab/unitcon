module Relation = Language.Relation
module Value = Language.Value
module Condition = Language.Condition
module MethodInfo = Language.MethodInfo
module SummaryMap = Language.SummaryMap
module CallPropMap = Language.CallPropMap
module G = Callgraph.G

let rec find_relation given_symbol relation =
  match Relation.M.find_opt given_symbol relation with
  | Some find_symbol -> find_relation find_symbol relation
  | None -> given_symbol

let get_symbol_list values =
  Value.M.fold (fun symbol _ symbol_list -> symbol :: symbol_list) values []

(* memory: Condition.mem *)
(* return: (callee_actual_symbol * head_symbol) list *)
let get_head_symbol_list symbols (_, memory) =
  let get_head_symbol symbol memory =
    Condition.M.fold
      (fun head v_and_s_list head_list ->
        let tail = List.rev v_and_s_list |> List.hd in
        match tail with
        | Condition.RH_Var _ -> head_list
        | Condition.RH_Symbol s ->
            if symbol = s then (symbol, head) :: head_list else head_list)
      memory []
  in
  List.map (fun symbol -> get_head_symbol symbol memory |> List.hd) symbols

(* variables: Condition.var *)
(* return: (callee_actual_symbol * head_symbol * param_index) list *)
let get_param_index_list head_symbol_list (variables, _) formal_params =
  let get_param_index head_symbol variables formal_params =
    let variable =
      match Condition.M.find head_symbol variables with
      | Condition.RH_Var v -> v
      | _ -> ""
    in
    let index =
      let rec get_index count params =
        match params with
        | hd :: tl -> (
            match hd with
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
      let index = get_param_index head_symbol variables formal_params in
      (symbol, head_symbol, index))
    head_symbol_list

(* caller_prop: contains boitv, citv, precond, postcond, arg *)
(* return: (caller_value_symbol * callee_value_symbol) *)
let get_caller_value_symbol_list caller_prop callee_param_index_list =
  List.map
    (fun (callee_value_symbol, _, index) ->
      let caller_value_symbol = List.nth caller_prop.Language.args index in
      (caller_value_symbol, callee_value_symbol))
    callee_param_index_list

let check_intersect_value_list caller_prop callee_summary value_symbol_list =
  let check_intersect_value caller_symbol callee_symbol =
    let caller_value = Value.M.find caller_symbol caller_prop.Language.value in
    let callee_value =
      Value.M.find callee_symbol callee_summary.Language.value
    in
    match (caller_value, callee_value) with
    | Eq eq_v1, Eq eq_v2 -> if eq_v1 = eq_v2 then true else false
    | Eq eq_v, Neq neq_v | Neq neq_v, Eq eq_v ->
        if eq_v = neq_v then false else true
    | Eq eq_v, Le le_v | Le le_v, Eq eq_v -> (
        match (eq_v, le_v) with
        | Int eq_int, Int le_int -> if eq_int <= le_int then true else false
        | Float eq_float, Float le_float ->
            if eq_float <= le_float then true else false
        | _ -> failwith "not allowed type in eq, le")
    | Eq eq_v, Lt lt_v | Lt lt_v, Eq eq_v -> (
        match (eq_v, lt_v) with
        | Int eq_int, Int lt_int -> if eq_int < lt_int then true else false
        | Float eq_float, Float lt_float ->
            if eq_float < lt_float then true else false
        | _ -> failwith "not allowed type in eq, lt")
    | Eq eq_v, Ge ge_v | Ge ge_v, Eq eq_v -> (
        match (eq_v, ge_v) with
        | Int eq_int, Int ge_int -> if eq_int >= ge_int then true else false
        | Float eq_float, Float ge_float ->
            if eq_float >= ge_float then true else false
        | _ -> failwith "not allowed type in eq, ge")
    | Eq eq_v, Gt gt_v | Gt gt_v, Eq eq_v -> (
        match (eq_v, gt_v) with
        | Int eq_int, Int gt_int -> if eq_int > gt_int then true else false
        | Float eq_float, Float gt_float ->
            if eq_float > gt_float then true else false
        | _ -> failwith "not allowed type in eq, gt")
    | Eq eq_v, Between (btw_min, btw_max) | Between (btw_min, btw_max), Eq eq_v
      -> (
        match (eq_v, btw_min, btw_max) with
        | Int eq_int, Int btw_min_int, Int btw_max_int ->
            if eq_int >= btw_min_int && eq_int <= btw_max_int then true
            else false
        | Float eq_float, Float btw_min_float, Float btw_max_float ->
            if eq_float >= btw_min_float && eq_float <= btw_max_float then true
            else false
        | _ -> failwith "not allowed type in eq, between")
    | Eq eq_v, Outside (out_min, out_max) | Outside (out_min, out_max), Eq eq_v
      -> (
        match (eq_v, out_min, out_max) with
        | Int eq_int, Int out_min_int, Int out_max_int ->
            if eq_int < out_min_int && eq_int > out_max_int then true else false
        | Float eq_float, Float out_min_float, Float out_max_float ->
            if eq_float < out_min_float && eq_float > out_max_float then true
            else false
        | _ -> failwith "not allowed type in eq, outside")
    | Le le_v, Ge ge_v | Ge ge_v, Le le_v -> (
        match (le_v, ge_v) with
        | Int le_int, Int ge_int -> if le_int >= ge_int then true else false
        | Float le_float, Float ge_float ->
            if le_float >= ge_float then true else false
        | _ -> failwith "not allowed type in le, ge")
    | Le l_v, Gt g_v
    | Lt l_v, Ge g_v
    | Lt l_v, Gt g_v
    | Ge g_v, Lt l_v
    | Gt g_v, Le l_v
    | Gt g_v, Lt l_v -> (
        match (l_v, g_v) with
        | Int l_int, Int g_int -> if l_int > g_int then true else false
        | Float l_float, Float g_float ->
            if l_float > g_float then true else false
        | _ -> failwith "not allowed type in le, ge")
    | Le le_v, Between (btw_min, btw_max) | Between (btw_min, btw_max), Le le_v
      -> (
        match (le_v, btw_min, btw_max) with
        | Int le_int, Int btw_min_int, Int _ ->
            if le_int < btw_min_int then false else true
        | Float le_float, Float btw_min_float, Float _ ->
            if le_float < btw_min_float then false else true
        | _ -> failwith "not allowed type in le, between")
    | Lt lt_v, Between (btw_min, btw_max) | Between (btw_min, btw_max), Lt lt_v
      -> (
        match (lt_v, btw_min, btw_max) with
        | Int lt_int, Int btw_min_int, Int _ ->
            if lt_int <= btw_min_int then false else true
        | Float lt_float, Float btw_min_float, Float _ ->
            if lt_float <= btw_min_float then false else true
        | _ -> failwith "not allowed type in lt, between")
    | Ge ge_v, Between (btw_min, btw_max) | Between (btw_min, btw_max), Ge ge_v
      -> (
        match (ge_v, btw_min, btw_max) with
        | Int ge_int, Int _, Int btw_max_int ->
            if ge_int > btw_max_int then false else true
        | Float ge_float, Float _, Float btw_max_float ->
            if ge_float > btw_max_float then false else true
        | _ -> failwith "not allowed type in ge, between")
    | Gt gt_v, Between (btw_min, btw_max) | Between (btw_min, btw_max), Gt gt_v
      -> (
        match (gt_v, btw_min, btw_max) with
        | Int gt_int, Int _, Int btw_max_int ->
            if gt_int >= btw_max_int then false else true
        | Float gt_float, Float _, Float btw_max_float ->
            if gt_float >= btw_max_float then false else true
        | _ -> failwith "not allowed type in gt, between")
    | Between (caller_min, caller_max), Between (callee_min, callee_max) -> (
        match (caller_min, caller_max, callee_min, callee_max) with
        | ( Int caller_min_int,
            Int caller_max_int,
            Int callee_min_int,
            Int callee_max_int ) ->
            if
              caller_max_int < callee_min_int || callee_max_int < caller_min_int
            then false
            else true
        | ( Float caller_min_float,
            Float caller_max_float,
            Float callee_min_float,
            Float callee_max_float ) ->
            if
              caller_max_float < callee_min_float
              || callee_max_float < caller_min_float
            then false
            else true
        | _ -> failwith "not allowed type in between, between")
    | Between (btw_min, btw_max), Outside (out_min, out_max)
    | Outside (out_min, out_max), Between (btw_min, btw_max) -> (
        match (btw_min, btw_max, out_min, out_max) with
        | Int btw_min_int, Int btw_max_int, Int out_min_int, Int out_max_int ->
            if out_min_int <= btw_min_int && out_max_int >= btw_max_int then
              false
            else true
        | ( Float btw_min_float,
            Float btw_max_float,
            Float out_min_float,
            Float out_max_float ) ->
            if btw_min_float <= out_min_float && btw_max_float >= out_max_float
            then false
            else true
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
        true
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
    check_intersect_value_list call_prop callee_summary value_symbol_list
    |> List.filter (fun value -> value = false)
  in
  if List.length intersect_value <> 0 then false else true

let is_public source_method method_info =
  let source_method_info = MethodInfo.M.find source_method method_info in
  match source_method_info.MethodInfo.modifier with
  | Public -> true
  | _ -> false

let rec find_public_source_method source_method source_summary call_graph
    summary call_prop_map method_info =
  if is_public source_method method_info then
    [ (source_method, source_summary.Language.precond) ]
  else
    let caller_list = G.succ call_graph source_method in
    List.fold_left
      (fun list caller_method ->
        let caller_prop_list =
          CallPropMap.M.find (caller_method, source_method) call_prop_map
          |> List.fold_left
               (fun caller_preconds call_prop ->
                 if
                   match_precond source_method source_summary call_prop
                     method_info
                 then
                   List.rev_append
                     (find_public_source_method caller_method call_prop
                        call_graph summary call_prop_map method_info)
                     caller_preconds
                 else caller_preconds)
               []
        in
        list @ caller_prop_list)
      [] caller_list

let mk_testcase source_method error_summary call_graph summary call_prop_map
    method_info =
  failwith "not implemented"
