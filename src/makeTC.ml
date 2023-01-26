module Relation = Language.Relation
module Value = Language.Value
module Condition = Language.Condition
module MethodInfo = Language.MethodInfo
module SummaryMap = Language.SummaryMap
module CallPropMap = Language.CallPropMap
module CG = Callgraph.G
module HG = Hierarchy.G

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
          | Int eq_int, Int le_int ->
              if eq_int <= le_int then (caller_prop.Language.value, true)
              else (caller_prop.Language.value, false)
          | Float eq_float, Float le_float ->
              if eq_float <= le_float then (caller_prop.Language.value, true)
              else (caller_prop.Language.value, false)
          | _ -> failwith "not allowed type in eq, le")
      | Eq eq_v, Lt lt_v | Lt lt_v, Eq eq_v -> (
          match (eq_v, lt_v) with
          | Int eq_int, Int lt_int ->
              if eq_int < lt_int then (caller_prop.Language.value, true)
              else (caller_prop.Language.value, false)
          | Float eq_float, Float lt_float ->
              if eq_float < lt_float then (caller_prop.Language.value, true)
              else (caller_prop.Language.value, false)
          | _ -> failwith "not allowed type in eq, lt")
      | Eq eq_v, Ge ge_v | Ge ge_v, Eq eq_v -> (
          match (eq_v, ge_v) with
          | Int eq_int, Int ge_int ->
              if eq_int >= ge_int then (caller_prop.Language.value, true)
              else (caller_prop.Language.value, false)
          | Float eq_float, Float ge_float ->
              if eq_float >= ge_float then (caller_prop.Language.value, true)
              else (caller_prop.Language.value, false)
          | _ -> failwith "not allowed type in eq, ge")
      | Eq eq_v, Gt gt_v | Gt gt_v, Eq eq_v -> (
          match (eq_v, gt_v) with
          | Int eq_int, Int gt_int ->
              if eq_int > gt_int then (caller_prop.Language.value, true)
              else (caller_prop.Language.value, false)
          | Float eq_float, Float gt_float ->
              if eq_float > gt_float then (caller_prop.Language.value, true)
              else (caller_prop.Language.value, false)
          | _ -> failwith "not allowed type in eq, gt")
      | Eq eq_v, Between (btw_min, btw_max)
      | Between (btw_min, btw_max), Eq eq_v -> (
          match (eq_v, btw_min, btw_max) with
          | Int eq_int, Int btw_min_int, Int btw_max_int ->
              if eq_int >= btw_min_int && eq_int <= btw_max_int then
                (caller_prop.Language.value, true)
              else (caller_prop.Language.value, false)
          | Float eq_float, Float btw_min_float, Float btw_max_float ->
              if eq_float >= btw_min_float && eq_float <= btw_max_float then
                (caller_prop.Language.value, true)
              else (caller_prop.Language.value, false)
          | _ -> failwith "not allowed type in eq, between")
      | Eq eq_v, Outside (out_min, out_max)
      | Outside (out_min, out_max), Eq eq_v -> (
          match (eq_v, out_min, out_max) with
          | Int eq_int, Int out_min_int, Int out_max_int ->
              if eq_int < out_min_int && eq_int > out_max_int then
                (caller_prop.Language.value, true)
              else (caller_prop.Language.value, false)
          | Float eq_float, Float out_min_float, Float out_max_float ->
              if eq_float < out_min_float && eq_float > out_max_float then
                (caller_prop.Language.value, true)
              else (caller_prop.Language.value, false)
          | _ -> failwith "not allowed type in eq, outside")
      | Le le_v, Ge ge_v | Ge ge_v, Le le_v -> (
          match (le_v, ge_v) with
          | Int le_int, Int ge_int ->
              if le_int >= ge_int then (caller_prop.Language.value, true)
              else (caller_prop.Language.value, false)
          | Float le_float, Float ge_float ->
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
          | Int l_int, Int g_int ->
              if l_int > g_int then (caller_prop.Language.value, true)
              else (caller_prop.Language.value, false)
          | Float l_float, Float g_float ->
              if l_float > g_float then (caller_prop.Language.value, true)
              else (caller_prop.Language.value, false)
          | _ -> failwith "not allowed type in le, ge")
      | Le le_v, Between (btw_min, btw_max)
      | Between (btw_min, btw_max), Le le_v -> (
          match (le_v, btw_min, btw_max) with
          | Int le_int, Int btw_min_int, Int _ ->
              if le_int < btw_min_int then (caller_prop.Language.value, false)
              else (caller_prop.Language.value, true)
          | Float le_float, Float btw_min_float, Float _ ->
              if le_float < btw_min_float then
                (caller_prop.Language.value, false)
              else (caller_prop.Language.value, true)
          | _ -> failwith "not allowed type in le, between")
      | Lt lt_v, Between (btw_min, btw_max)
      | Between (btw_min, btw_max), Lt lt_v -> (
          match (lt_v, btw_min, btw_max) with
          | Int lt_int, Int btw_min_int, Int _ ->
              if lt_int <= btw_min_int then (caller_prop.Language.value, false)
              else (caller_prop.Language.value, true)
          | Float lt_float, Float btw_min_float, Float _ ->
              if lt_float <= btw_min_float then
                (caller_prop.Language.value, false)
              else (caller_prop.Language.value, true)
          | _ -> failwith "not allowed type in lt, between")
      | Ge ge_v, Between (btw_min, btw_max)
      | Between (btw_min, btw_max), Ge ge_v -> (
          match (ge_v, btw_min, btw_max) with
          | Int ge_int, Int _, Int btw_max_int ->
              if ge_int > btw_max_int then (caller_prop.Language.value, false)
              else (caller_prop.Language.value, true)
          | Float ge_float, Float _, Float btw_max_float ->
              if ge_float > btw_max_float then
                (caller_prop.Language.value, false)
              else (caller_prop.Language.value, true)
          | _ -> failwith "not allowed type in ge, between")
      | Gt gt_v, Between (btw_min, btw_max)
      | Between (btw_min, btw_max), Gt gt_v -> (
          match (gt_v, btw_min, btw_max) with
          | Int gt_int, Int _, Int btw_max_int ->
              if gt_int >= btw_max_int then (caller_prop.Language.value, false)
              else (caller_prop.Language.value, true)
          | Float gt_float, Float _, Float btw_max_float ->
              if gt_float >= btw_max_float then
                (caller_prop.Language.value, false)
              else (caller_prop.Language.value, true)
          | _ -> failwith "not allowed type in gt, between")
      | Between (caller_min, caller_max), Between (callee_min, callee_max) -> (
          match (caller_min, caller_max, callee_min, callee_max) with
          | ( Int caller_min_int,
              Int caller_max_int,
              Int callee_min_int,
              Int callee_max_int ) ->
              if
                caller_max_int < callee_min_int
                || callee_max_int < caller_min_int
              then (caller_prop.Language.value, false)
              else (caller_prop.Language.value, true)
          | ( Float caller_min_float,
              Float caller_max_float,
              Float callee_min_float,
              Float callee_max_float ) ->
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
            ->
              if out_min_int <= btw_min_int && out_max_int >= btw_max_int then
                (caller_prop.Language.value, false)
              else (caller_prop.Language.value, true)
          | ( Float btw_min_float,
              Float btw_max_float,
              Float out_min_float,
              Float out_max_float ) ->
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
    with Not_found ->
      let callee_value =
        Value.M.find callee_symbol callee_summary.Language.value
      in
      (Value.M.add caller_symbol callee_value caller_prop.Language.value, true)
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

let get_value id summary =
  let variables, mem = summary.Language.precond in
  let target_variable =
    Condition.M.fold
      (fun symbol variable find_variable ->
        match variable with
        | Condition.RH_Var var -> if var = id then symbol else find_variable
        | _ -> find_variable)
      variables ""
  in
  let target_variable =
    Condition.M.fold
      (fun symbol symbol_trace find_variable ->
        if symbol = target_variable then
          let variable = List.rev symbol_trace |> List.hd in
          match variable with
          | Condition.RH_Symbol sym -> sym
          | _ -> find_variable
        else find_variable)
      mem ""
  in
  let values = summary.Language.value in
  let find_value =
    Value.M.fold
      (fun symbol value find_value ->
        if symbol = target_variable then value else find_value)
      values (Value.Eq Null)
  in
  let value =
    match find_value with
    | Value.Eq v -> (
        match v with
        | Int i ->
            let var = Z3.Arithmetic.Integer.mk_const_s z3ctx id in
            let value = Z3.Arithmetic.Integer.mk_numeral_i z3ctx i in
            let z3exp = Z3.Boolean.mk_eq z3ctx var value in
            calc_z3 var [ z3exp ]
        | Float f ->
            let var = Z3.Arithmetic.Real.mk_const_s z3ctx id in
            let value =
              Z3.Arithmetic.Real.mk_numeral_s z3ctx (f |> string_of_float)
            in
            let z3exp = Z3.Boolean.mk_eq z3ctx var value in
            calc_z3 var [ z3exp ]
        | String s -> s
        | Null -> "null"
        | _ -> "not implemented")
    | Value.Neq v -> (
        match v with
        | Int i ->
            let var = Z3.Arithmetic.Integer.mk_const_s z3ctx id in
            let value = Z3.Arithmetic.Integer.mk_numeral_i z3ctx i in
            let z3exp =
              Z3.Boolean.mk_eq z3ctx var value |> Z3.Boolean.mk_not z3ctx
            in
            calc_z3 var [ z3exp ]
        | Float f ->
            let var = Z3.Arithmetic.Real.mk_const_s z3ctx id in
            let value =
              Z3.Arithmetic.Real.mk_numeral_s z3ctx (f |> string_of_float)
            in
            let z3exp =
              Z3.Boolean.mk_eq z3ctx var value |> Z3.Boolean.mk_not z3ctx
            in
            calc_z3 var [ z3exp ]
        | _ -> "not implemented")
    | Value.Le v -> (
        match v with
        | Int i ->
            let var = Z3.Arithmetic.Integer.mk_const_s z3ctx id in
            let value = Z3.Arithmetic.Integer.mk_numeral_i z3ctx i in
            let z3exp = Z3.Arithmetic.mk_le z3ctx var value in
            calc_z3 var [ z3exp ]
        | Float f ->
            let var = Z3.Arithmetic.Real.mk_const_s z3ctx id in
            let value =
              Z3.Arithmetic.Real.mk_numeral_s z3ctx (f |> string_of_float)
            in
            let z3exp = Z3.Arithmetic.mk_le z3ctx var value in
            calc_z3 var [ z3exp ]
        | _ -> "not implemented")
    | Value.Lt v -> (
        match v with
        | Int i ->
            let var = Z3.Arithmetic.Integer.mk_const_s z3ctx id in
            let value = Z3.Arithmetic.Integer.mk_numeral_i z3ctx i in
            let z3exp = Z3.Arithmetic.mk_lt z3ctx var value in
            calc_z3 var [ z3exp ]
        | Float f ->
            let var = Z3.Arithmetic.Real.mk_const_s z3ctx id in
            let value =
              Z3.Arithmetic.Real.mk_numeral_s z3ctx (f |> string_of_float)
            in
            let z3exp = Z3.Arithmetic.mk_lt z3ctx var value in
            calc_z3 var [ z3exp ]
        | _ -> "not implemented")
    | Value.Ge v -> (
        match v with
        | Int i ->
            let var = Z3.Arithmetic.Integer.mk_const_s z3ctx id in
            let value = Z3.Arithmetic.Integer.mk_numeral_i z3ctx i in
            let z3exp = Z3.Arithmetic.mk_ge z3ctx var value in
            calc_z3 var [ z3exp ]
        | Float f ->
            let var = Z3.Arithmetic.Real.mk_const_s z3ctx id in
            let value =
              Z3.Arithmetic.Real.mk_numeral_s z3ctx (f |> string_of_float)
            in
            let z3exp = Z3.Arithmetic.mk_ge z3ctx var value in
            calc_z3 var [ z3exp ]
        | _ -> "not implemented")
    | Value.Gt v -> (
        match v with
        | Int i ->
            let var = Z3.Arithmetic.Integer.mk_const_s z3ctx id in
            let value = Z3.Arithmetic.Integer.mk_numeral_i z3ctx i in
            let z3exp = Z3.Arithmetic.mk_gt z3ctx var value in
            calc_z3 var [ z3exp ]
        | Float f ->
            let var = Z3.Arithmetic.Real.mk_const_s z3ctx id in
            let value =
              Z3.Arithmetic.Real.mk_numeral_s z3ctx (f |> string_of_float)
            in
            let z3exp = Z3.Arithmetic.mk_gt z3ctx var value in
            calc_z3 var [ z3exp ]
        | _ -> "not implemented")
    | Value.Between (v1, v2) -> (
        match (v1, v2) with
        | Int i1, Int i2 ->
            let var = Z3.Arithmetic.Integer.mk_const_s z3ctx id in
            let value1 = Z3.Arithmetic.Integer.mk_numeral_i z3ctx i1 in
            let value2 = Z3.Arithmetic.Integer.mk_numeral_i z3ctx i2 in
            let z3exp1 = Z3.Arithmetic.mk_ge z3ctx var value1 in
            let z3exp2 = Z3.Arithmetic.mk_le z3ctx var value2 in
            calc_z3 var [ z3exp1; z3exp2 ]
        | Float f1, Float f2 ->
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
        | _ -> "not implemented")
    | Value.Outside (v1, v2) -> (
        match (v1, v2) with
        | Int i1, Int i2 ->
            let var = Z3.Arithmetic.Integer.mk_const_s z3ctx id in
            let value1 = Z3.Arithmetic.Integer.mk_numeral_i z3ctx i1 in
            let value2 = Z3.Arithmetic.Integer.mk_numeral_i z3ctx i2 in
            let z3exp1 = Z3.Arithmetic.mk_lt z3ctx var value1 in
            let z3exp2 = Z3.Arithmetic.mk_gt z3ctx var value2 in
            calc_z3 var [ z3exp1; z3exp2 ]
        | Float f1, Float f2 ->
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
        | _ -> "not implemented")
  in
  value

let get_constructor_list class_name method_info hierarchy_graph =
  let class_to_find =
    try HG.succ hierarchy_graph class_name
    with Invalid_argument _ -> [ class_name ]
  in
  MethodInfo.M.fold
    (fun method_name _ method_list ->
      List.fold_left
        (fun init_list class_name_to_find ->
          if
            Str.string_match
              (class_name_to_find ^ ".<init>" |> Str.regexp)
              method_name 0
          then method_name :: init_list
          else method_list)
        method_list class_to_find)
    method_info []

let rec get_statement param target_summary summary method_info hierarchy_graph =
  let get_constructor class_name id target_summary summary method_info =
    let constructor_list =
      get_constructor_list class_name method_info hierarchy_graph
    in
    if List.length constructor_list = 0 then
      class_name ^ " " ^ id ^ " = new " ^ class_name ^ "();"
    else
      let constructor = List.hd constructor_list in
      let constructor_info = MethodInfo.M.find constructor method_info in
      let constructor_params = constructor_info.MethodInfo.formal_params in
      let constructor_summary =
        SummaryMap.M.find constructor summary |> List.hd
      in
      let constructor =
        Str.replace_first (Str.regexp ".<init>") "" constructor
      in
      if List.length constructor_params = 1 then
        class_name ^ " " ^ id ^ " = new " ^ constructor ^ ";"
      else
        List.fold_left
          (fun constructor_code param ->
            get_statement param constructor_summary summary method_info
              hierarchy_graph
            ^ "\n" ^ constructor_code)
          (class_name ^ " " ^ id ^ " = new " ^ constructor ^ ";")
          (List.tl constructor_params)
  in
  match param with
  | Language.This typ -> (
      match typ with
      | Int -> get_constructor "int" "gen1" target_summary summary method_info
      | Float ->
          get_constructor "float" "gen1" target_summary summary method_info
      | String ->
          get_constructor "String" "gen1" target_summary summary method_info
      | Object name ->
          get_constructor name "gen1" target_summary summary method_info
      | _ -> failwith "not allowed type this")
  | Language.Var (typ, id) -> (
      match typ with
      | Int -> "int " ^ id ^ " = " ^ get_value id target_summary ^ ";"
      | Float -> "float " ^ id ^ " = " ^ get_value id target_summary ^ ";"
      | String -> "String " ^ id ^ " = " ^ get_value id target_summary ^ ";"
      | Object name ->
          get_constructor name id target_summary summary method_info
      | _ -> failwith "not allowed type var" ^ id)

let mk_testcase all_param ps_method method_info =
  let start = "@Test\nvoid test() {\n" in
  let codes =
    List.fold_left (fun code param -> code ^ param ^ "\n") start all_param
  in
  let execute_ps id ps_method =
    let ps_info = MethodInfo.M.find ps_method method_info in
    let ps_params = ps_info.MethodInfo.formal_params in
    let str_params =
      List.fold_left
        (fun str_params variable ->
          match variable with
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
    hierarchy_graph =
  let ps_method_info = MethodInfo.M.find ps_method method_info in
  let ps_method_params = ps_method_info.MethodInfo.formal_params in
  let param_codes =
    List.map
      (fun param ->
        get_statement param ps_method_summary summary method_info
          hierarchy_graph)
      ps_method_params
  in
  mk_testcase param_codes ps_method method_info

let mk_testcases s_method error_summary call_graph summary call_prop_map
    method_info hierarchy_graph =
  let ps_methods =
    find_ps_method s_method error_summary call_graph summary call_prop_map
      method_info
  in
  List.fold_left
    (fun tests (ps_method, ps_method_summary) ->
      tests
      ^ find_all_parameter ps_method ps_method_summary summary method_info
          hierarchy_graph)
    "" ps_methods
