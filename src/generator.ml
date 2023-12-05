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

exception Not_found_setter

module VarSet = Set.Make (struct
  type t = Language.variable

  let compare = compare
end)

(* Set of VarSet *)
module VarSets = Set.Make (VarSet)

module VarListSet = Set.Make (struct
  type t = AST.var list

  let compare = compare
end)

module ImportSet = Set.Make (struct
  type t = string

  let compare = compare
end)

module ErrorEntrySet = Set.Make (struct
  type t = string * Language.summary

  let compare = compare
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
}

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

(* non-terminal cost for p, terminal cost for p, precision for p *)
let get_cost p =
  if p.unroll > 2 then (p.nt_cost, p.t_cost, p.prec) else (0, 0, 0)

let mk_cost prev_p curr_tc prec =
  {
    unroll = prev_p.unroll + 1;
    nt_cost = AST.count_nt curr_tc;
    t_cost = AST.count_t curr_tc;
    prec;
    tc = curr_tc;
  }

let empty_p = { unroll = 0; nt_cost = 0; t_cost = 0; prec = 0; tc = AST.Skip }

let mk_some x = Some x

let mk_var x = Condition.RH_Var x

let mk_symbol x = Condition.RH_Symbol x

let mk_index x = Condition.RH_Index x

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
      match Condition.M.find_opt (field_name |> mk_var) sym with
      | Some s -> get_tail_symbol field_name s memory
      | None -> (
          match Condition.M.find_opt Condition.RH_Any sym with
          | Some any_sym -> get_tail_symbol field_name any_sym memory
          | None -> symbol))
  | None -> symbol

let find_this_symbol sym condition =
  Condition.M.fold
    (fun symbol symbol_id this_symbol ->
      match symbol_id with
      | Condition.RH_Var v when v = "this" -> symbol
      | _ -> this_symbol)
    condition sym

let find_return_symbol sym condition =
  Condition.M.fold
    (fun symbol symbol_id return_symbol ->
      match symbol_id with
      | Condition.RH_Var v when v = "return" -> symbol
      | _ -> return_symbol)
    condition sym

let get_id_symbol id variable memory =
  let this_symbol = find_this_symbol Condition.RH_Any variable in
  let this_tail_symbol = get_tail_symbol "this" this_symbol memory in
  match Condition.M.find_opt this_tail_symbol memory with
  | None -> this_symbol
  | Some mem -> (
      let if_field_symbol = Condition.M.find_opt (id |> mk_var) mem in
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
  match Condition.M.find_opt (head_symbol |> mk_symbol) variables with
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
   value is set only when the symbol is RH_Index. *)
let get_head_symbol symbol mem =
  Condition.M.fold
    (fun hd_symbol trace hd_list ->
      let hd = find_real_head (get_rh_name ~is_var:false hd_symbol) mem in
      Condition.M.fold
        (fun trace_hd trace_tl hd_list ->
          match trace_tl with
          | Condition.RH_Symbol s when symbol = s -> [ (symbol, None, hd) ]
          | _ -> (
              match trace_hd with
              | Condition.RH_Index i when symbol = i ->
                  ( symbol,
                    get_next_symbol trace_tl mem
                    |> get_rh_name ~is_var:false |> mk_some,
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
      else
        (List.nth caller_prop.Language.args index, callee_value_symbol) :: lst)
    [] callee_param_index_list
  |> List.rev

let get_field_symbol id symbol mem =
  get_tail_symbol (id |> get_rh_name ~is_var:true) (symbol |> mk_symbol) mem

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
    let c_t_mem = Condition.M.find_opt (t_symbol |> mk_symbol) t_var in
    let c_c_mem = Condition.M.find_opt (c_symbol |> mk_symbol) c_var in
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
  let vmap_maker symbol target_vmap from_error =
    let value = Value.M.find symbol target_vmap in
    Value.M.add symbol
      Value.{ from_error; value = value.Value.value }
      target_vmap
  in
  let check_one caller_symbol callee_symbol =
    try
      let caller_value =
        Value.M.find caller_symbol caller_prop.Language.value
      in
      let callee_value =
        Value.M.find callee_symbol callee_summary.Language.value
      in
      let return_caller check =
        if check then
          ( (caller_value.Value.from_error || callee_value.Value.from_error)
            |> vmap_maker caller_symbol caller_prop.Language.value,
            check )
        else (caller_prop.Language.value, check)
      in
      match (caller_value.Value.value, callee_value.Value.value) with
      | Eq eq_v1, Eq eq_v2 ->
          if eq_v1 = eq_v2 then return_caller true else return_caller false
      | Eq eq_v, Neq neq_v | Neq neq_v, Eq eq_v ->
          if eq_v = neq_v then return_caller false else return_caller true
      | Eq eq_v, Le le_v | Le le_v, Eq eq_v -> (
          match (eq_v, le_v) with
          | Int eq_i, Int le_i
          | Long eq_i, Long le_i
          | Int eq_i, Long le_i
          | Long eq_i, Int le_i ->
              if eq_i <= le_i then return_caller true else return_caller false
          | Float eq_f, Float le_f
          | Double eq_f, Double le_f
          | Float eq_f, Double le_f
          | Double eq_f, Float le_f ->
              if eq_f <= le_f then return_caller true else return_caller false
          | _ -> (Language.Value.M.empty, false))
      | Eq eq_v, Lt lt_v | Lt lt_v, Eq eq_v -> (
          match (eq_v, lt_v) with
          | Int eq_i, Int lt_i
          | Long eq_i, Long lt_i
          | Int eq_i, Long lt_i
          | Long eq_i, Int lt_i ->
              if eq_i < lt_i then return_caller true else return_caller false
          | Float eq_f, Float lt_f
          | Double eq_f, Double lt_f
          | Float eq_f, Double lt_f
          | Double eq_f, Float lt_f ->
              if eq_f < lt_f then return_caller true else return_caller false
          | _ -> (Language.Value.M.empty, false))
      | Eq eq_v, Ge ge_v | Ge ge_v, Eq eq_v -> (
          match (eq_v, ge_v) with
          | Int eq_i, Int ge_i
          | Long eq_i, Long ge_i
          | Int eq_i, Long ge_i
          | Long eq_i, Int ge_i ->
              if eq_i >= ge_i then return_caller true else return_caller false
          | Float eq_f, Float ge_f
          | Double eq_f, Double ge_f
          | Float eq_f, Double ge_f
          | Double eq_f, Float ge_f ->
              if eq_f >= ge_f then return_caller true else return_caller false
          | _ -> (Language.Value.M.empty, false))
      | Eq eq_v, Gt gt_v | Gt gt_v, Eq eq_v -> (
          match (eq_v, gt_v) with
          | Int eq_i, Int gt_i
          | Long eq_i, Long gt_i
          | Int eq_i, Long gt_i
          | Long eq_i, Int gt_i ->
              if eq_i > gt_i then return_caller true else return_caller false
          | Float eq_f, Float gt_f
          | Double eq_f, Double gt_f
          | Float eq_f, Double gt_f
          | Double eq_f, Float gt_f ->
              if eq_f > gt_f then return_caller true else return_caller false
          | _ -> (Language.Value.M.empty, false))
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
              if eq_i >= btw_min_i && eq_i <= btw_max_i then return_caller true
              else return_caller false
          | Float eq_f, Float btw_min_f, Float btw_max_f
          | Float eq_f, Float btw_min_f, Double btw_max_f
          | Float eq_f, Double btw_min_f, Float btw_max_f
          | Float eq_f, Double btw_min_f, Double btw_max_f
          | Double eq_f, Float btw_min_f, Float btw_max_f
          | Double eq_f, Float btw_min_f, Double btw_max_f
          | Double eq_f, Double btw_min_f, Float btw_max_f
          | Double eq_f, Double btw_min_f, Double btw_max_f ->
              if eq_f >= btw_min_f && eq_f <= btw_max_f then return_caller true
              else return_caller false
          | _ -> (Language.Value.M.empty, false))
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
              if eq_i < o_min_i && eq_i > o_max_i then return_caller true
              else return_caller false
          | Float eq_f, Float o_min_f, Float o_max_f
          | Float eq_f, Float o_min_f, Double o_max_f
          | Float eq_f, Double o_min_f, Float o_max_f
          | Float eq_f, Double o_min_f, Double o_max_f
          | Double eq_f, Float o_min_f, Float o_max_f
          | Double eq_f, Float o_min_f, Double o_max_f
          | Double eq_f, Double o_min_f, Float o_max_f
          | Double eq_f, Double o_min_f, Double o_max_f ->
              if eq_f < o_min_f && eq_f > o_max_f then return_caller true
              else return_caller false
          | _ -> (Language.Value.M.empty, false))
      | Le le_v, Ge ge_v | Ge ge_v, Le le_v -> (
          match (le_v, ge_v) with
          | Int le_i, Int ge_i
          | Long le_i, Long ge_i
          | Int le_i, Long ge_i
          | Long le_i, Int ge_i ->
              if le_i >= ge_i then return_caller true else return_caller false
          | Float le_f, Float ge_f
          | Double le_f, Double ge_f
          | Float le_f, Double ge_f
          | Double le_f, Float ge_f ->
              if le_f >= ge_f then return_caller true else return_caller false
          | _ -> (Language.Value.M.empty, false))
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
              if l_i > g_i then return_caller true else return_caller false
          | Float l_f, Float g_f
          | Double l_f, Double g_f
          | Float l_f, Double g_f
          | Double l_f, Float g_f ->
              if l_f > g_f then return_caller true else return_caller false
          | _ -> (Language.Value.M.empty, false))
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
              if le_i < btw_min_i then return_caller false
              else return_caller true
          | Float le_f, Float btw_min_f, Float _
          | Float le_f, Float btw_min_f, Double _
          | Double le_f, Double btw_min_f, Float _
          | Double le_f, Double btw_min_f, Double _
          | Float le_f, Double btw_min_f, Float _
          | Float le_f, Double btw_min_f, Double _
          | Double le_f, Float btw_min_f, Float _
          | Double le_f, Float btw_min_f, Double _ ->
              if le_f < btw_min_f then return_caller false
              else return_caller true
          | _ -> (Language.Value.M.empty, false))
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
              if lt_i <= btw_min_i then return_caller false
              else return_caller true
          | Float lt_f, Float btw_min_f, Float _
          | Float lt_f, Float btw_min_f, Double _
          | Double lt_f, Double btw_min_f, Float _
          | Double lt_f, Double btw_min_f, Double _
          | Float lt_f, Double btw_min_f, Float _
          | Float lt_f, Double btw_min_f, Double _
          | Double lt_f, Float btw_min_f, Float _
          | Double lt_f, Float btw_min_f, Double _ ->
              if lt_f <= btw_min_f then return_caller false
              else return_caller true
          | _ -> (Language.Value.M.empty, false))
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
              if ge_i > btw_max_i then return_caller false
              else return_caller true
          | Float ge_f, Float _, Float btw_max_f
          | Float ge_f, Double _, Float btw_max_f
          | Double ge_f, Float _, Double btw_max_f
          | Double ge_f, Double _, Double btw_max_f
          | Float ge_f, Float _, Double btw_max_f
          | Float ge_f, Double _, Double btw_max_f
          | Double ge_f, Float _, Float btw_max_f
          | Double ge_f, Double _, Float btw_max_f ->
              if ge_f > btw_max_f then return_caller false
              else return_caller true
          | _ -> (Language.Value.M.empty, false))
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
              if gt_i >= btw_max_i then return_caller false
              else return_caller true
          | Float gt_f, Float _, Float btw_max_f
          | Float gt_f, Double _, Float btw_max_f
          | Double gt_f, Float _, Double btw_max_f
          | Double gt_f, Double _, Double btw_max_f
          | Float gt_f, Float _, Double btw_max_f
          | Float gt_f, Double _, Double btw_max_f
          | Double gt_f, Float _, Float btw_max_f
          | Double gt_f, Double _, Float btw_max_f ->
              if gt_f >= btw_max_f then return_caller false
              else return_caller true
          | _ -> (Language.Value.M.empty, false))
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
              if r_max_i < e_min_i || e_max_i < r_min_i then return_caller false
              else return_caller true
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
              if r_max_f < e_min_f || e_max_f < r_min_f then return_caller false
              else return_caller true
          | _ -> (Language.Value.M.empty, false))
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
                return_caller false
              else return_caller true
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
                return_caller false
              else return_caller true
          | _ -> (Language.Value.M.empty, false))
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
  List.fold_left
    (fun lst (caller_symbol, callee_symbol) ->
      check_one caller_symbol callee_symbol :: lst)
    [] vs_list
  |> List.rev

(* value_symbol_list: (caller, callee) list
   callee_sym_list: (symbol, value, head) list --> value is set only when symbol is index
*)
let combine_memory base_summary value_symbol_list callee_sym_list =
  let _, memory = base_summary.Language.precond in
  let combine r s value trace org_mem =
    Condition.M.add (r |> mk_symbol)
      (Condition.M.add (s |> mk_index) (value |> mk_symbol) trace)
      org_mem
  in
  List.fold_left
    (fun mem (r, _) ->
      List.fold_left
        (fun mem (s, v, head) ->
          match v with
          | Some value -> (
              match Condition.M.find_opt (r |> mk_symbol) mem with
              | Some m when find_real_head r memory = head ->
                  combine r s value m mem
              | None when find_real_head r memory = head ->
                  combine r s value Condition.M.empty mem
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
  let callee_head_symbols =
    callee_summary.Language.value |> get_symbol_list
    |> get_head_symbol_list callee_summary.Language.precond
  in
  let value_symbol_list =
    (MethodInfo.M.find callee_method m_info).MethodInfo.formal_params
    |> get_param_index_list callee_head_symbols callee_summary.Language.precond
    |> get_caller_value_symbol_list call_prop
  in
  let caller_new_mem =
    combine_memory call_prop value_symbol_list callee_head_symbols
  in
  let intersect_value =
    let values_and_check =
      check_intersect ~is_init:false call_prop callee_summary value_symbol_list
    in
    ( combine_value call_prop.Language.value values_and_check,
      List.filter (fun (_, c) -> c = false) values_and_check )
  in
  if intersect_value |> snd = [] then
    (intersect_value |> fst, caller_new_mem, true)
  else (intersect_value |> fst, caller_new_mem, false)

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
  | Some info -> (
      let is_test_file file_name =
        (* If this method is a method in the test file,
           don't use it even if the modifier is public*)
        Str.string_match (Str.regexp ".*/test/.*") file_name 0
      in
      match info.MethodInfo.modifier with
      | Public when is_test_file info.MethodInfo.filename |> not -> true
      | _ -> false)

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

let get_package_from_m t_method =
  let m_name =
    Regexp.first_rm ("(.*)" |> Str.regexp) t_method
    |> Str.split Regexp.dot |> List.rev |> List.hd
  in
  Regexp.first_rm ("\\." ^ m_name ^ "(.*)" |> Str.regexp) t_method

let get_package_from_v v =
  let typ = match v with Language.This typ -> typ | Var (typ, _) -> typ in
  match typ with
  | Language.Int | Long | Float | Double | Bool | Char | Array _ | None -> ""
  | String -> "java.lang.String"
  | Object t -> t

let is_recursive_param parent_class method_name m_info =
  let info = MethodInfo.M.find method_name m_info in
  let this = Language.Object parent_class in
  List.fold_left
    (fun check var ->
      match var with
      | Language.Var (typ, _) when typ = this -> true
      | _ -> check)
    false info.MethodInfo.formal_params

let contains_symbol symbol memory =
  let inner_contains_symbol mem =
    Condition.M.fold
      (fun _ hd check -> if hd = symbol then true else check)
      mem false
  in
  Condition.M.fold
    (fun sym hd check ->
      if sym = symbol then true else inner_contains_symbol hd || check)
    memory false

let is_new_loc summary =
  let collect_symbol mem =
    Condition.M.fold
      (fun _ hd acc_lst ->
        match hd with Condition.RH_Symbol _ -> hd :: acc_lst | _ -> acc_lst)
      mem []
  in
  let post_var, post_mem = summary.Language.postcond in
  let return_var = find_return_symbol Condition.RH_Any post_var in
  let new_loc_list =
    (match Condition.M.find_opt return_var post_mem with
    | Some m -> collect_symbol m
    | _ -> [])
    |> List.filter (fun x ->
           contains_symbol x (summary.Language.precond |> snd) |> not)
  in
  if new_loc_list = [] then false else true

let is_method_with_memory_effect m_name summary =
  let sum_list = SummaryMap.M.find m_name summary in
  List.filter is_new_loc sum_list = [] |> not

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

let not_found_value v =
  match v.Value.value with Value.Eq None -> true | _ -> false

let calc_value_list typ org_list =
  List.fold_left (fun lst x -> (0, x) :: lst) org_list (default_value_list typ)

let calc_value id value =
  let prec = if value.Value.from_error then 1 else 0 in
  let filter_size lst =
    if id = "size" || id = "index" then
      List.filter
        (fun x ->
          match x |> snd with AST.Primitive (Z x) -> x >= 0 | _ -> false)
        lst
    else lst
  in
  match value.Value.value with
  | Eq v -> (
      match v with
      | Int i | Long i ->
          let var = Z3.Arithmetic.Integer.mk_const_s z3ctx id in
          let exp =
            Z3.Arithmetic.Integer.mk_numeral_i z3ctx i
            |> Z3.Boolean.mk_eq z3ctx var
          in
          calc_value_list Int
            [ (prec, AST.Primitive (Z (calc_z3 var [ exp ] |> int_of_string))) ]
          |> filter_size
      | Float f | Double f ->
          let var = Z3.Arithmetic.Real.mk_const_s z3ctx id in
          let exp =
            Z3.Arithmetic.Real.mk_numeral_s z3ctx (f |> string_of_float)
            |> Z3.Boolean.mk_eq z3ctx var
          in
          calc_value_list Float
            [
              (prec, AST.Primitive (R (calc_z3 var [ exp ] |> float_of_string)));
            ]
      | Bool b -> calc_value_list Bool [ (prec, AST.Primitive (B b)) ]
      | Char c -> calc_value_list Char [ (prec, AST.Primitive (C c)) ]
      | String s -> calc_value_list String [ (prec, AST.Primitive (S s)) ]
      | Null -> [ (prec, AST.Null) ]
      | _ -> failwith "not implemented eq")
  | Neq v -> (
      match v with
      | Int i | Long i ->
          let var = Z3.Arithmetic.Integer.mk_const_s z3ctx id in
          let exp =
            Z3.Arithmetic.Integer.mk_numeral_i z3ctx i
            |> Z3.Boolean.mk_eq z3ctx var |> Z3.Boolean.mk_not z3ctx
          in
          calc_value_list Int
            [ (prec, AST.Primitive (Z (calc_z3 var [ exp ] |> int_of_string))) ]
      | Float f | Double f ->
          let var = Z3.Arithmetic.Real.mk_const_s z3ctx id in
          let exp =
            Z3.Arithmetic.Real.mk_numeral_s z3ctx (f |> string_of_float)
            |> Z3.Boolean.mk_eq z3ctx var |> Z3.Boolean.mk_not z3ctx
          in
          calc_value_list Float
            [
              (prec, AST.Primitive (R (calc_z3 var [ exp ] |> float_of_string)));
            ]
      | Bool b -> calc_value_list Bool [ (prec, AST.Primitive (B (b |> not))) ]
      | String s ->
          calc_value_list String [ (prec, AST.Primitive (S ("not_" ^ s))) ]
      | Null ->
          (* Among the const, only the string can be defined as null *)
          List.fold_left
            (fun lst x ->
              if x = AST.Null then (0, x) :: lst else (prec, x) :: lst)
            []
            (default_value_list String)
      | _ -> failwith "not implemented neq")
  | Le v -> (
      match v with
      | Int i | Long i ->
          let var = Z3.Arithmetic.Integer.mk_const_s z3ctx id in
          let exp =
            Z3.Arithmetic.Integer.mk_numeral_i z3ctx i
            |> Z3.Arithmetic.mk_le z3ctx var
          in
          calc_value_list Int
            [ (prec, AST.Primitive (Z (calc_z3 var [ exp ] |> int_of_string))) ]
      | Float f | Double f ->
          let var = Z3.Arithmetic.Real.mk_const_s z3ctx id in
          let exp =
            Z3.Arithmetic.Real.mk_numeral_s z3ctx (f |> string_of_float)
            |> Z3.Arithmetic.mk_le z3ctx var
          in
          calc_value_list Float
            [
              (prec, AST.Primitive (R (calc_z3 var [ exp ] |> float_of_string)));
            ]
      | _ -> failwith "not implemented le")
  | Lt v -> (
      match v with
      | Int i | Long i ->
          let var = Z3.Arithmetic.Integer.mk_const_s z3ctx id in
          let exp =
            Z3.Arithmetic.Integer.mk_numeral_i z3ctx i
            |> Z3.Arithmetic.mk_lt z3ctx var
          in
          calc_value_list Int
            [ (prec, AST.Primitive (Z (calc_z3 var [ exp ] |> int_of_string))) ]
      | Float f | Double f ->
          let var = Z3.Arithmetic.Real.mk_const_s z3ctx id in
          let exp =
            Z3.Arithmetic.Real.mk_numeral_s z3ctx (f |> string_of_float)
            |> Z3.Arithmetic.mk_lt z3ctx var
          in
          calc_value_list Float
            [
              (prec, AST.Primitive (R (calc_z3 var [ exp ] |> float_of_string)));
            ]
      | _ -> failwith "not implemented lt")
  | Ge v -> (
      match v with
      | Int i | Long i ->
          let var = Z3.Arithmetic.Integer.mk_const_s z3ctx id in
          let exp =
            Z3.Arithmetic.Integer.mk_numeral_i z3ctx i
            |> Z3.Arithmetic.mk_ge z3ctx var
          in
          calc_value_list Int
            [ (prec, AST.Primitive (Z (calc_z3 var [ exp ] |> int_of_string))) ]
          |> filter_size
      | Float f | Double f ->
          let var = Z3.Arithmetic.Real.mk_const_s z3ctx id in
          let exp =
            Z3.Arithmetic.Real.mk_numeral_s z3ctx (f |> string_of_float)
            |> Z3.Arithmetic.mk_ge z3ctx var
          in
          calc_value_list Float
            [
              (prec, AST.Primitive (R (calc_z3 var [ exp ] |> float_of_string)));
            ]
      | _ -> failwith "not implemented ge")
  | Gt v -> (
      match v with
      | Int i | Long i ->
          let var = Z3.Arithmetic.Integer.mk_const_s z3ctx id in
          let exp =
            Z3.Arithmetic.Integer.mk_numeral_i z3ctx i
            |> Z3.Arithmetic.mk_gt z3ctx var
          in
          calc_value_list Int
            [ (prec, AST.Primitive (Z (calc_z3 var [ exp ] |> int_of_string))) ]
      | Float f | Double f ->
          let var = Z3.Arithmetic.Real.mk_const_s z3ctx id in
          let exp =
            Z3.Arithmetic.Real.mk_numeral_s z3ctx (f |> string_of_float)
            |> Z3.Arithmetic.mk_gt z3ctx var
          in
          calc_value_list Float
            [
              (prec, AST.Primitive (R (calc_z3 var [ exp ] |> float_of_string)));
            ]
      | _ -> failwith "not implemented gt")
  | Between (v1, v2) -> (
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
            [ (prec, AST.Primitive (Z (calc_z3 var exp |> int_of_string))) ]
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
            [ (prec, AST.Primitive (R (calc_z3 var exp |> float_of_string))) ]
      | _ -> failwith "not implemented between")
  | Outside (v1, v2) -> (
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
            [ (prec, AST.Primitive (Z (calc_z3 var exp |> int_of_string))) ]
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
            [ (prec, AST.Primitive (R (calc_z3 var exp |> float_of_string))) ]
      | _ -> failwith "not implemented outside")

let find_target_value id summary =
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
            (fun _ trace_tl trace_find_var ->
              match trace_tl with
              | Condition.RH_Symbol s -> s
              | _ -> trace_find_var)
            symbol_trace find_variable
        else find_variable)
      mem target_variable
  in
  let values = summary.Language.value in
  Value.M.fold
    (fun symbol value find_value ->
      if symbol = target_variable then value else find_value)
    values
    Value.{ from_error = false; value = Value.Eq None }

let get_value typ id summary =
  let find_value = find_target_value id summary in
  if not_found_value find_value then
    List.fold_left (fun lst x -> (0, x) :: lst) [] (default_value_list typ)
  else calc_value id find_value

let get_array_size array summary =
  let _, memory = summary.Language.precond in
  let array_symbol = AST.org_symbol array summary in
  match Condition.M.find_opt (array_symbol |> mk_symbol) memory with
  | Some x -> (true, Condition.M.fold (fun _ _ size -> size + 1) x 0)
  | None -> (false, 1)

let get_same_type_param params =
  let get_type p = match p with Language.Var (t, _) -> t | _ -> None in
  List.fold_left
    (fun sets p ->
      let new_set =
        List.fold_left
          (fun set op_p ->
            if get_type p = get_type op_p && get_type p <> Language.None then
              VarSet.add op_p set
            else set)
          (VarSet.empty |> VarSet.add p)
          params
      in
      VarSets.add new_set sets)
    VarSets.empty params

let get_same_precond_param summary param_sets =
  VarSets.fold
    (fun set sets ->
      let filter_singleton set =
        if VarSet.cardinal set < 2 then VarSet.empty else set
      in
      let get_p_value p s =
        match p with
        | Language.Var (_, id) -> find_target_value id s
        | _ -> failwith "Fail: find the target value"
      in
      let new_set =
        let x =
          VarSet.fold
            (fun p new_set ->
              let v = get_p_value p summary in
              VarSet.fold
                (fun op_p new_set ->
                  if v = get_p_value op_p summary then VarSet.add op_p new_set
                  else new_set)
                set (VarSet.add p new_set))
            set VarSet.empty
        in
        x |> filter_singleton
      in
      VarSets.add new_set sets)
    param_sets VarSets.empty
  |> VarSets.filter (fun x -> VarSet.is_empty x |> not)

let get_same_params_set summary params =
  let new_p = List.fold_left (fun p v -> v :: p) [] params |> List.rev in
  get_same_type_param new_p |> get_same_precond_param summary

let satisfied_c m_summary id candidate_constructor summary =
  let c_summarys = SummaryMap.M.find candidate_constructor summary in
  let target_symbol =
    get_id_symbol
      (if is_receiver id then "this" else id)
      (m_summary.Language.precond |> fst)
      (m_summary.Language.precond |> snd)
    |> get_rh_name ~is_var:false
  in
  if target_symbol = "" then [ (true, c_summarys |> List.hd) ]
  else
    List.fold_left
      (fun lst c_summary ->
        ( [
            ( find_relation target_symbol m_summary.Language.relation,
              find_this_symbol Condition.RH_Any
                (c_summary.Language.postcond |> fst)
              |> get_rh_name ~is_var:false );
          ]
          |> check_intersect ~is_init:true m_summary c_summary,
          c_summary )
        :: lst)
      [] c_summarys
    |> List.fold_left
         (fun lst (check_summary, c_summary) ->
           if List.filter (fun (_, c) -> c = false) check_summary = [] then
             ( true,
               combine_value c_summary.Language.value check_summary
               |> new_value_summary c_summary )
             :: lst
           else (false, c_summary) :: lst)
         []

let match_constructor_name class_name method_name =
  let class_name = Str.global_replace Regexp.dollar "\\$" class_name in
  Str.string_match (class_name ^ "\\.<init>" |> Str.regexp) method_name 0

let match_return_object class_name method_name m_info =
  let info = MethodInfo.M.find method_name m_info in
  let return = info.MethodInfo.return in
  String.equal class_name return

let get_clist class_name m_info (c_info, ig) =
  let class_to_find =
    try IG.succ ig class_name |> List.cons class_name
    with Invalid_argument _ -> [ class_name ]
  in
  MethodInfo.M.fold
    (fun method_name _ method_list ->
      List.fold_left
        (fun init_list class_name_to_find ->
          if
            is_normal_class class_name_to_find c_info
            && is_private method_name m_info |> not
            && match_constructor_name class_name_to_find method_name
          then method_name :: init_list
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
  let all_var s_trace =
    Condition.M.fold
      (fun head _ gvar_list ->
        match head with
        | Condition.RH_Var var ->
            (0, AST.GlobalConstant (AST.get_short_class_name c_name ^ "." ^ var))
            :: gvar_list
        | _ -> gvar_list)
      s_trace []
  in
  let compare_var t_var s_trace =
    Condition.M.fold
      (fun head _ gvar ->
        match head with
        | Condition.RH_Var var when var = t_var ->
            AST.get_short_class_name c_name ^ "." ^ var |> mk_some
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
                 | Some gv -> (1, AST.GlobalConstant gv) :: list
                 | None -> list))
              mem list
            |> (Condition.M.fold (fun _ s_trace list ->
                    List.rev_append (all_var s_trace) list))
                 init_mem
        | None ->
            (Condition.M.fold (fun _ s_trace list ->
                 List.rev_append (all_var s_trace) list))
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
              get_rh_name ~is_var:false symbol |> mk_some
            else find_var
        | _ -> find_var)
      vars None
  in
  match t_var with
  | None ->
      if class_name = "java.lang.Class" then find_class_file
      else
        let gvlist = find_global_var_list class_name None mem summary m_info in
        if gvlist = [] then find_enum_var_list class_name e_info else gvlist
  | Some x ->
      let target_variable =
        Condition.M.fold
          (fun symbol symbol_trace find_variable ->
            if get_rh_name ~is_var:false symbol = x then
              Condition.M.fold
                (fun trace_hd _ trace_find_var ->
                  match trace_hd with
                  | Condition.RH_Var var -> var |> mk_some
                  | _ -> trace_find_var)
                symbol_trace find_variable
            else find_variable)
          mem None
      in
      find_global_var_list class_name target_variable mem summary m_info

let mk_params_list summary params_set org_param =
  let fst_param set = VarSet.elements set |> List.hd in
  let find_same_param target =
    let t = target.AST.variable |> fst in
    VarSets.fold
      (fun set find ->
        let fst_p = fst_param set in
        VarSet.fold (fun p f -> if t = p then fst_p else f) set find)
      params_set t
  in
  let org_params_list =
    List.fold_left
      (fun params v ->
        match v with
        | Language.Var (typ, _) when typ = Language.None -> params
        | _ ->
            incr new_var;
            AST.
              {
                import = get_package_from_v v;
                variable = (v, !new_var |> mk_some);
                field = FieldSet.S.empty;
                summary;
              }
            :: params)
      [] org_param
    |> List.rev
  in
  let find_org_param p =
    List.fold_left
      (fun param real_arg ->
        if p = (real_arg.AST.variable |> fst) then real_arg else param)
      AST.empty_var org_params_list
  in
  let rec mk_params org_params params_list =
    match org_params with
    | hd :: tl ->
        let same_param = find_same_param hd |> find_org_param in
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
  let param = if is_s then param else param |> List.tl in
  let same_params_set = get_same_params_set s param in
  let params_list = mk_params_list s same_params_set param in
  List.fold_left
    (fun arg_set lst -> VarListSet.add (lst |> List.rev) arg_set)
    VarListSet.empty params_list

let get_field_map ret s_map =
  let c_name = AST.get_vinfo ret |> fst |> Language.get_class_name in
  List.fold_left
    (fun fm (_, fields) -> FieldSet.S.union fields fm)
    FieldSet.S.empty
    (try SetterMap.M.find c_name s_map with _ -> [])

let error_entry_func ee es m_info c_info =
  let param = (MethodInfo.M.find ee m_info).MethodInfo.formal_params in
  let f_arg_list = mk_arg ~is_s:(is_s_method ee m_info) param es in
  let import = get_package_from_m ee in
  let typ_list =
    if is_private_class import c_info then
      try IG.succ (c_info |> snd) import |> List.cons import
      with Invalid_argument _ -> [ import ]
    else [ import ]
  in
  List.fold_left
    (fun lst typ ->
      if VarListSet.cardinal f_arg_list = 0 then
        (AST.F { typ; method_name = ee; import = typ; summary = es }, []) :: lst
      else
        VarListSet.fold
          (fun f_arg acc ->
            (AST.F { typ; method_name = ee; import = typ; summary = es }, f_arg)
            :: acc)
          f_arg_list lst)
    [] typ_list

(* id is receiver variable *)
let get_void_func id ?(ee = "") ?(es = Language.empty_summary) m_info c_info
    s_map =
  if AST.is_id id then error_entry_func ee es m_info c_info
  else
    let var = AST.get_v id in
    let class_name = AST.get_vinfo id |> fst |> Language.get_class_name in
    if class_name = "" || class_name = "String" then []
    else
      let setter_list =
        (try SetterMap.M.find class_name s_map with _ -> [])
        |> List.filter (fun (s, fields) ->
               is_private s m_info |> not
               && (FieldSet.S.subset var.field fields
                  || Str.string_match (".*Array\\.set" |> Str.regexp) s 0))
      in
      List.fold_left
        (fun lst (s, _) ->
          let f_arg_list =
            mk_arg ~is_s:(is_s_method s m_info)
              (MethodInfo.M.find s m_info).MethodInfo.formal_params var.summary
          in
          let f =
            AST.F
              {
                typ = class_name;
                method_name = s;
                import = var.import;
                summary = var.summary;
              }
          in
          if VarListSet.cardinal f_arg_list = 0 then (f, []) :: lst
          else
            VarListSet.fold (fun f_arg acc -> (f, f_arg) :: acc) f_arg_list lst)
        [] setter_list

let get_ret_obj class_name m_info (_, ig) s_map =
  let class_to_find =
    try IG.succ ig class_name |> List.cons class_name
    with Invalid_argument _ -> [ class_name ]
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
          then method_name :: init_list
          else init_list)
        method_list class_to_find)
    m_info []

let modify_summary id t_summary a_summary =
  let from_error, value = get_array_size id t_summary in
  let new_value =
    Value.M.add
      (AST.org_symbol "size" a_summary)
      Value.{ from_error; value = Value.Ge (Int value) }
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
    let this_symbol = AST.org_symbol "this" old_summary |> mk_symbol in
    let new_premem =
      Condition.M.find this_symbol (old_summary.precond |> snd)
      |> Condition.M.add
           (values |> fst |> fst |> mk_index)
           (values |> snd |> fst |> mk_symbol)
    in
    let new_postmem =
      Condition.M.find this_symbol (old_summary.postcond |> snd)
      |> Condition.M.add
           (values |> fst |> fst |> mk_index)
           (values |> snd |> fst |> mk_symbol)
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
  if !Cmdline.basic_mode || !Cmdline.syn_priority then
    List.fold_left
      (fun list constructor -> (0, constructor, Language.empty_summary) :: list)
      [] summary_list
  else
    List.fold_left
      (fun list constructor ->
        (List.fold_left (fun lst (check, summary) ->
             if check then
               if is_array_init constructor then
                 (1, constructor, modify_summary id t_summary summary) :: lst
               else (1, constructor, summary) :: lst
             else (0, constructor, summary) :: lst))
          list
          (satisfied_c t_summary id constructor summary))
      [] summary_list

let get_cfunc constructor m_info =
  let cost, c, s = constructor in
  let t = get_package_from_m c in
  let func = AST.F { typ = t; method_name = c; import = t; summary = s } in
  let arg_list =
    mk_arg ~is_s:(is_s_method c m_info)
      (MethodInfo.M.find c m_info).MethodInfo.formal_params s
  in
  if VarListSet.cardinal arg_list = 0 then [ (cost, (func, AST.Arg [])) ]
  else
    VarListSet.fold
      (fun arg cfuncs -> (cost, (func, AST.Arg arg)) :: cfuncs)
      arg_list []

let get_cfuncs list m_info =
  List.fold_left
    (fun lst (cost, c, s) ->
      List.rev_append (get_cfunc (cost, c, s) m_info) lst)
    [] list

let get_c ret summary _ m_info c_info =
  let class_name = AST.get_vinfo ret |> fst |> Language.get_class_name in
  if class_name = "" then []
  else
    let id = AST.get_vinfo ret |> snd in
    let summary_filtering list =
      List.filter (fun (_, c, _) -> is_public c m_info) list
      |> List.filter (fun (_, c, _) ->
             is_recursive_param class_name c m_info |> not)
    in
    let s_list =
      get_clist class_name m_info c_info
      |> satisfied_c_list id (AST.get_v ret).summary summary
      |> summary_filtering
    in
    get_cfuncs s_list m_info

let get_ret_c ret summary m_info c_info s_map =
  let class_name = AST.get_vinfo ret |> fst |> Language.get_class_name in
  if class_name = "" then []
  else
    let id = AST.get_vinfo ret |> snd in
    let summary_filtering list =
      List.filter (fun (_, c, _) -> is_public c m_info) list
      |> List.filter (fun (_, c, _) -> is_method_with_memory_effect c summary)
      |> List.filter (fun (_, c, _) ->
             is_recursive_param class_name c m_info |> not)
    in
    let s_list =
      get_ret_obj class_name m_info c_info s_map
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
            !outer |> mk_some );
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
          x
          |> List.rev_append
               (List.fold_left
                  (fun lst x -> AST.mk_assign_arg x arg :: lst)
                  [] s)))
    [ AST.Skip ] args

let const_unroll p summary m_info e_info =
  match p with
  | AST.Const (x, _) when AST.const p ->
      let typ, id = AST.get_vinfo x in
      if is_primitive x then
        List.fold_left
          (fun lst x1 -> (x1 |> fst, AST.const_rule1 p (x1 |> snd)) :: lst)
          []
          (get_value typ id (AST.get_v x).summary)
      else
        let r3 =
          List.fold_left
            (fun lst x1 ->
              match x1 |> snd with
              | AST.Primitive _ -> lst
              | _ -> (x1 |> fst, AST.const_rule3 p) :: lst)
            []
            (get_value typ id (AST.get_v x).summary)
        in
        let r2 =
          List.fold_left
            (fun lst x1 -> (x1 |> fst, AST.const_rule2 p (x1 |> snd)) :: lst)
            []
            (global_var_list
               (Language.get_class_name (AST.get_vinfo x |> fst))
               (AST.get_v x).summary summary m_info e_info)
        in
        if is_receiver (AST.get_vinfo x |> snd) then r2
        else List.rev_append r3 r2
  | _ -> failwith "Fail: const_unroll"

let fcall_in_assign_unroll p summary cg m_info c_info s_map =
  match p with
  | AST.Assign (x0, _, _, _) when AST.fcall_in_assign p ->
      let field_map = get_field_map x0 s_map in
      List.rev_append
        (get_c x0 summary cg m_info c_info)
        (get_ret_c x0 summary m_info c_info s_map)
      |> List.fold_left
           (fun lst (prec, (f, arg)) ->
             (prec, AST.fcall_in_assign_rule p field_map f arg) :: lst)
           []
  | _ -> failwith "Fail: fcall_in_assign_unroll"

let recv_in_assign_unroll (prec, p) m_info c_info =
  match p with
  | AST.Assign (_, _, f, arg) when AST.recv_in_assign p ->
      if
        is_nested_class (AST.get_func f).import
        && is_s_class (AST.get_func f).import c_info |> not
        && is_init_method (AST.get_func f).method_name
      then (
        let recv, f, arg = get_inner_func f arg in
        let r2 = AST.recv_in_assign_rule2_1 p recv f arg in
        let r3 = AST.recv_in_assign_rule3_1 p recv f arg in
        incr outer;
        (prec, r2) :: [ (prec, r3) ])
      else if cname_condition (AST.get_func f).method_name m_info then
        [ (prec, get_cname f |> AST.recv_in_assign_rule1 p) ]
      else
        let r2 = AST.recv_in_assign_rule2 p "con_recv" !recv in
        let r3 = AST.recv_in_assign_rule3 p "con_recv" !recv in
        incr recv;
        (prec, r2) :: [ (prec, r3) ]
  | _ -> failwith "Fail: recv_in_assign_unroll"

let rec arg_in_assign_unroll (prec, p) =
  match p with
  | AST.Assign (_, _, _, arg) when AST.arg_in_assign p ->
      get_arg_seq
        (List.fold_left
           (fun lst x -> AST.Variable x :: lst)
           [] (arg |> AST.get_arg))
      |> List.fold_left
           (fun lst x ->
             (prec, AST.arg_in_assign_rule p x (AST.Param (arg |> AST.get_arg)))
             :: lst)
           []
  | Seq (s1, s2) when AST.arg_in_assign s2 ->
      arg_in_assign_unroll (prec, s2)
      |> List.fold_left
           (fun lst x -> (x |> fst, AST.Seq (s1, x |> snd)) :: lst)
           []
  | _ -> failwith "Fail: arg_in_assign_unroll"

let void_unroll p =
  match p with
  | AST.Seq _ when AST.void p ->
      (0, AST.void_rule1 p)
      :: List.fold_left (fun lst x -> (0, x) :: lst) [] (AST.void_rule2 p)
  | _ -> failwith "Fail: void_unroll"

let fcall_in_void_unroll p m_info c_info s_map =
  match p with
  | AST.Void (x, _, _) when AST.fcall1_in_void p || AST.fcall2_in_void p ->
      let lst = get_void_func x m_info c_info s_map in
      if lst = [] then raise Not_found_setter
      else
        List.fold_left
          (fun lst (f, arg) ->
            (0, AST.fcall_in_void_rule p f (AST.Arg arg)) :: lst)
          [] lst
  | _ -> failwith "Fail: fcall_in_void_unroll"

let recv_in_void_unroll (prec, p) m_info =
  match p with
  | AST.Void (_, f, _) when AST.recv_in_void p ->
      if cname_condition (AST.get_func f).method_name m_info then
        [ (prec, get_cname f |> AST.recv_in_void_rule1 p) ]
      else
        let r2 = AST.recv_in_void_rule2 p "con_recv" !recv in
        let r3 = AST.recv_in_void_rule3 p "con_recv" !recv in
        incr recv;
        (prec, r2) :: [ (prec, r3) ]
  | _ -> failwith "Fail: recv_in_void_unroll"

let rec arg_in_void_unroll (prec, p) =
  match p with
  | AST.Void (_, _, arg) when AST.arg_in_void p ->
      let arg_seq =
        get_arg_seq
          (List.fold_left
             (fun lst x -> AST.Variable x :: lst)
             [] (arg |> AST.get_arg))
      in
      List.fold_left
        (fun lst x ->
          (prec, AST.arg_in_void_rule p x (AST.Param (arg |> AST.get_arg)))
          :: lst)
        [] arg_seq
  | Seq (s1, s2) when AST.arg_in_void s2 ->
      arg_in_void_unroll (prec, s2)
      |> List.fold_left
           (fun lst x -> (x |> fst, AST.Seq (s1, x |> snd)) :: lst)
           []
  | _ -> failwith "Fail: arg_in_void_unroll"

let one_unroll p summary cg m_info c_info s_map e_info =
  match p with
  | AST.Seq _ when AST.void p -> void_unroll p
  | Const _ when AST.const p -> const_unroll p summary m_info e_info
  | Assign _ when AST.fcall_in_assign p ->
      (* fcall_in_assign --> recv_in_assign --> arg_in_assign *)
      fcall_in_assign_unroll p summary cg m_info c_info s_map
      |> List.fold_left
           (fun acc_lst x ->
             List.rev_append (recv_in_assign_unroll x m_info c_info) acc_lst)
           []
      |> List.fold_left
           (fun acc_lst x -> List.rev_append (arg_in_assign_unroll x) acc_lst)
           []
      |> List.rev
  | Void _ when AST.fcall1_in_void p ->
      (* fcall1_in_void --> recv_in_void --> arg_in_void *)
      fcall_in_void_unroll p m_info c_info s_map
      |> List.fold_left
           (fun acc_lst x ->
             List.rev_append (recv_in_void_unroll x m_info) acc_lst)
           []
      |> List.fold_left
           (fun acc_lst x -> List.rev_append (arg_in_void_unroll x) acc_lst)
           []
      |> List.rev
  | Void _ when AST.fcall2_in_void p ->
      (* fcall2_in_void --> arg_in_void *)
      fcall_in_void_unroll p m_info c_info s_map
      |> List.fold_left
           (fun acc_lst x -> List.rev_append (arg_in_void_unroll x) acc_lst)
           []
      |> List.rev
  | Void _ when AST.recv_in_void p ->
      (* unroll error entry *)
      recv_in_void_unroll (0, p) m_info
      |> List.fold_left
           (fun acc_lst x -> List.rev_append (arg_in_void_unroll x) acc_lst)
           []
      |> List.rev
  | _ -> failwith "Fail: one_unroll"

let rec all_unroll ?(assign_ground = false) p summary cg m_info c_info s_map
    e_info stmt_map =
  match p with
  | _ when AST.ground p -> stmt_map
  | _ when assign_ground ->
      all_unroll_void p summary cg m_info c_info s_map e_info stmt_map
  | AST.Seq (s1, s2) when s2 = AST.Stmt ->
      all_unroll ~assign_ground s1 summary cg m_info c_info s_map e_info
        stmt_map
  | AST.Seq (s1, s2) ->
      all_unroll ~assign_ground s1 summary cg m_info c_info s_map e_info
        stmt_map
      |> all_unroll ~assign_ground s2 summary cg m_info c_info s_map e_info
  | _ ->
      StmtMap.M.add p
        (one_unroll p summary cg m_info c_info s_map e_info)
        stmt_map

and all_unroll_void p summary cg m_info c_info s_map e_info stmt_map =
  match p with
  | _ when AST.ground p -> stmt_map
  | AST.Seq _ when AST.void p ->
      StmtMap.M.add p
        (one_unroll p summary cg m_info c_info s_map e_info)
        stmt_map
  | Seq (s1, s2) -> (
      match AST.last_code s1 with
      | AST.Assign _ when AST.is_stmt s2 ->
          let new_void =
            one_unroll
              (AST.Seq (AST.last_code s1, s2))
              summary cg m_info c_info s_map e_info
            |> List.fold_left
                 (fun lst void ->
                   ( void |> fst,
                     AST.Seq (AST.modify_last_assign s1, void |> snd) )
                   :: lst)
                 []
            |> List.rev
          in
          StmtMap.M.add p new_void stmt_map
      | _ ->
          all_unroll_void s1 summary cg m_info c_info s_map e_info stmt_map
          |> all_unroll_void s2 summary cg m_info c_info s_map e_info)
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
  | AST.Seq (s1, s2) -> p :: List.rev_append (return_stmts s1) (return_stmts s2)
  | _ when AST.ground p -> []
  | _ -> [ p ]

let sort_stmts map stmts =
  List.sort
    (fun s1 s2 ->
      match (StmtMap.M.find_opt s1 map, StmtMap.M.find_opt s2 map) with
      | Some l1, Some l2 -> compare (l1 |> List.length) (l2 |> List.length)
      | Some _, None -> 1
      | None, Some _ -> -1
      | None, None -> 0)
    stmts

let combinate (prec, p) stmt_map =
  let combinate_stmt p s new_s_list =
    List.fold_left
      (fun lst new_s ->
        ((p |> fst) + (new_s |> fst), change_stmt (p |> snd) s (new_s |> snd))
        :: lst)
      [] new_s_list
  in
  return_stmts p |> sort_stmts stmt_map
  |> List.fold_left
       (fun lst s ->
         match StmtMap.M.find_opt s stmt_map with
         | Some new_s_list when new_s_list = [] ->
             (* Because these will be never grounded, remove all *)
             []
         | Some new_s_list ->
             List.fold_left
               (fun l _p -> List.rev_append (combinate_stmt _p s new_s_list) l)
               [] lst
         | _ -> lst)
       [ (prec, p) ]
  |> List.rev

let check_overload prev_ee current_ee =
  let prev =
    if prev_ee = "" then ""
    else
      Str.split (Str.regexp "(") prev_ee
      |> List.hd
      |> Str.global_replace Regexp.dollar "\\$"
  in
  if prev = "" || Str.string_match (prev ^ "(" |> Str.regexp) current_ee 0 then
    true
  else false

(* find error entry *)
let rec find_ee ?(prev_ee = "") e_method e_summary cg summary call_prop_map
    m_info c_info =
  let propagation ?(prev_ee = "") caller_method caller_preconds call_prop =
    let new_value, new_mem, check_match =
      satisfy e_method e_summary call_prop m_info
    in
    if !Cmdline.basic_mode || !Cmdline.syn_priority then
      ErrorEntrySet.union caller_preconds
        (find_ee ~prev_ee caller_method Language.empty_summary cg summary
           call_prop_map m_info c_info)
    else if check_match then
      let new_call_prop =
        new_mem_summary (new_value_summary call_prop new_value) new_mem
      in
      ErrorEntrySet.union caller_preconds
        (find_ee ~prev_ee caller_method new_call_prop cg summary call_prop_map
           m_info c_info)
    else caller_preconds
  in
  if prev_ee <> "" && check_overload prev_ee e_method |> not then
    ErrorEntrySet.empty
  else
    let new_prev_ee, ee_set =
      if is_public e_method m_info && check_overload prev_ee e_method then
        (e_method, ErrorEntrySet.add (e_method, e_summary) ErrorEntrySet.empty)
      else (prev_ee, ErrorEntrySet.empty)
    in
    let caller_list =
      try
        CG.succ cg e_method
        |> List.filter (fun x -> x <> e_method && x <> prev_ee)
      with Invalid_argument _ -> []
    in
    List.fold_left
      (fun set caller_method ->
        (match
           CallPropMap.M.find_opt (caller_method, e_method) call_prop_map
         with
        | None ->
            (* It is possible without any specific conditions *)
            find_ee ~prev_ee:new_prev_ee caller_method Language.empty_summary cg
              summary call_prop_map m_info c_info
        | Some prop_list ->
            List.fold_left
              (fun caller_preconds call_prop ->
                propagation ~prev_ee:new_prev_ee caller_method caller_preconds
                  call_prop)
              ErrorEntrySet.empty prop_list)
        |> ErrorEntrySet.union set)
      ee_set caller_list

let pretty_format p =
  let i_format i = Str.replace_first Regexp.dollar "." i in
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
          set (arg |> AST.get_param)
        |> add_import (AST.get_v x0).import
        |> add_import (AST.get_func f).import
    | Void (_, f, arg) ->
        List.fold_left
          (fun s (a : AST.var) -> add_import a.import s)
          set (arg |> AST.get_param)
        |> add_import (AST.get_func f).import
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
  let start = "\npublic static void main(String args[]) throws Exception {\n" in
  let code = start ^ AST.code p ^ "}\n\n" in
  (import, code)

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

let rec mk_testcase summary cg m_info c_info s_map e_info queue =
  let queue = if !Cmdline.basic_mode then queue else priority_q queue in
  match queue with
  | p :: tl ->
      if AST.ground p.tc then [ (pretty_format p.tc, tl) ]
      else
        (match
           all_unroll ~assign_ground:(AST.assign_ground p.tc) p.tc summary cg
             m_info c_info s_map e_info StmtMap.M.empty
         with
        | exception Not_found_setter -> tl
        | x ->
            combinate (p.prec, p.tc) x
            |> List.fold_left
                 (fun lst new_tc ->
                   mk_cost p (new_tc |> snd) (new_tc |> fst) :: lst)
                 []
            |> List.rev_append (tl |> List.rev))
        |> mk_testcase summary cg m_info c_info s_map e_info
  | [] -> []

let mk_testcases ~is_start pkg_name queue (e_method, error_summary)
    (cg, summary, call_prop_map, m_info, c_info, s_map, e_info) =
  let apply_rule list =
    List.fold_left
      (fun lst (f, arg) ->
        AST.fcall_in_void_rule (AST.Void (Id, Func, Arg [])) f (AST.Arg arg)
        :: lst)
      [] list
  in
  let init =
    if is_start then (
      pkg := pkg_name;
      let e_method =
        if String.contains e_method ':' then
          e_method |> Str.split Regexp.colon |> List.hd
        else e_method
      in
      ErrorEntrySet.fold
        (fun (ee, ee_s) init_list ->
          apply_rule (get_void_func AST.Id ~ee ~es:ee_s m_info c_info s_map)
          |> List.fold_left
               (fun lst new_tc -> mk_cost empty_p new_tc 0 :: lst)
               []
          |> List.rev_append init_list)
        (find_ee e_method error_summary cg summary call_prop_map m_info c_info)
        [])
    else queue
  in
  let result = mk_testcase summary cg m_info c_info s_map e_info init in
  if result = [] then (("", ""), []) else List.hd result
