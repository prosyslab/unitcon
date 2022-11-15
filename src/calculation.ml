module SummaryMap = Summary.SummaryMap
module TraceMap = Trace.TraceMap
module ErrorSummaryMap = ErrorSummary.ErrorSummaryMap

let z3ctx =
  Z3.mk_context
    [
      ("model", "true");
      ("proof", "true");
      ("dump_models", "true");
      ("unsat_core", "true");
    ]

let solver = Z3.Solver.mk_solver z3ctx None
let mk_object_list pred_list =
  let mk_object pred =
    match pred with
    | Summary.Predicate.Eq (Var _, String _) -> pred
    | Summary.Predicate.Object (Var _, Field _) -> pred
    | _ -> None
  in
  match pred_list with
  | [] -> []
  | hd::tl -> mk_object hd::mk_object_list tl

let mk_z3_exp pred =
  match pred with
  | Summary.Predicate.Eq (Var _var, Int _i) ->
      let var = Z3.Arithmetic.Integer.mk_const_s z3ctx _var in
      let i = Z3.Arithmetic.Integer.mk_numeral_i z3ctx _i in
      Z3.Boolean.mk_eq z3ctx var i
  | Neq (Var _var, Int _i) ->
      let var = Z3.Arithmetic.Integer.mk_const_s z3ctx _var in
      let i = Z3.Arithmetic.Integer.mk_numeral_i z3ctx _i in
      Z3.Boolean.mk_eq z3ctx var i |> Z3.Boolean.mk_not z3ctx
  | Eq (Var _var, String _str) -> Z3.Boolean.mk_true z3ctx
  | Eq (Var _, Symbol _) -> Z3.Boolean.mk_true z3ctx
  | Object _ -> Z3.Boolean.mk_true z3ctx
  | _ -> 
    Z3.Boolean.mk_true z3ctx
    (* failwith "mk_z3_exp not implement" *)

let find_precond method_name target_method tuple summary error_summary =
  let file_name = tuple.Summary.filename in
  let visited = tuple.Summary.visited |> List.rev in
  let tuple = Summary.{ filename = file_name; visited } in
  if SummaryMap.M.mem method_name summary |> not then []
  else if method_name = target_method then
    let prop_record = ErrorSummaryMap.M.find method_name error_summary in
    prop_record.ErrorSummary.prop
  else
    let _summary = SummaryMap.M.find method_name summary in
    let rec precond (summary : Summary.summary) =
      match summary with
      | hd :: tl ->
          let new_tuple =
            Summary.{ filename = file_name; visited = hd.Summary.visited }
          in
          if Summary.equal_key new_tuple tuple = 0 then hd.Summary.precond
          else precond tl
      | _ ->
          let hd_precond = _summary |> List.hd in
          hd_precond.Summary.precond
    in
    precond _summary

let calc_precond trace target_method summary error_summary =
  let precond =
    TraceMap.M.fold
      (fun method_name value list ->
        find_precond method_name target_method value summary error_summary
        :: list)
      trace []
  in
  let precond = List.concat precond in
  let z3_exp = List.map mk_z3_exp precond in
  let object_exp = mk_object_list precond in
  Z3.Solver.add solver z3_exp;
  Z3.Solver.check solver [] |> Z3.Solver.string_of_status |> print_endline;
  (Z3.Solver.get_model solver |> Option.get, object_exp)
