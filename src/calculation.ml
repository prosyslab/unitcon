module SummaryMap = Summary.SummaryMap
module FindMethodMap = Summary.FindMethodMap
module TraceMap = Trace.TraceMap

let z3ctx =
  Z3.mk_context
    [
      ("model", "true");
      ("proof", "true");
      ("dump_models", "true");
      ("unsat_core", "true");
    ]

let solver = Z3.Solver.mk_solver z3ctx None

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
  | _ -> failwith "mk_z3_exp not implement"

let find_precond tuple summary for_finding =
  let file_name = tuple.Summary.filename in
  let visited = tuple.Summary.visited |> List.rev in
  let tuple = Summary.{ filename = file_name; visited } in
  let method_name = FindMethodMap.M.find tuple for_finding in
  let summary = SummaryMap.M.find method_name summary in
  let rec precond (summary : Summary.summary) =
    match summary with
    | hd :: tl ->
        if (hd.Summary.visited : int list) = visited then hd.Summary.precond
        else precond tl
    | _ -> failwith "not found precond"
  in
  precond summary

let calc_precond trace summary for_finding =
  let precond =
    TraceMap.M.fold
      (fun _ value list -> find_precond value summary for_finding :: list)
      trace []
  in
  let precond = List.concat precond in
  let z3_exp = List.map mk_z3_exp precond in
  Z3.Solver.add solver z3_exp;
  Z3.Solver.check solver [] |> Z3.Solver.string_of_status |> print_endline;
  Z3.Solver.get_model solver |> Option.get
