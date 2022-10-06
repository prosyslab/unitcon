module SummaryMap = Summary.SummaryMap
(*when making precond, Pred shape*)

let rm_char str =
  let str = Str.replace_first (Str.regexp "^, +") "" str in
  Str.replace_first (Str.regexp ", +$") "" str

let get_param_var param =
  let Summary.Param_Typ typ, Summary.Exp.Var var = param in
  if String.equal var "this" then "" else var

let get_param_var_list param_list =
  let var_list = List.map (fun x -> get_param_var x) param_list in
  let var =
    List.fold_left (fun statement x -> statement ^ x ^ ", ") "" var_list
  in
  rm_char var

let get_target target_method param_list =
  let class_method =
    target_method |> String.split_on_char '(' |> List.hd
    |> String.split_on_char '.'
  in
  let method_name = List.nth class_method (List.length class_method - 1) in
  let class_name = List.nth class_method (List.length class_method - 2) in
  let val_name = "obj1" in
  class_name ^ " " ^ val_name ^ " = new " ^ class_name ^ "();\n" ^ val_name
  ^ "." ^ method_name ^ "("
  ^ get_param_var_list param_list
  ^ ");\n"

let return_statement param precond =
  let Summary.Param_Typ typ, Summary.Exp.Var var = param in
  let _var = Z3.Arithmetic.Integer.mk_const_s Calculation.z3ctx var in
  let value = Z3.Model.eval precond _var false in
  match value with
  | Some v ->
      if String.equal (_var |> Z3.Expr.to_string) (v |> Z3.Expr.to_string) then
        if String.equal var "this" then ""
        else typ ^ " " ^ var ^ " = new " ^ typ ^ "();\n"
      else typ ^ " " ^ var ^ " = " ^ (v |> Z3.Expr.to_string) ^ ";\n"
  | None -> ""

let precond_cat param_list precond =
  let statement_list =
    List.map (fun x -> return_statement x precond) param_list
  in
  List.fold_left (fun statement x -> String.cat statement x) "" statement_list

let mk_testcase target_method summary precond =
  let target_method_summary =
    SummaryMap.M.find target_method summary |> List.hd
  in
  let param_list = target_method_summary.Summary.param in
  let precond_statements = precond_cat param_list precond in
  let target_statements = get_target target_method param_list in
  let _start = "public void test() { \n" in
  let _end = "}\n" in
  _start ^ precond_statements ^ target_statements ^ _end
