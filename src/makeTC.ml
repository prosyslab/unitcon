module SummaryMap = Summary.SummaryMap
(*when making precond, Pred shape*)

let rm_char str =
  let str = Str.replace_first (Str.regexp "^, +") "" str in
  Str.replace_first (Str.regexp ", +$") "" str

let get_param_var param =
  let Summary.Param_Typ typ, Summary.Exp.Var var = param in
  print_endline var;
  if String.equal var "this" then "" else var

let get_param_var_list param_list =
  let var_list = List.map (fun x -> get_param_var x) param_list in
  let var =
    List.fold_left (fun statement x -> statement ^ x ^ ", ") "" var_list
  in
  print_endline var;
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

(* target: one paramter *)
let compare_field param precond_obj init_method postcond =
  (* iteration according to # of fields *)
  let rec is_eq_field field postcond = 
    match postcond with
    | [] -> false
    | hd::tl ->
      match field, hd with
      | (Var field_var, Int field_intValue), (Var hd_var, Int hd_intValue) ->
        if hd_var = field_var && hd_intValue = field_intValue then true false else is_eq_field field tl
      in
  match precond_obj with
  | Summary.Predicatre.Obj (Var _var, Field _field) when _var = param ->
    List.fold_left (fun init x -> is_eq_field x postcond && init) true precond_obj
  | _ -> failwith "not?"

let mk_object param precond_obj summary =
  let reg param =
    let _type, _var =
      match param with
      | Param_Typ _type, Var _var -> (_type, _var)
      | _ -> ("", "")
    in
    Str.regexp_string (_type ^ ".<init>")
  in
  let initial param =
    let regexp_param = reg param in
    SummaryMap.fold
      (fun k value list ->
        if Str.string_match regexp_param k 0 then 
          let postcond = SummaryMap.find k summary in
          let post = postcond.Summary.postcond in

          k :: list else list)
      summary []
  in
  List.map (fun x -> inital x) param

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

let mk_testcase target_method summary precond precond_obj =
  let target_method_summary =
    SummaryMap.M.find target_method summary |> List.hd
  in
  print_endline target_method;
  let param_list = target_method_summary.Summary.param in
  let precond_statements = precond_cat param_list precond in
  let precond_obj_statements = mk_object param_list precond_obj summary in
  let target_statements = get_target target_method param_list in
  let _start = "public void test() { \n" in
  let _end = "}\n" in
  _start ^ precond_statements ^ target_statements ^ _end
