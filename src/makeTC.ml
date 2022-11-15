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
    | hd :: tl -> (
        match (field, hd) with
        | ( (Summary.Exp.Var field_var, Summary.Exp.Int field_intValue),
            Summary.Predicate.Eq (Summary.Exp.Var hd_var, Summary.Exp.Int hd_intValue) ) ->
            if hd_var = field_var && hd_intValue = field_intValue then true
            else is_eq_field field tl
        | ( (Summary.Exp.Var field_var, Summary.Exp.String field_stringValue),
            Summary.Predicate.Eq (Summary.Exp.Var hd_var, Summary.Exp.String hd_stringValue) ) ->
            if hd_var = field_var && hd_stringValue = field_stringValue then true
            else is_eq_field field tl)
  in
  let precond_obj_one precond_obj =
    match (precond_obj, param) with
    | Summary.Predicate.Object (Var obj_var, Field obj_field),
        (Summary.Param_Typ param_type, Summary.Exp.Var param_var) ->
        List.fold_left
          (fun init x -> is_eq_field x postcond && init)
          true obj_field
    | _ -> false
  in
  let rec comp precond_obj =
    match precond_obj with
    | [] -> false
    | hd :: tl -> if precond_obj_one hd then true else comp tl
  in
  comp precond_obj

(*param: parameter one, precond_obj: one obj precond*)
let get_object_initial param precond_obj summary =
  let reg param =
    let _type, _var =
      match param with
      | Summary.Param_Typ _type, Summary.Exp.Var _var -> (_type, _var)
      | _ -> ("", "")
    in
    Str.regexp_string (_type ^ ".<init>")
  in
  let initial param =
    let regexp_param = reg param in
    let init_method = SummaryMap.M.fold
      (fun k _ list ->
        if Str.string_match regexp_param k 0 then
          (let postcond = SummaryMap.M.find k summary |> List.hd in
          let post = postcond.Summary.postcond in
          if compare_field param precond_obj k post then [(param, k)]
          else list)
        else list)
      summary []
      in
      try let _ = List.hd init_method in init_method with Failure _ -> [(param, "null")] 
  in
  List.map (fun x -> initial x) param

let mk_object param precond_obj summary =
  let initial_method = get_object_initial param precond_obj summary in
  List.fold_left
    (fun stat x ->
      let x = List.hd x in
      let x, init_method = x in
      let Summary.Param_Typ typ, Summary.Exp.Var var = x in
      if init_method = "null" then stat ^ typ ^ " " ^ var ^ " = null;\n"
      else
      stat ^ typ ^ " " ^ var ^ " = new " ^ init_method ^ "();\n"
      )
    "" initial_method

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
  _start ^ precond_obj_statements ^ target_statements ^ _end
