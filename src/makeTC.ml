module SummaryMap = Summary.SummaryMap
(*when making precond, Pred shape*)

type return = OBJ | NULL | NONE

let rm_char str =
  let str = Str.replace_first (Str.regexp "^, +") "" str in
  Str.replace_first (Str.regexp ", +$") "" str

let remove_this param : Summary.param list =
  List.fold_left
    (fun list x ->
      let var =
        match x with
        | Summary.Param_Typ _, Summary.Exp.Var v -> v
        | _ -> failwith ""
      in
      if String.equal var "this" then list else x :: list)
    [] param

let get_param_var param =
  let var =
    match param with
    | Summary.Param_Typ _, Summary.Exp.Var v -> v
    | _ -> failwith ""
  in
  if String.equal var "this" then "" else var

let get_param_var_list param_list =
  let var_list = List.map (fun x -> get_param_var x) param_list in
  let var =
    List.fold_left (fun statement x -> statement ^ x ^ ", ") "" var_list
  in
  rm_char var

let execute_constructor val_name constructor summary =
  let class_method =
    constructor |> String.split_on_char '(' |> List.hd
    |> String.split_on_char '.'
  in
  let class_name = List.nth class_method (List.length class_method - 2) in
  try
    let param_list = SummaryMap.M.find constructor summary |> List.hd in
    let param_list = param_list.Summary.param |> remove_this in
    class_name ^ " " ^ val_name ^ " = new " ^ class_name ^ "("
    ^ get_param_var_list param_list
    ^ ");\n"
  with Not_found ->
    class_name ^ " " ^ val_name ^ " = new " ^ class_name ^ "();\n"

let get_target target_method param_list =
  let class_method =
    target_method |> String.split_on_char '(' |> List.hd
    |> String.split_on_char '.'
  in
  let method_name = List.nth class_method (List.length class_method - 1) in
  let class_name = List.nth class_method (List.length class_method - 2) in
  let val_name = "obj1" in
  let regexp = Str.regexp_string "<init>" in
  if Str.string_match regexp method_name 0 then
    class_name ^ " " ^ val_name ^ " = new " ^ class_name ^ "("
    ^ get_param_var_list param_list
    ^ ");\n"
  else
    class_name ^ " " ^ val_name ^ " = new " ^ class_name ^ "();\n" ^ val_name
    ^ "." ^ method_name ^ "("
    ^ get_param_var_list param_list
    ^ ");\n"

(* compare_prop -> target: one paramter, postcond: all postcondition *)
let compare_prop param precond_obj postcond =
  (* iteration according to # of fields *)
  let rec is_eq_field field post_field =
    match post_field with
    | [] -> true (*not found is null, so true*)
    | hd :: tl -> (
        match (field, hd) with
        | ( (Summary.Exp.Var field_var, Summary.Exp.Int field_intValue),
            (Summary.Exp.Var hd_var, Summary.Exp.Int hd_intValue) ) ->
            if hd_var = field_var && hd_intValue = field_intValue then true
            else is_eq_field field tl
        | ( (Summary.Exp.Var field_var, Summary.Exp.String field_stringValue),
            (Summary.Exp.Var hd_var, Summary.Exp.String hd_stringValue) ) ->
            if hd_var = field_var && hd_stringValue = field_stringValue then
              true
            else is_eq_field field tl
        | _ -> is_eq_field field tl)
  in
  let rec precond_obj_one precond_obj postcond =
    match postcond with
    | [] -> NONE
    | hd :: tl -> (
        match (precond_obj, hd) with
        | ( Summary.Predicate.Object (Var _, _),
            Summary.Predicate.Object (Var _, _) ) -> (
            match (precond_obj, param) with
            | ( Summary.Predicate.Object (Var obj_var, Field obj_field),
                (Summary.Param_Typ _, Summary.Exp.Var param_var) )
              when obj_var = param_var ->
                let cmp_result =
                  let _, post_field =
                    match hd with
                    | Summary.Predicate.Object (Var post_var, Field post_field)
                      ->
                        (post_var, post_field)
                    | Summary.Predicate.Object
                        (String post_var, Field post_field) ->
                        (post_var, post_field)
                    | _ -> failwith "???"
                  in
                  List.fold_left
                    (fun init x -> is_eq_field x post_field && init)
                    true obj_field
                in
                if cmp_result then OBJ else NONE
            | _ -> precond_obj_one precond_obj tl)
        | ( Summary.Predicate.Object (Var _, _),
            Summary.Predicate.Object (Symbol _, _) ) ->
            precond_obj_one precond_obj tl
        | Summary.Predicate.Eq _, Summary.Predicate.Eq _ -> (
            match (precond_obj, param) with
            | ( Summary.Predicate.Eq (Var eq_var, Var eq_value),
                (Summary.Param_Typ _, Summary.Exp.Var param_var) )
              when eq_var = param_var ->
                if eq_value = "null" then NULL else NONE
            | _ -> precond_obj_one precond_obj tl)
        | _ -> precond_obj_one precond_obj tl)
  in
  let rec comp precond_obj =
    match precond_obj with
    | [] -> NONE
    | hd :: tl ->
        let result = precond_obj_one hd postcond in
        if result <> NONE then result else comp tl
  in
  comp precond_obj

let rec compare_prop_null param precond_obj =
  let param_var =
    match param with
    | Summary.Param_Typ _, Summary.Exp.Var v -> v
    | _ -> failwith ""
  in
  match precond_obj with
  | [] -> NONE
  | hd :: tl -> (
      match hd with
      | Summary.Predicate.Eq (Var eq_var, Var eq_value) when eq_var = param_var
        ->
          if eq_value = "null" then NULL else NONE
      | _ -> compare_prop_null param tl)

(*param: parameter one, precond_obj: all obj precond*)
let rec get_object_constructor param precond_obj summary =
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
    let constructor =
      SummaryMap.M.fold
        (fun k _ list ->
          if Str.string_match regexp_param k 0 then
            let postcond = SummaryMap.M.find k summary |> List.hd in
            let post = postcond.Summary.postcond in
            match compare_prop param precond_obj post with
            | OBJ ->
                let sub_param = SummaryMap.M.find k summary |> List.hd in
                let sub_param = sub_param.Summary.param |> remove_this in
                if List.length sub_param <> 0 then
                  (List.append
                     (List.rev_append
                        (List.concat
                           (get_object_constructor sub_param precond_obj summary))
                        [ (param, k) ]))
                    list
                else List.rev_append [ (param, k) ] list
            | NULL -> List.rev_append [ (param, "null") ] list
            | NONE -> list
          else list)
        summary []
    in
    try
      let _ = List.hd constructor in
      constructor
    with Failure _ ->
      let _typ, _var =
        match param with
        | Summary.Param_Typ p, Summary.Exp.Var v -> (p, v)
        | _ -> failwith ""
      in
      [ (param, _typ ^ ".<init>()") ]
    (*default constructor*)
  in
  List.map (fun x -> initial x) param

let mk_object param precond_obj summary =
  let constructor_list =
    get_object_constructor param precond_obj summary |> List.concat
  in
  List.fold_left
    (fun stat x ->
      let x, constructor = x in
      let typ, var =
        match x with
        | Summary.Param_Typ p, Summary.Exp.Var v -> (p, v)
        | _ -> failwith ""
      in
      if constructor = "null" then stat ^ typ ^ " " ^ var ^ " = null;\n"
      else stat ^ execute_constructor var constructor summary)
    "" constructor_list

let get_precond_statement param precond precond_obj summary =
  let typ, var =
    match param with
    | Summary.Param_Typ p, Summary.Exp.Var v -> (p, v)
    | _ -> failwith ""
  in
  let _var = Z3.Arithmetic.Integer.mk_const_s Calculation.z3ctx var in
  let value = Z3.Model.eval precond _var false in
  match value with
  | Some v ->
      if String.equal (_var |> Z3.Expr.to_string) (v |> Z3.Expr.to_string) then
        mk_object [ param ] precond_obj summary
      else
        typ ^ " " ^ var ^ " = "
        ^ (v |> Z3.Arithmetic.Integer.numeral_to_string)
        ^ ";\n"
  | None -> ""

let mk_precond_statement param_list precond precond_obj summary =
  let statement_list =
    List.map
      (fun x -> get_precond_statement x precond precond_obj summary)
      param_list
  in
  List.fold_left (fun statement x -> String.cat statement x) "" statement_list

let mk_testcase target_method summary precond precond_obj =
  let target_method_summary =
    SummaryMap.M.find target_method summary |> List.hd
  in
  let param_list =
    target_method_summary.Summary.param |> remove_this |> List.rev
  in
  let precond_statements =
    mk_precond_statement param_list precond precond_obj summary
  in
  let target_statements = get_target target_method param_list in
  let _start = "public void test() { \n" in
  let _end = "}\n" in
  _start ^ precond_statements ^ target_statements ^ _end
