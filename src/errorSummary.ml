open Language
module Json = Yojson.Safe
module JsonUtil = Yojson.Safe.Util

let add_use_field value_map field_set =
  Condition.M.fold
    (fun field _ field_set ->
      match field with
      | Condition.RH_Var id ->
          FieldSet.add { used_in_error = true; name = id } field_set
      | _ -> field_set)
    value_map field_set

(* map the fields used when executing the error method
   from the parameters of the error method into a set of fields. *)
let get_use_field pre_var pre_mem =
  Condition.M.fold
    (fun sym _ ufset ->
      match Condition.M.find_opt (AST.get_next_symbol sym pre_mem) pre_mem with
      | Some value_map ->
          UseFieldMap.M.add sym (add_use_field value_map FieldSet.empty) ufset
      | _ -> ufset)
    pre_var UseFieldMap.M.empty

let parse_summary summary =
  let relation =
    JsonUtil.member "BoItv" summary |> JsonUtil.to_string |> Parser.parse_boitv
  in
  let pre_var =
    JsonUtil.member "Precond_Stack" summary
    |> JsonUtil.to_string |> Parser.parse_var
  in
  let pre_mem =
    JsonUtil.member "Precond_Heap" summary
    |> JsonUtil.to_string |> Parser.parse_mem
  in
  let value =
    JsonUtil.member "CItv" summary
    |> JsonUtil.to_string
    |> Parser.parse_citv true pre_mem
  in
  let post_var =
    JsonUtil.member "Postcond_Stack" summary
    |> JsonUtil.to_string |> Parser.parse_var
  in
  let post_mem =
    JsonUtil.member "Postcond_Heap" summary
    |> JsonUtil.to_string |> Parser.parse_mem
  in
  {
    relation;
    value;
    use_field = get_use_field pre_var pre_mem;
    precond = (pre_var, pre_mem);
    postcond = (post_var, post_mem);
    args = [];
  }

let get_method_name assoc =
  let method_name =
    JsonUtil.member "Procname" assoc |> JsonUtil.to_string |> Parser.split_name
  in
  method_name

let from_error_summary_json json =
  if !Cmdline.basic_mode then (get_method_name json, empty_summary)
  else (get_method_name json, parse_summary json)
