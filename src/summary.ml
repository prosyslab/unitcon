module Json = Yojson.Safe
module JsonUtil = Yojson.Safe.Util
module Relation = Language.Relation
module Value = Language.Value
module Condition = Language.Condition
module MethodInfo = Language.MethodInfo
module SummaryMap = Language.SummaryMap

let parse_summary summary =
  let relation =
    JsonUtil.member "BoItv" summary |> JsonUtil.to_string |> Parser.parse_boitv
  in
  let value =
    JsonUtil.member "CItv" summary |> JsonUtil.to_string |> Parser.parse_citv
  in
  let pre_var =
    JsonUtil.member "Precond_Stack" summary
    |> JsonUtil.to_string |> Parser.parse_var
  in
  let pre_mem =
    JsonUtil.member "Precond_Heap" summary
    |> JsonUtil.to_string |> Parser.parse_mem
  in
  let post_var =
    JsonUtil.member "Postcond_Stack" summary
    |> JsonUtil.to_string |> Parser.parse_var
  in
  let post_mem =
    JsonUtil.member "Postcond_Heap" summary
    |> JsonUtil.to_string |> Parser.parse_mem
  in
  Language.
    {
      relation;
      value;
      precond = (pre_var, pre_mem);
      postcond = (post_var, post_mem);
      args = [];
    }

let get_method_name assoc =
  let split_name name =
    if String.contains name ' ' then
      name |> String.split_on_char ' ' |> List.tl |> List.hd
    else name
  in
  let method_name =
    JsonUtil.member "method" assoc
    |> JsonUtil.to_list |> List.hd |> JsonUtil.to_string |> split_name
  in
  method_name

let get_return assoc =
  let split_return m =
    if String.contains m ' ' then m |> String.split_on_char ' ' |> List.hd
    else ""
  in
  let return =
    JsonUtil.member "method" assoc
    |> JsonUtil.to_list |> List.hd |> JsonUtil.to_string |> split_return
  in
  return

let is_unnes_method fparam =
  let check_anony_class t =
    match t with
    | Language.Object o ->
        let clist = Str.split Regexp.dollar o in
        List.fold_left
          (fun check name ->
            match name |> int_of_string_opt with Some _ -> true | _ -> check)
          false clist
    | _ -> false
  in
  let check_lambda id =
    if Str.string_match ("\\$bcvar" |> Str.regexp) id 0 then true else false
  in
  let check_unnes p =
    match p |> snd with
    | Language.This _ -> false
    | Var (typ, id) -> check_anony_class typ || check_lambda id
  in
  List.fold_left
    (fun check param -> if check_unnes param then true else check)
    false fparam

let mapping_method_info method_info mmap =
  let method_name = get_method_name method_info in
  let return = get_return method_info in
  let modifier =
    JsonUtil.member "modifier" method_info
    |> JsonUtil.to_list |> List.hd |> Language.modifier_of_json
  in
  let is_static =
    JsonUtil.member "is_static" method_info
    |> JsonUtil.to_list |> List.hd |> JsonUtil.to_string |> bool_of_string
  in
  let formal_params =
    JsonUtil.member "param" method_info
    |> JsonUtil.to_list
    |> List.fold_left
         (fun l p -> (JsonUtil.to_string p |> Parser.parse_param) :: l)
         []
    |> List.rev
  in
  let filename =
    JsonUtil.member "filename" method_info
    |> JsonUtil.to_list |> List.hd |> JsonUtil.to_string
  in
  let info =
    MethodInfo.{ modifier; is_static; formal_params; return; filename }
  in
  if
    Str.string_match (".*access\\$.*" |> Str.regexp) method_name 0
    || Str.string_match (".*access_.*" |> Str.regexp) method_name 0
    || Str.string_match (".*\\.clone()$" |> Str.regexp) method_name 0
    || is_unnes_method formal_params
  then mmap
  else MethodInfo.M.add method_name info mmap

let mapping_summary method_summarys minfo mmap =
  let method_name = get_method_name method_summarys in
  let summarys =
    JsonUtil.member "summary" method_summarys
    |> JsonUtil.to_list
    |> List.fold_left (fun lst summary -> parse_summary summary :: lst) []
    |> List.rev
  in
  let summarys =
    if summarys = [] then [ Language.empty_summary ] else summarys
  in
  if
    Str.string_match (".*access\\$.*" |> Str.regexp) method_name 0
    || Str.string_match (".*access_.*" |> Str.regexp) method_name 0
    || Str.string_match (".*\\.clone()$" |> Str.regexp) method_name 0
    || MethodInfo.M.mem method_name minfo |> not
  then mmap
  else SummaryMap.M.add method_name summarys mmap

let from_method_json json =
  let json = JsonUtil.to_list json in
  let method_info =
    List.fold_left
      (fun mmap method_info -> mapping_method_info method_info mmap)
      MethodInfo.M.empty json
  in
  Modeling.add_java_package_method method_info

let from_summary_json minfo json =
  let json = JsonUtil.to_list json in
  let summary_map =
    List.fold_left
      (fun mmap method_summarys -> mapping_summary method_summarys minfo mmap)
      SummaryMap.M.empty json
  in
  Modeling.add_java_package_summary summary_map
