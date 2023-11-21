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
    JsonUtil.member "Procname" assoc |> JsonUtil.to_string |> split_name
  in
  method_name

let from_error_summary_json json =
  if !Cmdline.basic_mode || !Cmdline.syn_priority then
    (get_method_name json, Language.empty_summary)
  else (get_method_name json, parse_summary json)
