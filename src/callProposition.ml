open Language
module Json = Yojson.Safe
module JsonUtil = Yojson.Safe.Util

let parse_callprop callprop =
  let relation =
    JsonUtil.member "BoItv" callprop |> JsonUtil.to_string |> Parser.parse_boitv
  in
  let value =
    JsonUtil.member "CItv" callprop
    |> JsonUtil.to_string |> Parser.parse_citv false
  in
  let pre_var =
    JsonUtil.member "Precond_Stack" callprop
    |> JsonUtil.to_string |> Parser.parse_var
  in
  let pre_mem =
    JsonUtil.member "Precond_Heap" callprop
    |> JsonUtil.to_string |> Parser.parse_mem
  in
  let post_var =
    JsonUtil.member "Postcond_Stack" callprop
    |> JsonUtil.to_string |> Parser.parse_var
  in
  let post_mem =
    JsonUtil.member "Postcond_Heap" callprop
    |> JsonUtil.to_string |> Parser.parse_mem
  in
  let args =
    JsonUtil.member "Args" callprop |> JsonUtil.to_string |> Parser.parse_args
  in
  {
    relation;
    value;
    use_field = UseFieldMap.M.empty;
    precond = (pre_var, pre_mem);
    postcond = (post_var, post_mem);
    args;
  }

let get_method_names assoc =
  let caller_name =
    JsonUtil.member "Caller" assoc |> JsonUtil.to_string |> Parser.split_name
  in
  let callee_name =
    JsonUtil.member "Callee" assoc |> JsonUtil.to_string |> Parser.split_name
  in
  (caller_name, callee_name)

let mapping_callprop callprop mmap =
  let method_names = get_method_names callprop in
  if method_names = ("", "") then mmap
  else
    let callprop = parse_callprop callprop in
    let callprop_map =
      match CallPropMap.M.find_opt method_names mmap with
      | Some props -> CallPropMap.M.add method_names (callprop :: props) mmap
      | None -> CallPropMap.M.add method_names [ callprop ] mmap
    in
    callprop_map

let from_callprop_json json =
  let json = JsonUtil.to_list json in
  List.fold_left
    (fun mmap callprop -> mapping_callprop callprop mmap)
    CallPropMap.M.empty json
