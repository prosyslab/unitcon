open Language
module Json = Yojson.Safe
module JsonUtil = Yojson.Safe.Util

let collect_enum_const assoc mmap =
  let enum_name = JsonUtil.member "enum" assoc |> JsonUtil.to_string in
  let const = JsonUtil.member "const" assoc |> JsonUtil.to_string in
  let new_const_list =
    if EnumInfo.M.mem enum_name mmap then
      List.cons const (EnumInfo.M.find enum_name mmap)
    else [ const ]
  in
  EnumInfo.M.add enum_name new_const_list mmap

let of_json json =
  let enum_info = json |> JsonUtil.to_list in
  List.fold_left
    (fun mmap enum -> collect_enum_const enum mmap)
    EnumInfo.M.empty enum_info
