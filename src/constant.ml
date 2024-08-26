open Language
module Json = Yojson.Safe
module JsonUtil = Yojson.Safe.Util

let default_value typ =
  match typ with
  | Int | Long -> [ "1"; "2"; "0"; "-1"; "-2"; "100"; "-100"; "1000"; "-1000" ]
  | Short | Byte -> [ "1"; "2"; "0"; "-1"; "-2"; "-128"; "127" ]
  | Float | Double ->
      [
        "1.0";
        "0.0";
        "2.0";
        "-1.0";
        "-2.0";
        "100.0";
        "-100.0";
        "1000.0";
        "-1000.0";
      ]
  | Bool -> [ "false"; "true" ]
  | Char -> [ "x" ]
  | String -> [ "NULL"; ""; "string"; "1234"; "false"; "true" ]
  | _ -> [ "NULL" ]

let default_primitive =
  (* default value of Object, Array, NonType is null *)
  let typ_list =
    [ Int; Long; Short; Byte; Float; Double; Bool; Char; String ]
  in
  List.fold_left
    (fun mmap typ ->
      PrimitiveInfo.TypeMap.add typ
        (PrimitiveInfo.ClassMap.add "" (default_value typ)
           PrimitiveInfo.ClassMap.empty)
        mmap)
    PrimitiveInfo.TypeMap.empty typ_list

let expand_string_value m_name p_info =
  let method_name = Regexp.first_rm ("(.*)" |> Str.regexp) m_name in
  let default_map, default =
    match PrimitiveInfo.TypeMap.find_opt String p_info with
    | Some map -> (
        match PrimitiveInfo.ClassMap.find_opt "" map with
        | Some value -> (map, value)
        | _ -> (PrimitiveInfo.ClassMap.empty, []))
    | _ -> (PrimitiveInfo.ClassMap.empty, [])
  in
  let extra =
    match PrimitiveInfo.TypeMap.find_opt String p_info with
    | Some map -> (
        match PrimitiveInfo.ClassMap.find_opt method_name map with
        | Some value -> value
        | _ -> [])
    | _ -> []
  in
  PrimitiveInfo.TypeMap.add String
    (PrimitiveInfo.ClassMap.add "" (List.rev_append default extra) default_map)
    p_info

let collect_enum_const assoc mmap =
  let enum_name = JsonUtil.member "enum" assoc |> JsonUtil.to_string in
  let const = JsonUtil.member "const" assoc |> JsonUtil.to_string in
  let new_const_list =
    if InstanceInfo.M.mem enum_name mmap then
      List.cons const (InstanceInfo.M.find enum_name mmap)
    else [ const ]
  in
  InstanceInfo.M.add enum_name new_const_list mmap

let collect_ginstance assoc mmap =
  let class_name = JsonUtil.member "name" assoc |> JsonUtil.to_string in
  let inst = JsonUtil.member "value" assoc |> JsonUtil.to_string in
  let new_inst_list =
    if InstanceInfo.M.mem class_name mmap then
      let old_list = InstanceInfo.M.find class_name mmap in
      if List.mem inst old_list then old_list else List.cons inst old_list
    else [ inst ]
  in
  InstanceInfo.M.add class_name new_inst_list mmap

let collect_primitive assoc mmap =
  let class_name = JsonUtil.member "name" assoc |> JsonUtil.to_string in
  let const =
    JsonUtil.member "value" assoc
    |> JsonUtil.to_string
    |> Regexp.first_rm (Str.regexp "^\"")
    |> Regexp.first_rm (Str.regexp "\"$")
  in
  let new_const_list =
    if PrimitiveInfo.ClassMap.mem class_name mmap then
      let old_list = PrimitiveInfo.ClassMap.find class_name mmap in
      if List.mem const old_list then old_list else List.cons const old_list
    else [ const ]
  in
  PrimitiveInfo.ClassMap.add class_name new_const_list mmap

let str_to_typ typ =
  if typ = "int" then Int
  else if typ = "long" then Long
  else if typ = "float" then Float
  else if typ = "double" then Double
  else if typ = "char" then Char
  else if typ = "String" then String
  else NonType

let of_enum_json json =
  let enum_info = JsonUtil.to_list json in
  List.fold_left
    (fun mmap enum -> collect_enum_const enum mmap)
    InstanceInfo.M.empty enum_info

let of_ginstance_json mmap json =
  let ginst = JsonUtil.member "Object" json |> JsonUtil.to_list in
  List.fold_left (fun mmap inst -> collect_ginstance inst mmap) mmap ginst

let of_primitive_json mmap json =
  let typ_list = [ "int"; "long"; "float"; "double"; "char"; "String" ] in
  List.fold_left
    (fun mmap typ ->
      let cmap =
        match PrimitiveInfo.TypeMap.find_opt (str_to_typ typ) mmap with
        | Some m -> m
        | _ -> PrimitiveInfo.ClassMap.empty
      in
      let const_info =
        JsonUtil.member typ json |> JsonUtil.to_list
        |> List.fold_left (fun tmap const -> collect_primitive const tmap) cmap
      in
      PrimitiveInfo.TypeMap.add (str_to_typ typ) const_info mmap)
    mmap typ_list
