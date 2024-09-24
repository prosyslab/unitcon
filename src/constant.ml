open Language
module Json = Yojson.Safe
module JsonUtil = Yojson.Safe.Util

let str_to_typ = function
  | "int" -> Int
  | "long" -> Long
  | "short" -> Short
  | "byte" -> Byte
  | "float" -> Float
  | "double" -> Double
  | "char" -> Char
  | "String" -> String
  | _ -> NonType

let basic_types =
  [ "int"; "long"; "short"; "byte"; "float"; "double"; "char"; "String" ]

let default_value typ =
  match typ with
  | Int | Long -> [ "1"; "2"; "0"; "-1"; "-2"; "100"; "-100"; "1000"; "-1000" ]
  | Short | Byte -> [ "1"; "2"; "0"; "-1"; "-2"; "-128"; "127" ]
  | Float | Double ->
      [
        "0.05";
        "0.5";
        "1.0";
        "0.0";
        "-0.05";
        "-0.5";
        "-1.0";
        "100.0";
        "-100.0";
        "1000.0";
        "-1000.0";
      ]
  | Bool -> [ "false"; "true" ]
  | Char -> [ "x" ]
  | String -> [ "NULL"; ""; "1234"; "true"; "root" ]
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

let add_gconst cname assoc mmap =
  let is_enum = JsonUtil.member "is_enum" assoc |> JsonUtil.to_bool in
  let val_type = JsonUtil.member "val_type" assoc |> JsonUtil.to_string in
  let value = JsonUtil.member "value" assoc |> JsonUtil.to_string in
  if is_enum |> not && val_type <> "Object" then mmap
  else
    let new_gc =
      match InstanceInfo.M.find_opt cname mmap with
      | Some old_gc when List.mem value old_gc |> not -> List.cons value old_gc
      | Some old_gc -> old_gc
      | None -> [ value ]
    in
    InstanceInfo.M.add cname new_gc mmap

let add_constant c_or_m_name assoc cmap =
  let value = JsonUtil.member "value" assoc |> JsonUtil.to_string in
  let new_c =
    match PrimitiveInfo.ClassMap.find_opt c_or_m_name cmap with
    | Some old_c when List.mem value old_c |> not -> List.cons value old_c
    | Some old_c -> old_c
    | None -> [ value ]
  in
  PrimitiveInfo.ClassMap.add c_or_m_name new_c cmap

let of_gconst_json json =
  List.fold_left
    (fun mmap cname ->
      let assoc = JsonUtil.member cname json in
      add_gconst cname assoc mmap)
    InstanceInfo.M.empty (JsonUtil.keys json)

let of_primitive_json mmap json =
  List.fold_left
    (fun mmap c_or_m_name ->
      let assoc = JsonUtil.member c_or_m_name json in
      let val_type = JsonUtil.member "val_type" assoc |> JsonUtil.to_string in
      if
        List.mem val_type basic_types |> not
        || JsonUtil.member "is_enum" assoc |> JsonUtil.to_bool
      then mmap
      else
        let cmap =
          match PrimitiveInfo.TypeMap.find_opt (str_to_typ val_type) mmap with
          | Some m -> m
          | _ -> PrimitiveInfo.ClassMap.empty
        in
        let new_cmap = add_constant c_or_m_name assoc cmap in
        PrimitiveInfo.TypeMap.add (str_to_typ val_type) new_cmap mmap)
    mmap (JsonUtil.keys json)
