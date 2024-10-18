open! Javalib_pack

let is_file f =
  try (Unix.stat f).Unix.st_kind = Unix.S_REG
  with Unix.Unix_error (Unix.ENOENT, _, _) -> false

let make_dir_absolute dir =
  if Filename.is_relative dir then Filename.concat (Unix.getcwd ()) dir else dir

(* copyed and modified from https://github.com/javalib-team/javalib/blob/ae04c6b3c2331b01876dcf7a0dade45e51c9574b/src/jFile.ml#L361 *)
let fold f acc filename =
  if is_file filename && Filename.check_suffix filename ".class" then (
    let cp = Javalib.class_path (Filename.dirname filename) in
    let file = Filename.chop_suffix (Filename.basename filename) ".class" in
    let acc = f acc (Javalib.get_class cp (JBasics.make_cn file)) in
    Javalib.close_class_path cp;
    acc)
  else if
    is_file filename
    && (Filename.check_suffix filename ".jar"
       || Filename.check_suffix filename ".zip")
  then
    let cp = Filename.dirname filename in
    let filename = Filename.basename filename in
    Javalib.read
      (Javalib.make_directories cp)
      (fun acc c -> f acc c)
      acc [ filename ]
  else if Sys.is_directory filename then (
    let cp = filename in
    let jar_files = ref [] in
    let dir = Unix.opendir (make_dir_absolute filename) in
    try
      while true do
        let next = Unix.readdir dir in
        if
          Filename.check_suffix next ".jar" || Filename.check_suffix next ".zip"
        then jar_files := next :: !jar_files
      done;
      assert false
    with End_of_file ->
      Unix.closedir dir;
      Javalib.read
        (Javalib.make_directories cp)
        (fun acc c -> f acc c)
        acc !jar_files)
  else (
    prerr_string filename;
    prerr_endline
      " is not a valid class file, nor a valid jar (or zip) file, nor a \
       directory";
    exit 0)

let rec string_of_value_type = function
  | JBasics.TBasic bt -> string_of_basic_type bt
  | TObject ot -> string_of_object_type ot

and string_of_basic_type = function
  | `Bool -> "bool"
  | `Byte -> "byte"
  | `Char -> "char"
  | `Short -> "short"
  | `Int -> "int"
  | `Long -> "long"
  | `Float -> "float"
  | `Double -> "double"

and string_of_object_type = function
  | TArray vt -> string_of_value_type vt ^ "[]"
  | TClass c -> JBasics.cn_name c

let basic_types =
  [
    "bool";
    "byte";
    "char";
    "short";
    "int";
    "long";
    "float";
    "double";
    "String";
    "java.lang.String";
  ]

let assoc_of_value ?(is_enum = false) typ value =
  `Assoc
    [
      ("is_enum", `Bool is_enum);
      ("val_type", `String typ);
      ("value", `String value);
    ]

let get_const name = function
  | `Byte b when b > 32 && b < 127 ->
      let char_value = Char.chr b |> String.make 1 in
      [
        (name, assoc_of_value "byte" (string_of_int b));
        (name, assoc_of_value "char" char_value);
        (name, assoc_of_value "String" char_value);
        (name, assoc_of_value "int" (string_of_int b));
      ]
  | `Byte b ->
      [
        (name, assoc_of_value "byte" (string_of_int b));
        (name, assoc_of_value "int" (string_of_int b));
      ]
  | `Double d -> [ (name, assoc_of_value "double" (string_of_float d)) ]
  | `Float f -> [ (name, assoc_of_value "float" (string_of_float f)) ]
  | `Int i -> [ (name, assoc_of_value "int" (Int32.to_int i |> string_of_int)) ]
  | `Long l ->
      [ (name, assoc_of_value "long" (Int64.to_int l |> string_of_int)) ]
  | `Short s ->
      [
        (name, assoc_of_value "short" (string_of_int s));
        (name, assoc_of_value "int" (string_of_int s));
      ]
  | `String s -> [ (name, assoc_of_value "String" (JBasics.jstr_raw s)) ]
  | _ -> []

let get_case_const mname matches =
  List.fold_left
    (fun acc (case, _) ->
      let value = Int32.to_int case in
      let str_of_value = string_of_int value in
      if value > 32 && value < 127 then
        (mname, assoc_of_value "char" str_of_value)
        :: (mname, assoc_of_value "String" str_of_value)
        :: (mname, assoc_of_value "int" str_of_value)
        :: acc
      else (mname, assoc_of_value "int" str_of_value) :: acc)
    [] matches

let get_opconst name m =
  let impl = m.Javalib.cm_implementation in
  match impl with
  | Javalib.Java code ->
      Array.fold_left
        (fun acc op ->
          match op with
          | JCode.OpConst const -> List.rev_append (get_const name const) acc
          | OpLookupSwitch (_, matches) ->
              List.rev_append (get_case_const name matches) acc
          | _ -> acc)
        [] (Lazy.force code).JCode.c_code
  | _ -> []

let handle_methods cname methods =
  JBasics.MethodMap.fold
    (fun _ m acc ->
      match m with
      | Javalib.ConcreteMethod c ->
          let mname = JBasics.ms_name c.cm_signature in
          let name = if mname = "<init>" then cname else cname ^ "." ^ mname in
          List.rev_append (get_opconst name c) acc
      | Javalib.AbstractMethod _ ->
          (* if method m is abstract method then we can not get constants from method *)
          acc)
    methods []

let handle_field_constant cname fields =
  let usable_field cf =
    cf.Javalib.cf_access = `Public && cf.Javalib.cf_static
  in
  JBasics.FieldMap.fold
    (fun fs cf acc ->
      let ft = JBasics.fs_type fs in
      if
        List.mem (ft |> string_of_value_type) basic_types |> not
        && usable_field cf
      then
        let item = assoc_of_value "Object" (cname ^ "." ^ JBasics.fs_name fs) in
        (ft |> string_of_value_type, item) :: acc
      else acc)
    fields []

let handle_enum_constant cname consts =
  Array.fold_left
    (fun acc v ->
      match v with
      | JBasics.ConstNameAndType (name, des) -> (
          match des with
          | SValue vt
            when List.mem (vt |> string_of_value_type) basic_types |> not ->
              let item =
                assoc_of_value ~is_enum:true "Object" (cname ^ "." ^ name)
              in
              (vt |> string_of_value_type, item) :: acc
          | _ -> acc)
      | _ -> acc)
    [] consts

let handle_class c =
  let cname = JBasics.cn_name c.Javalib.c_name in
  let is_enum = c.c_enum in
  let is_usable_class =
    if c.c_access = `Public && not c.c_abstract then true else false
  in
  let const = if is_enum then [] else handle_methods cname c.c_methods in
  let g_const =
    if is_usable_class then
      if is_enum then handle_enum_constant cname c.c_consts
      else handle_field_constant cname c.c_fields
    else []
  in
  List.rev_append const g_const

let fold_class acc ioc : (string * Yojson.Safe.t) list =
  match ioc with
  | Javalib.JInterface _ -> acc
  | Javalib.JClass c -> List.rev_append (handle_class c) acc

let run p =
  let (x : (string * Yojson.Safe.t) list) =
    fold (fun acc ioc -> fold_class acc ioc) [] p
  in
  let r = `Assoc x in
  let cons = Filename.concat in
  let p_dir = if Filename.is_relative p then cons (Unix.getcwd ()) p else p in
  let oc =
    cons (cons p_dir "unitcon_properties") "constant_info.json" |> open_out
  in
  Yojson.Safe.pretty_to_channel oc r;
  close_out oc
