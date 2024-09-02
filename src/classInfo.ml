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

let string_of_value_type_opt = function
  | Some vt -> string_of_value_type vt
  | None -> "void"

let string_of_args_list args =
  let rec make_arg_code args =
    match args with hd :: tl -> "," ^ hd ^ make_arg_code tl | _ -> ""
  in
  "(" ^ Regexp.first_rm (Str.regexp "^,") (make_arg_code args) ^ ")"

let handle_methods methods =
  JBasics.MethodMap.fold
    (fun _ m acc ->
      match m with
      | Javalib.ConcreteMethod c ->
          let name = JBasics.ms_name c.cm_signature in
          let access =
            match c.cm_access with
            | `Default -> `String "default"
            | `Private -> `String "private"
            | `Protected -> `String "protected"
            | _ -> `String "public"
          in
          let rtype =
            `String (JBasics.ms_rtype c.cm_signature |> string_of_value_type_opt)
          in
          let raw_args =
            List.map
              (fun vt -> string_of_value_type vt)
              (JBasics.ms_args c.cm_signature)
          in
          let args = `List (List.map (fun v -> `String v) raw_args) in
          let item =
            [
              ("access", access);
              ("is_static", `Bool (Javalib.is_static_method m));
              ("rtype", rtype);
              ("args", args);
            ]
          in
          (name ^ string_of_args_list raw_args, `Assoc item) :: acc
      | Javalib.AbstractMethod a ->
          let name = JBasics.ms_name a.am_signature in
          let access =
            match a.am_access with
            | `Default -> `String "default"
            | `Private -> `String "private"
            | `Protected -> `String "protected"
            | _ -> `String "public"
          in
          let rtype =
            `String (JBasics.ms_rtype a.am_signature |> string_of_value_type_opt)
          in
          let raw_args =
            List.map
              (fun vt -> string_of_value_type vt)
              (JBasics.ms_args a.am_signature)
          in
          let args = `List (List.map (fun v -> `String v) raw_args) in
          let item =
            [
              ("access", access);
              ("is_static", `Bool (Javalib.is_static_method m));
              ("rtype", rtype);
              ("args", args);
            ]
          in
          (name ^ string_of_args_list raw_args, `Assoc item) :: acc)
    methods []

let handle_interface i =
  let cname = JBasics.cn_name i.Javalib.i_name in
  let access =
    match i.i_access with
    | `Default -> `String "default"
    | _ -> `String "public"
  in
  let pkg_name = `String (JBasics.cn_package i.i_name |> String.concat ".") in
  let interfaces =
    `List (List.map (fun i -> `String (JBasics.cn_name i)) i.i_interfaces)
  in
  let inner_class =
    List.map
      (fun ic ->
        match ic.Javalib.ic_class_name with
        | Some s -> (JBasics.cn_name s, `Bool ic.Javalib.ic_static)
        | None -> ("", `Bool false))
      i.i_inner_classes
  in
  let is_abstract = `Bool false in
  let item =
    [
      ("pkg_name", pkg_name);
      ("access", access);
      ("is_abstract", is_abstract);
      ("is_interface", `Bool true);
      ("interfaces", interfaces);
      ("inner_class", `Assoc inner_class);
    ]
  in
  (cname, `Assoc item)

let handle_class c =
  let cname = JBasics.cn_name c.Javalib.c_name in
  let access =
    match c.c_access with
    | `Default -> `String "default"
    | _ -> `String "public"
  in
  let pkg_name = `String (JBasics.cn_package c.c_name |> String.concat ".") in
  let super_class =
    match c.c_super_class with
    | Some s -> `String (JBasics.cn_name s)
    | _ -> `Null
  in
  let interfaces =
    `List (List.map (fun i -> `String (JBasics.cn_name i)) c.c_interfaces)
  in
  let inner_class =
    List.map
      (fun ic ->
        match ic.Javalib.ic_class_name with
        | Some s -> (JBasics.cn_name s, `Bool ic.Javalib.ic_static)
        | None -> ("", `Bool false))
      c.c_inner_classes
  in
  let is_abstract = `Bool c.c_abstract in
  let methods = handle_methods c.c_methods in
  let item =
    [
      ("pkg_name", pkg_name);
      ("access", access);
      ("is_abstract", is_abstract);
      ("is_interface", `Bool false);
      ("super_class", super_class);
      ("interfaces", interfaces);
      ("inner_class", `Assoc inner_class);
      ("methods", `Assoc methods);
    ]
  in
  (cname, `Assoc item)

let fold_class acc ioc : (string * Yojson.Safe.t) list =
  match ioc with
  | Javalib.JInterface i -> handle_interface i :: acc
  | Javalib.JClass c -> handle_class c :: acc

let run p =
  let (x : (string * Yojson.Safe.t) list) =
    fold (fun acc ioc -> fold_class acc ioc) [] p
  in
  let r = `Assoc x in
  let cons = Filename.concat in
  let p_dir = if Filename.is_relative p then cons (Unix.getcwd ()) p else p in
  let oc =
    cons (cons p_dir "unitcon_properties") "class_info.json" |> open_out
  in
  Yojson.Safe.pretty_to_channel oc r;
  close_out oc
