open! Javalib_pack
open Utils
module UsedClasses = Set.Make (String)
module Callee = Set.Make (String)

let used_classes = ref UsedClasses.empty

let is_file f =
  try (Unix.stat f).Unix.st_kind = Unix.S_REG
  with Unix.Unix_error (Unix.ENOENT, _, _) -> false

let is_test_class name =
  Str.string_match (Str.regexp "Test.*") name 0
  || Str.string_match (Str.regexp ".*Test$") name 0

let is_lambda_class name =
  match Str.search_forward (Str.regexp "\\$Lambda\\$[_0-9]+") name 0 with
  | exception Not_found -> false
  | _ -> true

let is_anonymous name =
  let check_int name =
    match Str.search_forward (Str.regexp "\\$[0-9]+") name 0 with
    | exception Not_found -> false
    | _ -> true
  in
  is_lambda_class name || check_int name

let is_ignore_class name = is_test_class name || is_anonymous name

let make_dir_absolute dir =
  if Filename.is_relative dir then Filename.(Unix.getcwd () / dir) else dir

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

let string_of_access access =
  match access with
  | `Private -> "private"
  | `Protected -> "protected"
  | `Default -> "default"
  | `Public -> "public"

let rec string_of_value_type = function
  | JBasics.TBasic bt -> string_of_basic_type bt
  | TObject ot -> string_of_object_type ot

and string_of_basic_type = function
  | `Bool -> "boolean"
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

let string_of_args args =
  let rec make_arg_code args =
    match args with hd :: tl -> "," ^ hd ^ make_arg_code tl | _ -> ""
  in
  "(" ^ Regexp.first_rm (Str.regexp "^,") (make_arg_code args) ^ ")"

let string_of_jmethod_or_interface joi =
  match joi with
  | `InterfaceMethod (cn, ms) -> JBasics.cn_name cn ^ "." ^ JBasics.ms_name ms
  | `Method (cn, ms) -> JBasics.cn_name cn ^ "." ^ JBasics.ms_name ms

let string_of_lambda m =
  match m with
  | `InvokeInterface (cn, ms) -> JBasics.cn_name cn ^ "." ^ JBasics.ms_name ms
  | `InvokeSpecial joi -> string_of_jmethod_or_interface joi
  | `InvokeStatic joi -> string_of_jmethod_or_interface joi
  | `InvokeVirtual (obj, ms) ->
      string_of_object_type obj ^ "." ^ JBasics.ms_name ms
  | _ -> ""

let get_lambda_method t =
  match t with
  | `Dynamic b_method ->
      List.fold_left
        (fun acc arg ->
          match arg with
          | `MethodHandle m -> string_of_lambda m :: acc
          | _ -> acc)
        [] b_method.JBasics.bm_args
  | _ -> []

let get_complete_lambda_method lambda_list all_methods =
  List.fold_left
    (fun acc x ->
      List.fold_left
        (fun acc2 lambda ->
          if Str.string_match (Str.regexp (lambda ^ "(")) x 0 then
            Callee.add x acc2
          else acc2)
        acc lambda_list)
    Callee.empty all_methods

let string_of_class t =
  match t with
  | `Dynamic _ -> ""
  | `Interface _ -> ""
  | `Special (_, cn) -> JBasics.cn_name cn
  | `Static (_, cn) -> JBasics.cn_name cn
  | `Virtual obj -> string_of_object_type obj

let get_callee_methods caller_ms all_methods =
  let impl = caller_ms.Javalib.cm_implementation in
  match impl with
  | Javalib.Java code ->
      Array.fold_left
        (fun acc op ->
          match op with
          | JCode.OpInvoke (typ, ms) ->
              let class_name = string_of_class typ in
              let lambda_method = get_lambda_method typ in
              if class_name = "" && lambda_method <> [] then
                Callee.union
                  (get_complete_lambda_method lambda_method all_methods)
                  acc
              else if class_name = "" then acc
              else
                let name = JBasics.ms_name ms in
                let raw_args =
                  List.map
                    (fun vt -> string_of_value_type vt)
                    (JBasics.ms_args ms)
                in
                Callee.add
                  (class_name ^ "." ^ name ^ string_of_args raw_args)
                  acc
          | _ -> acc)
        Callee.empty (Lazy.force code).JCode.c_code
  | Native -> Callee.empty

let get_methods_names cname methods =
  JBasics.MethodMap.fold
    (fun _ m acc ->
      match m with
      | Javalib.ConcreteMethod c ->
          let name = JBasics.ms_name c.cm_signature in
          let raw_args =
            List.map
              (fun vt -> string_of_value_type vt)
              (JBasics.ms_args c.cm_signature)
          in
          (cname ^ "." ^ name ^ string_of_args raw_args) :: acc
      | Javalib.AbstractMethod a ->
          let name = JBasics.ms_name a.am_signature in
          let raw_args =
            List.map
              (fun vt -> string_of_value_type vt)
              (JBasics.ms_args a.am_signature)
          in
          (cname ^ "." ^ name ^ string_of_args raw_args) :: acc)
    methods []

let handle_methods cname methods =
  JBasics.MethodMap.fold
    (fun _ m acc ->
      match m with
      | Javalib.ConcreteMethod c ->
          let name = JBasics.ms_name c.cm_signature in
          let access = string_of_access c.cm_access in
          let rtype =
            `String (JBasics.ms_rtype c.cm_signature |> string_of_value_type_opt)
          in
          let raw_args =
            List.map
              (fun vt -> string_of_value_type vt)
              (JBasics.ms_args c.cm_signature)
          in
          let args = `List (List.map (fun v -> `String v) raw_args) in
          let callee =
            `List
              (List.map
                 (fun m -> `String m)
                 (get_callee_methods c (get_methods_names cname methods)
                 |> Callee.elements))
          in
          let item =
            [
              ("access", `String access);
              ("is_static", `Bool (Javalib.is_static_method m));
              ("rtype", rtype);
              ("args", args);
              ("callee", callee);
            ]
          in
          (cname ^ "." ^ name ^ string_of_args raw_args, `Assoc item) :: acc
      | Javalib.AbstractMethod a ->
          let name = JBasics.ms_name a.am_signature in
          let access = string_of_access a.am_access in
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
              ("access", `String access);
              ("is_static", `Bool (Javalib.is_static_method m));
              ("rtype", rtype);
              ("args", args);
              ("callee", `List []);
            ]
          in
          (cname ^ "." ^ name ^ string_of_args raw_args, `Assoc item) :: acc)
    methods []

let handle_interface i =
  let cname = JBasics.cn_name i.Javalib.i_name in
  let access = string_of_access i.i_access in
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
      ("access", `String access);
      ("is_abstract", is_abstract);
      ("is_interface", `Bool true);
      ("interfaces", interfaces);
      ("inner_class", `Assoc inner_class);
    ]
  in
  (cname, `Assoc item)

let handle_class c =
  let cname = JBasics.cn_name c.Javalib.c_name in
  let access = string_of_access c.c_access in
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
  let methods = handle_methods cname c.c_methods in
  let item =
    [
      ("access", `String access);
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
  let name = Javalib.get_name ioc in
  let simple_name = JBasics.cn_simple_name name in
  let full_name = JBasics.cn_name name in
  if is_ignore_class simple_name || UsedClasses.mem full_name !used_classes then (
    if !Cmdline.debug then Logger.info "ignore class: %s" full_name;
    acc)
  else (
    used_classes := UsedClasses.add full_name !used_classes;
    match ioc with
    | Javalib.JInterface i -> handle_interface i :: acc
    | Javalib.JClass c -> handle_class c :: acc)

let run p =
  let (x : (string * Yojson.Safe.t) list) =
    fold (fun acc ioc -> fold_class acc ioc) [] p
  in
  let r = `Assoc x in
  let oc = Filename.(!Cmdline.out_dir / "class-info.json") |> open_out in
  Yojson.Safe.pretty_to_channel oc r;
  close_out oc
