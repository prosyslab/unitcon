module F = Format
module L = Logger
module ImportSet = Set.Make (String)

let read_all_string in_chan =
  let res = Buffer.create 1024 in
  let rec loop () =
    match input_line in_chan with
    | line ->
        Buffer.add_string res line;
        Buffer.add_string res "\n";
        loop ()
    | exception End_of_file -> Buffer.contents res
  in
  loop ()

let execute command =
  L.info "Current working directory: %s" (Unix.getcwd ());
  L.info "Running command: %s" command;
  Sys.command command

let print_and_log ?(quiet = false) =
  if quiet then F.ifprintf F.err_formatter
  else L.info ~to_console:true ~new_line:true

module Filename = struct
  include Filename

  let ( / ) l r = concat l r

  let cwd = Sys.getcwd ()

  let resolve path = if is_relative path then Unix.realpath path else path

  let exists = Sys.file_exists

  let copy src dst =
    let in_fd = Unix.openfile src [ Unix.O_RDONLY ] 0 in
    let out_fd =
      Unix.openfile dst [ Unix.O_WRONLY; Unix.O_CREAT; Unix.O_TRUNC ] 0o666
    in
    let in_chan = Unix.in_channel_of_descr in_fd in
    let out_chan = Unix.out_channel_of_descr out_fd in
    let data = read_all_string in_chan in
    output_string out_chan data;
    close_in in_chan;
    close_out out_chan

  let mkdir ?(exists_ok = false) dir perm =
    if not (exists dir) then Unix.mkdir dir perm
    else if exists_ok then ()
    else L.error "Directory %s already exists" dir

  let mkpath ?(exists_ok = false) path perm =
    let path = Str.split (Str.regexp dir_sep) (resolve path) in
    let rec mkdeps path = function
      | [] -> ()
      | f :: deps ->
          let p = path / f in
          mkdir ~exists_ok p perm;
          mkdeps p deps
    in
    mkdeps "/" path

  let rename = Unix.rename

  let unlink = Unix.unlink

  let rec unlink_dir path =
    if not (exists path) then ()
    else if Sys.is_directory path then
      Array.iter
        (fun file ->
          let abspath = resolve (path / file) in
          if Sys.is_directory abspath then unlink_dir abspath
          else unlink abspath)
        (Sys.readdir path)
    else L.error "Path %s is not a directory" path

  let remove_file f =
    if Sys.file_exists f then
      try Unix.unlink f with _ -> L.info "Fail delete %s" f
end

let input_path = "unitcon-properties"

let unitcon_path =
  let path = Filename.dirname Sys.argv.(0) in
  if Filename.is_relative path then Filename.(Filename.cwd / path) else path

let dot_to_dir_sep path =
  Str.global_replace (Str.regexp "\\.") Filename.dir_sep path

let get_class_name m_name = Regexp.first_rm (Str.regexp "\\.[^\\.]+(.*)") m_name

let get_package_name c_name =
  Regexp.first_rm (Str.regexp "\\$.*") c_name
  |> Regexp.first_rm (Str.regexp "\\.[^\\.]+$")

let replace_nested_symbol str = Str.global_replace Regexp.dollar "." str

let is_init_method m_name = Str.string_match (Str.regexp ".*\\.<init>") m_name 0

let is_lambda_class name =
  match Str.search_forward (Str.regexp "\\$Lambda\\$[_0-9]+") name 0 with
  | exception Not_found -> false
  | _ -> true

let is_lambda name =
  match Str.search_forward (Str.regexp "\\.lambda\\$") name 0 with
  | exception Not_found -> false
  | _ -> true

let is_anonymous m_name =
  let check_int name =
    match Str.search_forward (Str.regexp "\\$[0-9]+") name 0 with
    | exception Not_found -> false
    | _ -> true
  in
  is_lambda_class m_name || check_int (get_class_name m_name)

let get_array_class_name name =
  let arr = [ "Int"; "Long"; "Byte"; "Float"; "Double"; "Bool"; "Char" ] in
  if List.mem name arr then String.lowercase_ascii name else name

let is_array_init fname =
  let arr =
    [
      "Int";
      "Long";
      "Byte";
      "Float";
      "Double";
      "Bool";
      "Char";
      "String";
      "Object.*";
    ]
  in
  let rec check arr =
    match arr with
    | h :: t ->
        if Str.string_match (h ^ "Array[0-9]*\\.<init>" |> Str.regexp) fname 0
        then true
        else check t
    | [] -> false
  in
  check arr

let is_array_set fname =
  let arr =
    [
      "Int";
      "Long";
      "Byte";
      "Float";
      "Double";
      "Bool";
      "Char";
      "String";
      "Object.*";
    ]
  in
  let rec check arr =
    match arr with
    | h :: t ->
        if Str.string_match (h ^ "Array[0-9]*\\.set" |> Str.regexp) fname 0 then
          true
        else check t
    | [] -> false
  in
  check arr

let is_array package =
  let arr =
    [
      "Int";
      "Long";
      "Byte";
      "Float";
      "Double";
      "Bool";
      "Char";
      "String";
      "Object.*";
    ]
  in
  let rec check arr =
    match arr with
    | h :: t ->
        if Str.string_match (h ^ "Array[0-9]*$" |> Str.regexp) package 0 then
          true
        else check t
    | [] -> false
  in
  check arr

let rm_object_array_import i =
  if Str.string_match (Str.regexp "Object.+Array[0-9]*$") i 0 then
    Regexp.first_rm (Str.regexp "^Object") i
    |> Regexp.first_rm (Str.regexp "Array[0-9]*$")
  else i

let get_array_dim_from_class_name f =
  Regexp.first_rm (Str.regexp ".*Array") f |> int_of_string

let is_modeling_set fname =
  is_array_set fname
  || Str.string_match (Str.regexp "java.util.Map.put") fname 0

let is_lambda_method m_name = is_lambda m_name || is_lambda_class m_name

let filter_list =
  [
    "java.io.FileInputStream.<init>(java.lang.String)";
    "java.io.FileInputStream.<init>(java.io.FileDescriptor)";
    "java.io.SequenceInputStream.<init>(java.io.InputStream)";
    "java.io.SequenceInputStream.<init>(java.io.InputStream,java.io.InputStream)";
    "java.io.ByteArrayInputStream.<init>(byte[])";
    "java.io.ByteArrayInputStream.<init>(byte[],int,int)";
    "java.io.PipedInputStream.<init>()";
    "java.io.PipedInputStream.<init>(int)";
    "java.io.PipedInputStream.<init>(java.io.PipedOutputStream)";
    "java.io.PipedInputStream.<init>(java.io.PipedOutputStream,int)";
    "java.io.SequenceInputStream.<init>(java.io.InputStream,java.io.InputStream)";
    "java.io.SequenceInputStream.<init>(java.util.Enumeration)";
    "java.io.BufferedInputStream.<init>(java.io.InputStream)";
    "java.io.BufferedInputStream.<init>(java.io.InputStream,int)";
    "java.io.DataInputStream.<init>(java.io.InputStream)";
    "java.io.PushbackInputStream.<init>(java.io.InputStream)";
    "java.io.PushbackInputStream.<init>(java.io.InputStream,int)";
    "java.io.FileOutputStream.<init>(java.lang.String)";
    "java.io.FileOutputStream.<init>(java.lang.String,boolean)";
    "java.io.FileOutputStream.<init>(java.io.FileDescriptor)";
    "java.io.PipedOutputStream.<init>()";
    "java.io.PipedOutputStream.<init>(java.io.PipedInputStream)";
    "java.io.FilterOutputStream.<init>(java.io.OutputStream)";
    "java.io.BufferedOutputStream.<init>(java.io.OutputStream)";
    "java.io.BufferedOutputStream.<init>(java.io.OutputStream,int)";
    "java.io.DataOutputStream.<init>(java.io.OutputStream)";
    "java.io.BufferedReader.<init>(java.io.Reader)";
    "java.io.BufferedReader.<init>(java.io.Reader,int)";
    "java.io.LineNumberReader.<init>(java.io.Reader)";
    "java.io.LineNumberReader.<init>(java.io.Reader,int)";
    "java.io.FileReader.<init>(java.lang.String)";
    "java.io.PushbackReader.<init>(java.io.Reader)";
    "java.io.PushbackReader.<init>(java.io.Reader,int)";
    "java.io.PipedReader.<init>()";
    "java.io.PipedReader.<init>(int)";
    "java.io.PipedReader.<init>(java.io.PipedWriter)";
    "java.io.PipedReader.<init>(java.io.PipedWriter,int)";
    "java.io.PipedWriter.<init>()";
    "java.io.PipedWriter.<init>(java.io.PipedReader)";
    "java.io.BufferedWriter.<init>(java.io.Writer)";
    "java.io.BufferedWriter.<init>(java.io.Writer,int)";
    "java.io.OutputStreamWriter.<init>(java.io.OutputStream)";
    "java.io.OutputStreamWriter.<init>(java.io.OutputStream,java.nio.charset.Charset)";
    "java.io.OutputStreamWriter.<init>(java.io.OutputStream,java.nio.charset.CharsetEncoder)";
    "java.io.OutputStreamWriter.<init>(java.io.OutputStream,java.lang.String)";
    "java.io.PrintWriter.<init>(java.io.OutputStream)";
    "java.io.PrintWriter.<init>(java.io.OutputStream,boolean)";
    "java.io.PrintWriter.<init>(java.lang.String)";
    "java.io.PrintWriter.<init>(java.lang.String,java.lang.String)";
    "java.io.PrintWriter.<init>(java.io.Writer)";
    "java.io.PrintWriter.<init>(java.io.Writer,boolean)";
    "java.io.FileWriter.<init>(java.io.FileDescriptor)";
    "java.io.FileWriter.<init>(java.lang.String)";
    "java.io.FileWriter.<init>(java.lang.String,boolean)";
    "java.io.File.<init>(java.net.URI)";
    "java.io.File.<init>(java.io.File,java.lang.String)";
    "java.io.File.<init>(java.lang.String,java.lang.String)";
  ]
