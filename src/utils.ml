module ImportSet = Set.Make (struct
  type t = string

  let compare = compare
end)

let dot_to_dir_sep path =
  Str.global_replace (Str.regexp "\\.") Filename.dir_sep path

let get_class_name m_name = Regexp.first_rm (Str.regexp "\\.[^\\.]+(.*)") m_name

let get_package_name c_name =
  Regexp.first_rm (Str.regexp "\\$.*") c_name
  |> Regexp.first_rm (Str.regexp "\\.[^\\.]+$")

let replace_nested_symbol str = Str.global_replace Regexp.dollar "." str

let is_init_method m_name = Str.string_match (Str.regexp ".*\\.<init>") m_name 0

let is_anonymous m_name =
  let check_int name =
    match int_of_string_opt name with Some _ -> true | _ -> false
  in
  let rec check lst =
    match lst with hd :: tl -> check_int hd || check tl | _ -> false
  in
  Str.string_match (Str.regexp ".*\\$Lambda\\$_[0-9]+.*") m_name 0
  || get_class_name m_name |> String.split_on_char '$' |> check

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

let filter_list =
  [
    "java.io.FileInputStream.<init>(java.lang.String)";
    "java.io.FileInputStream.<init>(java.io.FileDescriptor)";
    "java.io.SequenceInputStream.<init>(java.io.InputStream)";
    "java.io.SequenceInputStream.<init>(java.io.InputStream,java.io.InputStream)";
    "java.io.PipedInputStream.<init>()";
    "java.io.PipedInputStream.<init>(int)";
    "java.io.BufferedReader.<init>(java.io.Reader)";
    "java.io.BufferedReader.<init>(java.io.Reader,int)";
    "java.io.LineNumberReader.<init>(java.io.Reader)";
    "java.io.LineNumberReader.<init>(java.io.Reader,int)";
    "java.io.FileReader.<init>(java.lang.String)";
    "java.io.PushbackReader.<init>(java.io.Reader)";
    "java.io.PushbackReader.<init>(java.io.Reader,int)";
    "java.io.PipedReader.<init>()";
    "java.io.PipedReader.<init>(int)"
  ]
