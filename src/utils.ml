let get_class_name m_name =
  Regexp.first_rm ("\\.[^\\.]+(.*)" |> Str.regexp) m_name

let replace_nested_symbol str = Str.global_replace Regexp.dollar "." str

let is_init_method m_name =
  Str.string_match (".*\\.<init>" |> Str.regexp) m_name 0

let get_array_class_name name =
  if name = "String" || name = "Object" then name
  else String.lowercase_ascii name

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
      "Object";
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
      "Object";
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
      "Object";
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

let get_array_dim_from_class_name f =
  Regexp.first_rm (Str.regexp ".*Array") f
  |> int_of_string

let is_modeling_set fname =
  is_array_set fname
  || Str.string_match ("java.util.Map.put" |> Str.regexp) fname 0
