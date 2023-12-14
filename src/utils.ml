let get_class_name m_name =
  Regexp.first_rm ("\\.[^\\.]+(.*)" |> Str.regexp) m_name

let replace_nested_symbol str = Str.global_replace Regexp.dollar "." str

let is_init_method m_name =
  Str.string_match (".*\\.<init>" |> Str.regexp) m_name 0

let is_array_init fname =
  let arr =
    [ "Int"; "Long"; "Float"; "Double"; "Bool"; "Char"; "String"; "Object" ]
  in
  let rec check arr =
    match arr with
    | h :: t ->
        if Str.string_match (h ^ "Array\\.<init>" |> Str.regexp) fname 0 then
          true
        else check t
    | [] -> false
  in
  check arr

let is_array_set fname =
  let arr =
    [ "Int"; "Long"; "Float"; "Double"; "Bool"; "Char"; "String"; "Object" ]
  in
  let rec check arr =
    match arr with
    | h :: t ->
        if Str.string_match (h ^ "Array\\.set" |> Str.regexp) fname 0 then true
        else check t
    | [] -> false
  in
  check arr

let is_array package =
  let arr =
    [ "Int"; "Long"; "Float"; "Double"; "Bool"; "Char"; "String"; "Object" ]
  in
  let rec check arr =
    match arr with
    | h :: t ->
        if Str.string_match (h ^ "Array$" |> Str.regexp) package 0 then true
        else check t
    | [] -> false
  in
  check arr