let pre_space = Str.regexp "^[ \t\r\n]+"

let post_space = Str.regexp "[ \t\r\n]+$"

let bk = Str.regexp "[{}]"

let arrow = Str.regexp "->"

let max = Str.regexp "max("

let min = Str.regexp "min("

let bk2 = Str.regexp "[)\\[\\]]"

let bm = Str.regexp ","

let colon = Str.regexp ":"

let eq = Str.regexp "="

let neq = Str.regexp "!="

let ge = Str.regexp ">="

let gt = Str.regexp ">"

let le = Str.regexp "<="

let lt = Str.regexp "<"

let in_n = Str.regexp "in_N"

let in_bk = Str.regexp "in\\["

let open_bk = Str.regexp "\\["

let end_bk = Str.regexp "\\]"

let ots = Str.regexp "not_in\\["

let remain_symbol = Str.regexp "[&{}]"

let remain_symbol2 = Str.regexp "}*[ \t\r\n]+}$"

let o_bks = Str.regexp "\\[{"

let c_bks = Str.regexp "}\\]"

let o_bk = Str.regexp "{"

let c_bk = Str.regexp "}"

let symbol = Str.regexp "^[avu][0-9]+$"

let index = Str.regexp "^\\[[avu][0-9]+\\]$"

let any = Str.regexp "\\*"

let start_bm = Str.regexp "^,[ \t\r\n]*"

let ref = Str.regexp "^[ \t\r\n]*->[ \t\r\n]*$"

let array = Str.regexp ".+\\[_\\*_\\].*"

let rm_array = Str.regexp "\\[_\\*_\\](\\*)"

let dollar = Str.regexp "\\$"

let dot = Str.regexp "\\."

let space = Str.regexp " "

let space2 = Str.regexp "  "

let test_class = Str.regexp "UnitconTest[0-9]+\\.class"

let test_file = Str.regexp "UnitconTest[0-9]+\\.java"

let global_rm exp str = Str.global_replace exp "" str

let first_rm exp str = Str.replace_first exp "" str

let rm_space str =
  let str = first_rm pre_space str in
  first_rm post_space str

let remove_bk str = global_rm bk str |> rm_space

let rm_first_rest str = global_rm (Str.regexp "^, ") str

let package = Str.regexp "package"
