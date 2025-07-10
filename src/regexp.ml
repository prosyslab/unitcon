let pre_space = Str.regexp "^[ \t\r\n]+"

let post_space = Str.regexp "[ \t\r\n]+$"

let bk = Str.regexp "[{}]"

let arrow = Str.regexp "->"

let max = Str.regexp "max("

let min = Str.regexp "min("

let end_bk2 = Str.regexp ")"

let bm = Str.regexp ","

let colon = Str.regexp ":"

let eq = Str.regexp "="

let neq = Str.regexp "!="

let ge = Str.regexp ">="

let gt = Str.regexp ">"

let le = Str.regexp "<="

let lt = Str.regexp "<"

let in_n = Str.regexp "in_N" (* check between[-inf +inf] *)

let in_bk = Str.regexp "in\\["

let open_bk = Str.regexp "\\["

let end_bk = Str.regexp "\\]"

let open_end_bk = Str.regexp "\\[\\]"

let not_in_bk = Str.regexp "not_in\\["

let remain_symbol = Str.regexp "[&{}]"

let remain_symbol2 = Str.regexp "}*[ \t\r\n]+}$"

let o_bks = Str.regexp "\\[[ \t\r\n]*{"

let c_bks = Str.regexp "}[ \t\r\n]*\\]"

let o_bk = Str.regexp "{"

let c_bk = Str.regexp "}"

let symbol_prefix = Str.regexp "^[avu]"

let anony_symbol_prefix = Str.regexp "v-"

let symbol = Str.regexp "^[avu][0-9]+$"

let index = Str.regexp "^\\[[avu][0-9]+\\]$"

let all = Str.regexp ".*"

let any = Str.regexp "\\*"

let any_to_all = Str.regexp "\\*.*$"

let start_bm = Str.regexp "^,[ \t\r\n]*"

let start_rest = Str.regexp "^,"

let start_rest_space = Str.regexp "^, "

let ref = Str.regexp "^[ \t\r\n]*->[ \t\r\n]*$"

let array = Str.regexp ".+\\[_\\*_\\].*"

let rm_array = Str.regexp "\\[_\\*_\\](\\*)"

let dollar = Str.regexp "\\$"

let dollar_to_all = Str.regexp "\\$.*"

let dot = Str.regexp "\\."

let space = Str.regexp " "

let space2 = Str.regexp "  "

let new_line = Str.regexp "\n"

let test_class = Str.regexp "UnitconTest[0-9]+\\.class"

let test_file = Str.regexp "UnitconTest[0-9]+\\.java"

let interface = Str.regexp "UnitconInterface"

let enum = Str.regexp "UnitconEnum"

let global_rm exp str = Str.global_replace exp "" str

let first_rm exp str = Str.replace_first exp "" str

let rm_space str =
  let str = first_rm pre_space str in
  first_rm post_space str

let remove_bk str = global_rm bk str |> rm_space

let rm_first_rest str = global_rm start_rest_space str

let package = Str.regexp "package"

let init = Str.regexp "\\.<init>(.*)"

let init_end = Str.regexp "\\.<.*>(.*)$"

let only_init = Str.regexp "\\.<init>"

let method_params = Str.regexp "(.*)"

let method_params_end = Str.regexp "(.*)$"

let modeling_array = Str.regexp "Array[0-9]*"

let modeling_array_end = Str.regexp "Array[0-9]*$"

let all_to_array = Str.regexp ".*Array"

let backslash = Str.regexp "\\"

let double_quote = Str.regexp "\""

let single_quote = Str.regexp "\'"

let java_file = Str.regexp "java\\.io\\.File\\.<init>"

let java_map_put = Str.regexp "java\\.util\\.Map\\.put"

let java_nio_package = Str.regexp "java\\.nio\\..*"

let lambda_num = Str.regexp "\\$Lambda\\$[_0-9]+"

let lambda = Str.regexp "\\.lambda\\$"

let lambda_var = Str.regexp "\\$bcvar"

let access_dollar = Str.regexp "access\\$"

let access_underbar = Str.regexp "access_"

let clone_method = Str.regexp "\\.clone()$"

let alias_sign = Str.regexp "\\[specialized with aliases\\]"

let test_start_class = Str.regexp "Test.*"

let test_end_class = Str.regexp ".*Test$"

let test_dir dir_sep = Str.regexp (dir_sep ^ "test" ^ dir_sep)

let anony_num = Str.regexp "\\$[0-9]+"

let start_object = Str.regexp "^Object"

let object_array = Str.regexp "Object.+Array[0-9]*$"

let method_to_param = Str.regexp "\\.[^\\.]+(.*)"

let class_to_all = Str.regexp "\\.[^\\.]+$"

let log_eq = Str.regexp "Log="

let javax = Str.regexp "javax"

let sun = Str.regexp "sun"

let com = Str.regexp "com"

let org = Str.regexp "org"

let jdk = Str.regexp "jdk"

let javac = Str.regexp "javac"

let java = Str.regexp "java"

let find = Str.regexp "find"

let init_err_msg = Str.regexp "Error occurred during initialization of VM"

let test_err_msg = Str.regexp "[0-9]+:* error"
