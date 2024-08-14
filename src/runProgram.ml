open Language
module F = Format
module Json = Yojson.Safe
module JsonUtil = Yojson.Safe.Util
module ImportSet = Utils.ImportSet

exception Compilation_Error

let con_path = "unitcon_properties"

let unitcon_path =
  let path = Filename.dirname Sys.argv.(0) in
  if Filename.is_relative path then Filename.concat (Unix.getcwd ()) path
  else path

let test_basename = "UnitconTest"

let multi_test_basename = "UnitconMultiTest"

let driver_basename = "UnitconDriver"

let time = ref 0.0

let num_of_tc_files = ref 0

let num_of_multi_tc_files = ref 0

let num_of_driver_files = ref 0

let num_of_last_exec_tc = ref 0

let num_of_success = ref 0

let first_success_tc = ref ""

let last_success_tc = ref ""

let require_enum_class = ref false

let require_interface_class = ref false

let error_method_name = ref ""

let bug_type = ref ""

type t = {
  program_dir : string;
  summary_file : string;
  error_summary_file : string;
  call_prop_file : string;
  inheritance_file : string;
  enum_file : string;
  constant_file : string;
  fuzz_constant_file : string;
  test_dir : string;
  multi_test_dir : string;
  driver_dir : string;
  expected_bug : string;
}

type run_type = Compile | Group | Fuzzer | Test

let info =
  ref
    {
      program_dir = "";
      summary_file = "";
      error_summary_file = "";
      call_prop_file = "";
      inheritance_file = "";
      enum_file = "";
      constant_file = "";
      fuzz_constant_file = "";
      test_dir = "";
      multi_test_dir = "";
      driver_dir = "";
      expected_bug = "";
    }

(* ************************************** *
   parse analyzer's output
 * ************************************** *)

let input name =
  let chan = open_in name in
  let data = Marshal.from_channel chan in
  close_in chan;
  data

let parse_method_info filename =
  if not (Sys.file_exists filename) then failwith (filename ^ " not found");
  let json = input filename in
  Summary.from_method_json json

let parse_summary filename minfo =
  let json = input filename in
  Summary.from_summary_json minfo json

let parse_callgraph filename =
  let data = input filename in
  Callgraph.of_json data

let get_setter summary m_info = Setter.from_summary_map summary m_info

let get_bug_type filename =
  if not (Sys.file_exists filename) then
    bug_type := "java.lang.NullPointerException"
  else
    let ic = open_in filename in
    bug_type :=
      really_input_string ic (in_channel_length ic)
      |> Str.global_replace Regexp.dollar "\\$"
      |> Regexp.rm_space;
    close_in ic

let parse_error_summary filename =
  if not (Sys.file_exists filename) then failwith (filename ^ " not found");
  let json = Json.from_file filename in
  ErrorSummary.from_error_summary_json json

let parse_callprop filename =
  if not (Sys.file_exists filename) then failwith (filename ^ " not found");
  let data = Json.lineseq_from_file filename in
  let json =
    `List
      (Seq.fold_left
         (fun lst assoc -> match assoc with `Json j -> j :: lst | _ -> lst)
         [] data)
  in
  CallProposition.from_callprop_json json

let parse_class_info filename =
  if not (Sys.file_exists filename) then failwith (filename ^ " not found");
  let json = Json.from_file filename in
  let elem = JsonUtil.to_list json |> List.hd in
  let info = Inheritance.of_json elem in
  (fst info, snd info |> Modeling.add_java_package_inheritance)

let parse_enum_info filename =
  if not (Sys.file_exists filename) then InstanceInfo.M.empty
  else Json.from_file filename |> Constant.of_enum_json

let parse_instance_info filename inst_info =
  if not (Sys.file_exists filename) then inst_info
  else Json.from_file filename |> Constant.of_ginstance_json inst_info

let parse_primitive_info filename =
  let default = Constant.default_primitive in
  if not (Sys.file_exists filename) then default
  else Json.from_file filename |> Constant.of_primitive_json default

(* ************************************** *
   run program
 * ************************************** *)

let lock_read_only dir = "chattr -R +i " ^ dir

let unlock_read_only dir = "chattr -R -i " ^ dir

let my_really_read_string in_chan =
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

let modify_execute_command command t_file_name = command ^ " " ^ t_file_name

let check_substring substr str =
  match Str.search_forward (Str.regexp substr) str 0 with
  | exception Not_found -> false
  | _ -> true

let compare_stack_trace target_trace error_trace =
  check_substring
    (!bug_type ^ ".*" ^ "[ \t\r\n]+[^a]*" ^ target_trace)
    error_trace

let check_package_name_presence package_name error_trace =
  check_substring package_name error_trace

let check_target_method_presence error_trace =
  check_substring
    ("java.lang.NullPointerException.*" ^ !error_method_name)
    error_trace

let check_useless_npe error_trace =
  let ignored_npes =
    [
      "java.io.File.<init>";
      "java.io.FileInputStream.<init>";
      "java.io.FileOutputStream.<init>";
      "java.util.Objects.requireNonNull";
    ]
  in
  List.exists (fun ignored -> check_substring ignored error_trace) ignored_npes

let run_type str =
  if Str.string_match (Str.regexp "^javac") str 0 then Compile
  else if Str.string_match (Str.regexp "^find") str 0 then Group
  else if Str.string_match (Str.regexp "^java") str 0 then Test
  else if
    let start_cmd = "^" ^ Filename.concat unitcon_path "deps/jazzer" in
    Str.string_match (Str.regexp start_cmd) str 0
  then Fuzzer
  else if Str.string_match (Str.regexp "^chattr") str 0 then Fuzzer
  else failwith "not supported build type"

let string_of_expected_bug file =
  if not (Sys.file_exists file) then failwith (file ^ " not found");
  let ic = open_in file in
  let s = really_input_string ic (in_channel_length ic) in
  close_in ic;
  Str.global_replace Regexp.dollar "\\$" s
  |> Str.global_replace (Str.regexp "\n") "[ \t\r\n]+"

let get_index_of_substring substr str start =
  match Str.search_forward (Str.regexp substr) str start with
  | exception Not_found -> None
  | i -> Some i

let get_rep_input error_trace expected_bug =
  let expect = string_of_expected_bug expected_bug in
  let target = !bug_type ^ ".*" ^ "[ \t\r\n]+[^a]*" ^ expect in
  (* Exception ... Unitcon=index= ... -----UnitConLogEnd----- *)
  let s_idx = get_index_of_substring target error_trace 0 in
  let e_idx =
    match s_idx with
    | None -> None
    | Some i -> get_index_of_substring "-----UnitConLogEnd-----" error_trace i
  in
  let trace_and_input =
    match (s_idx, e_idx) with
    | None, _ | _, None -> ""
    | Some s, Some e -> String.sub error_trace s (e - s)
  in
  let rec get_input lst =
    match lst with
    | hd :: tl ->
        if check_substring "UnitCon=" hd then
          let name_idx =
            Str.replace_first (Str.regexp "UnitCon=") "" hd
            |> Str.split (Str.regexp "=")
          in
          (name_idx |> List.hd, name_idx |> List.tl |> List.hd |> int_of_string)
          :: get_input tl
        else get_input tl
    | _ -> []
  in
  Str.split (Str.regexp "\n") trace_and_input |> get_input

let get_rep_file error_trace expected_bug =
  let expect = string_of_expected_bug expected_bug in
  let target = !bug_type ^ ".*" ^ "[ \t\r\n]+[^a]*" ^ expect in
  (* == Java Exception: ... reproducer_path= ... Java reproducer written to ... *)
  let trace = get_index_of_substring target error_trace 0 in
  let s_idx =
    match trace with
    | None -> None
    | Some i ->
        get_index_of_substring "Java reproducer written to" error_trace i
  in
  let fs_idx =
    match s_idx with
    | None -> None
    | Some i -> get_index_of_substring "Crash_" error_trace i
  in
  let fe_idx =
    match s_idx with
    | None -> None
    | Some i -> get_index_of_substring "\\.java" error_trace i
  in
  let f_name =
    match (fs_idx, fe_idx) with
    | None, _ | _, None -> ""
    | Some s, Some e -> String.sub error_trace s (e + 5 - s)
  in
  f_name

let execute_command command =
  let close_channel (stdout, stdin, stderr) =
    close_out stdin;
    (stdout, stderr)
  in
  let execute command =
    let stdout, stdin, stderr =
      Unix.open_process_full command (Unix.environment ())
    in
    let pid = Unix.process_full_pid (stdout, stdin, stderr) in
    (try Unix.waitpid [ Unix.WUNTRACED ] pid |> ignore with _ -> ());
    close_channel (stdout, stdin, stderr)
  in
  match run_type command with
  | Compile | Group | Fuzzer -> execute command
  | Test -> execute ("timeout 5s " ^ command)

let simple_compiler program_dir command =
  let current_dir = Unix.getcwd () in
  Sys.chdir program_dir;
  let ic_out, ic_err = execute_command command in
  Sys.chdir current_dir;
  (ic_out, ic_err)

let get_package p = if p = "" then p else "package " ^ p ^ ";\n"

let get_imports i_set =
  let is_default_path i = String.contains i '.' |> not in
  let str_set =
    ImportSet.fold
      (fun i s ->
        let path = Utils.rm_object_array_import i in
        if i = "" || (Utils.is_array i && path = i) || is_default_path i then s
        else
          ImportSet.add ("import " ^ Utils.replace_nested_symbol path ^ ";\n") s)
      i_set ImportSet.empty
  in
  let init =
    if !Cmdline.mock then "import static org.mockito.Mockito.mock;\n" else ""
  in
  ImportSet.fold (fun i s -> s ^ i) str_set init

let need_default_interface tc_body =
  match Str.search_forward (Str.regexp "UnitconInterface") tc_body 0 with
  | exception _ -> ()
  | _ -> require_interface_class := true

let need_default_enum tc_body =
  match Str.search_forward (Str.regexp "UnitconEnum") tc_body 0 with
  | exception _ -> ()
  | _ -> require_enum_class := true

let need_default_class tc_body =
  need_default_interface tc_body;
  need_default_enum tc_body

let insert_test oc (file_num, tc, time) =
  let insert oc (i_set, m_bodies) =
    let time = "/* Duration of synthesis: " ^ string_of_float time ^ "*/\n" in
    let start = "@Test\npublic void test() {\n" in
    need_default_class m_bodies;
    get_package !Cmdline.extension |> output_string oc;
    (* if package is needed, add package keyword. Cmdline.extension does not contain the class name *)
    get_imports i_set ^ "import org.junit.Test;\n\n" |> output_string oc;
    output_string oc time;
    "public class UnitconTest" ^ string_of_int file_num ^ " {\n"
    |> output_string oc;
    start ^ "try {\n" ^ m_bodies
    ^ "}\ncatch(Exception e) {\ne.printStackTrace();\n}\n" ^ "}\n}\n"
    |> output_string oc;
    flush oc;
    close_out oc
  in
  insert oc tc

let insert_loop loop_id =
  let id = AST.loop_id_lvar_code loop_id |> snd in
  let index = id ^ "_index" in
  let init = index ^ " = 0; " in
  let cond = index ^ " < " ^ id ^ ".length; " in
  let incr = index ^ "++" in
  "for(int " ^ init ^ cond ^ incr ^ ") {\n"

let insert_loops loop_id_map =
  AST.LoopIdMap.M.fold
    (fun id _ (code, count) -> (code ^ insert_loop id, count + 1))
    loop_id_map ("", 0)

let rec close_bracket count =
  if count <= 0 then "" else "}\n" ^ close_bracket (count - 1)

let insert_multi_test_log loop_id_map =
  let end_signal = "System.err.println(\"-----UnitConLogEnd-----\");\n" in
  let log id =
    "System.err.println(\"UnitCon=\" + \"" ^ id ^ "\" + \"=\" + " ^ id
    ^ "_index" ^ ");\n"
  in
  AST.LoopIdMap.M.fold
    (fun id _ code -> log (AST.loop_id_lvar_code id |> snd) ^ code)
    loop_id_map end_signal

let insert_multi_test oc (file_num, tc, loop_id_map, time) =
  let insert oc (i_set, m_bodies) =
    let time = "/* Duration of synthesis: " ^ string_of_float time ^ "*/\n" in
    let start = "@Test\npublic void test() {\n" in
    let array_for_loop =
      AST.LoopIdMap.M.fold
        (fun id exps code -> code ^ AST.loop_id_code id exps)
        loop_id_map ""
    in
    let loop_stmt, loop_cnt = insert_loops loop_id_map in
    let loop_input_log = insert_multi_test_log loop_id_map in
    need_default_class m_bodies;
    get_package !Cmdline.extension |> output_string oc;
    (* if package is needed, add package keyword. Cmdline.extension does not contain the class name *)
    get_imports i_set ^ "import org.junit.Test;\n\n" |> output_string oc;
    output_string oc time;
    "public class UnitconMultiTest" ^ string_of_int file_num ^ " {\n"
    |> output_string oc;
    start ^ array_for_loop ^ loop_stmt ^ "try {\n" ^ m_bodies
    ^ "}\ncatch(Exception e) {\ne.printStackTrace();\n" ^ loop_input_log ^ "}\n"
    ^ close_bracket loop_cnt ^ "}\n}\n"
    |> output_string oc;
    flush oc;
    close_out oc
  in
  insert oc tc

let insert_driver oc (file_num, tc, time) =
  let insert oc (i_set, m_bodies) =
    let time = "/* Duration of synthesis: " ^ string_of_float time ^ "*/\n" in
    let start =
      "public static void fuzzerTestOneInput(FuzzedDataProvider data) throws \
       Exception, Throwable {\n"
    in
    need_default_class m_bodies;
    get_package !Cmdline.extension |> output_string oc;
    (* if package is needed, add package keyword. Cmdline.extension does not contain the class name *)
    get_imports i_set
    ^ "import com.code_intelligence.jazzer.api.FuzzedDataProvider;\n\n"
    |> output_string oc;
    output_string oc time;
    "public class UnitconDriver" ^ string_of_int file_num ^ " {\n"
    |> output_string oc;
    start ^ m_bodies ^ "}\n}\n" |> output_string oc;
    flush oc;
    close_out oc
  in
  insert oc tc

let insert_log_driver oc (file_num, tc, time) =
  let get_id stmt =
    if check_substring "data\\.consume" stmt then
      Str.split (Str.regexp " ") stmt |> List.tl |> List.hd |> Regexp.rm_space
    else ""
  in
  let log id = "System.err.println(\"UnitCon=\" + " ^ id ^ ");\n" in
  let rec add_log lst =
    match lst with
    | hd :: tl ->
        let id = get_id hd in
        if id <> "" then hd ^ "\n" ^ log id ^ add_log tl
        else hd ^ "\n" ^ add_log tl
    | _ -> ""
  in
  let insert oc (i_set, m_bodies) =
    let time = "/* Duration of synthesis: " ^ string_of_float time ^ "*/\n" in
    let start =
      "public static void fuzzerTestOneInput(FuzzedDataProvider data) throws \
       Exception, Throwable {\n"
    in
    get_package !Cmdline.extension |> output_string oc;
    (* if package is needed, add package keyword. Cmdline.extension does not contain the class name *)
    get_imports i_set
    ^ "import com.code_intelligence.jazzer.api.FuzzedDataProvider;\n\n"
    |> output_string oc;
    output_string oc time;
    "public class UnitconDriver" ^ string_of_int file_num ^ " {\n"
    |> output_string oc;
    let modified_m_bodies = Str.split (Str.regexp "\n") m_bodies |> add_log in
    start ^ modified_m_bodies ^ "}\n}\n" |> output_string oc;
    flush oc;
    close_out oc
  in
  insert oc tc

let add_default_class test_dir =
  let need_default_interface () =
    if !require_interface_class then (
      let oc = open_out (Filename.concat test_dir "UnitconInterface.java") in
      get_package !Cmdline.extension |> output_string oc;
      output_string oc "interface UnitconInterface {}\n";
      close_out oc)
  in
  let need_default_enum () =
    if !require_enum_class then (
      let oc = open_out (Filename.concat test_dir "UnitconEnum.java") in
      get_package !Cmdline.extension |> output_string oc;
      output_string oc "enum UnitconEnum {}\n";
      close_out oc)
  in
  need_default_interface ();
  need_default_enum ()

let add_testcase test_dir file_num (tc, time) =
  let oc =
    open_out
      (Filename.concat test_dir
         (test_basename ^ string_of_int file_num ^ ".java"))
  in
  insert_test oc (file_num, tc, time)

let add_multi_testcase test_dir file_num (tc, loop_ids, time) =
  let oc =
    open_out
      (Filename.concat test_dir
         (multi_test_basename ^ string_of_int file_num ^ ".java"))
  in
  insert_multi_test oc (file_num, tc, loop_ids, time)

let add_driver driver_dir file_num (tc, time) =
  let oc =
    open_out
      (Filename.concat driver_dir
         (driver_basename ^ string_of_int file_num ^ ".java"))
  in
  insert_driver oc (file_num, tc, time)

let add_log_driver driver_dir file_num (tc, time) =
  let oc =
    open_out
      (Filename.concat driver_dir
         (driver_basename ^ string_of_int file_num ^ ".java"))
  in
  insert_log_driver oc (file_num, tc, time)

let remove_file fname =
  if Sys.file_exists fname then
    try Unix.unlink fname with _ -> Logger.info "Fail delete %s" fname

let remove_files dir (pattern : Str.regexp) =
  let remove_file file =
    if Str.string_match pattern file 0 then
      Unix.unlink (Filename.concat dir file)
  in
  let files = Array.to_list (Sys.readdir dir) in
  List.iter (fun file -> remove_file file) files

let remove_all_test_classes test_dir = remove_files test_dir Regexp.test_class

let remove_all_test_files test_dir = remove_files test_dir Regexp.test_file

let remove_all_files dir = remove_files dir (Str.regexp ".*")

let make_folder path =
  try Unix.mkdir path 0o775
  with Unix.Unix_error (EEXIST, _, _) ->
    remove_all_test_classes path;
    remove_all_test_files path;
    remove_file (Filename.concat path "UnitconInterface.java");
    remove_file (Filename.concat path "UnitconEnum.java");
    remove_file (Filename.concat path "UnitconInterface.class");
    remove_file (Filename.concat path "UnitconEnum.class")

let init_folder dir =
  let folders = Str.split (Str.regexp Filename.dir_sep) dir in
  let rec make_folders path = function
    | [] -> ()
    | f :: dep ->
        let p = path ^ Filename.dir_sep ^ f in
        make_folder p;
        make_folders p dep
  in
  make_folders "" folders

let get_compilation_error_files data =
  let get_f_name line =
    String.split_on_char ':' line |> List.hd |> Filename.basename
  in
  let data = String.split_on_char '\n' data in
  List.fold_left
    (fun f_list line ->
      if Str.string_match (Str.regexp ".*UnitconTest[0-9]+\\.java") line 0 then
        let file_name = get_f_name line in
        file_name :: f_list
      else f_list)
    [] data

let remove_last_file test_dir =
  decr num_of_tc_files;
  let last_file = "UnitconTest" ^ string_of_int !num_of_tc_files ^ ".java" in
  remove_file (Filename.concat test_dir last_file)

let rec remove_no_exec_files curr_num test_dir =
  if !num_of_tc_files = !num_of_last_exec_tc || curr_num > !num_of_tc_files then
    ()
  else
    let curr_tc = "UnitconTest" ^ string_of_int curr_num ^ ".java" in
    let curr_class = "UnitconTest" ^ string_of_int curr_num ^ ".class" in
    remove_file (Filename.concat test_dir curr_tc);
    remove_file (Filename.concat test_dir curr_class);
    remove_no_exec_files (curr_num + 1) test_dir

let modify_files test_dir data =
  let error_files = get_compilation_error_files data in
  List.iter
    (fun file -> remove_file (Filename.concat test_dir file))
    error_files

let checking_init_err data =
  match
    Str.search_forward
      (Str.regexp "Error occurred during initialization of VM")
      data 0
  with
  | exception Not_found -> false
  | _ -> true

let checking_error_presence data =
  match Str.search_forward (Str.regexp "[0-9]+ error") data 0 with
  | exception Not_found -> ()
  | _ -> raise Compilation_Error

let checking_bug_presence error_trace expected_bug =
  if !Cmdline.unknown_bug then
    check_package_name_presence
      (string_of_expected_bug expected_bug)
      error_trace
    && check_target_method_presence error_trace
    && check_useless_npe error_trace |> not
  else compare_stack_trace (string_of_expected_bug expected_bug) error_trace

let get_const_sequence tc =
  let consume_func t =
    get_consume_func t |> Str.replace_first Regexp.dot "\\."
  in
  let identify_const_type s =
    if check_substring (consume_func Int) s then Int
    else if check_substring (consume_func Long) s then Long
    else if check_substring (consume_func Short) s then Short
    else if check_substring (consume_func Byte) s then Byte
    else if check_substring (consume_func Float) s then Float
    else if check_substring (consume_func Double) s then Double
    else if check_substring (consume_func Bool) s then Bool
    else if check_substring (consume_func Char) s then Char
    else if check_substring (consume_func String) s then String
    else NonType
  in
  let rec collect lst =
    match lst with
    | hd :: tl when check_substring "data\\.consume" hd ->
        identify_const_type hd :: collect tl
    | _ :: tl -> collect tl
    | _ -> []
  in
  Str.split (Str.regexp "\n") tc |> collect

let driver_to_tc typs inputs tc =
  let default_value typ =
    (* for avoiding compilation error *)
    match typ with
    | Int | Short | Byte -> "0"
    | Long -> "0l"
    | Double -> "0."
    | Float -> "0.f"
    | Char -> "\'\\0\'"
    | String -> "\"\""
    | Bool -> "false"
    | _ -> ""
  in
  let modify_format typ input =
    match typ with
    | Int | Short | Byte | Double | Bool -> input
    | Long -> input ^ "l"
    | Float -> input ^ "f"
    | Char -> "\'" ^ input ^ "\'"
    | String -> "\"" ^ input ^ "\""
    | _ -> input
  in
  let consume_func t =
    get_consume_func t |> Str.replace_first Regexp.dot "\\."
  in
  let rec func_to_value t_lst i_lst tc =
    match (t_lst, i_lst) with
    | typ :: t_tl, input :: i_tl ->
        let f = consume_func typ in
        let new_input = modify_format typ input in
        Str.replace_first (Str.regexp f) new_input tc |> func_to_value t_tl i_tl
    | typ :: t_tl, [] ->
        let f = consume_func typ in
        Str.replace_first (Str.regexp f) (default_value typ) tc
        |> func_to_value t_tl []
    | _ -> tc
  in
  func_to_value typs inputs tc

let loop_index_to_tc rep_input loop_id_map tc =
  let rec find_input count exps =
    match exps with
    | hd :: _ when count = 0 -> hd
    | _ :: tl -> find_input (count - 1) tl
    | _ -> AST.Exp
  in
  let find_id str_id =
    AST.LoopIdMap.M.fold
      (fun id _ found ->
        if str_id = (AST.loop_id_lvar_code id |> snd) then id else found)
      loop_id_map AST.Id
  in
  List.fold_left
    (fun old_tc (id, idx) ->
      let to_be_modified = id ^ "\\[" ^ id ^ "_index\\]" in
      let ast_id = find_id id in
      let real_input =
        find_input idx (AST.LoopIdMap.M.find ast_id loop_id_map)
      in
      let input_code = AST.exp_code real_input ast_id in
      Str.replace_first (Str.regexp to_be_modified) input_code old_tc)
    tc rep_input

let init program_dir =
  let cons = Filename.concat in
  let program_dir =
    if Filename.is_relative program_dir then cons (Unix.getcwd ()) program_dir
    else program_dir
  in
  let t_dir =
    if !Cmdline.extension = "" then "unitcon_tests"
    else Utils.dot_to_dir_sep !Cmdline.extension
  in
  let d_dir =
    if !Cmdline.extension = "" then "unitcon_drivers"
    else Utils.dot_to_dir_sep !Cmdline.extension
  in
  let mt_dir =
    if !Cmdline.extension = "" then "unitcon_multi_tests"
    else Utils.dot_to_dir_sep !Cmdline.extension
  in
  info :=
    {
      program_dir;
      summary_file = cons con_path "summary.json" |> cons program_dir;
      error_summary_file =
        cons con_path "error_summaries.json" |> cons program_dir;
      call_prop_file = cons con_path "call_proposition.json" |> cons program_dir;
      inheritance_file =
        cons con_path "inheritance_info.json" |> cons program_dir;
      enum_file = cons con_path "enum_info.json" |> cons program_dir;
      constant_file = cons con_path "extra_constant.json" |> cons program_dir;
      fuzz_constant_file = cons con_path "fuzz_constant" |> cons program_dir;
      test_dir = cons program_dir t_dir;
      multi_test_dir = cons program_dir mt_dir;
      driver_dir = cons program_dir d_dir;
      expected_bug = cons con_path "expected_bug" |> cons program_dir;
    };
  init_folder !info.test_dir;
  init_folder !info.multi_test_dir;
  init_folder !info.driver_dir;
  cons !info.test_dir "log.txt" |> Logger.from_file;
  get_bug_type (cons con_path "expected_bug_type" |> cons !info.program_dir);
  Logger.info "Start UnitCon for %s" program_dir

(* return: (testcase * list(partial testcase)) *)
let make_testcase ~is_start queue e_method_info program_info =
  Generator.mk_testcases ~is_start queue e_method_info program_info

let compile_cmd =
  "find ./unitcon_tests/ -name \"*.java\" > test_files; "
  ^ "javac -cp with_dependency.jar:"
  ^ Filename.concat unitcon_path "deps/junit-4.11.jar"
  ^ " @test_files"

let multi_test_compile_cmd =
  "find ./unitcon_multi_tests/ -name \"*.java\" > multi_test_files; "
  ^ "javac -cp with_dependency.jar:"
  ^ Filename.concat unitcon_path "deps/junit-4.11.jar"
  ^ " @multi_test_files"

let driver_compile_cmd =
  "find ./unitcon_drivers/ -name \"*.java\" > driver_files; "
  ^ "javac -cp with_dependency.jar:"
  ^ Filename.concat unitcon_path "deps/jazzer_standalone.jar"
  ^ " @driver_files"

let build_program info =
  let rec compile_loop () =
    let ic_out, ic_err = simple_compiler info.program_dir compile_cmd in
    let data_out = my_really_read_string ic_out in
    let data_err = my_really_read_string ic_err in
    close_in ic_out;
    close_in ic_err;
    if checking_init_err data_out then (
      remove_last_file info.test_dir;
      compile_loop ())
    else
      match checking_error_presence data_err with
      | exception Compilation_Error ->
          modify_files info.test_dir data_err;
          compile_loop ()
      | _ -> ()
  in
  compile_loop ()

let build_multi_test info =
  let ic_out, ic_err =
    simple_compiler info.program_dir multi_test_compile_cmd
  in
  close_in ic_out;
  close_in ic_err

let build_driver info =
  let ic_out, ic_err = simple_compiler info.program_dir driver_compile_cmd in
  close_in ic_out;
  close_in ic_err

let normal_exit =
  Sys.Signal_handle
    (fun _ ->
      (* unlock files and folders because they should not be locked when the process terminates *)
      let ic_out, ic_err =
        unlock_read_only !info.program_dir |> simple_compiler !info.program_dir
      in
      close_in ic_out;
      close_in ic_err;
      Logger.info "Normal End UnitCon for %s: %b(%d) (total time: %f)"
        !info.program_dir
        (if !num_of_success > 0 then true else false)
        !num_of_success
        (Unix.gettimeofday () -. !time);
      Logger.info "First Success Test: %s" !first_success_tc;
      Logger.info "Last Success Test: %s" !last_success_tc;
      (* clean up useless files and directories *)
      remove_no_exec_files !num_of_last_exec_tc !info.test_dir;
      remove_file (Filename.concat !info.program_dir "multi_test_files");
      remove_file (Filename.concat !info.program_dir "driver_files");
      remove_all_files !info.multi_test_dir;
      remove_all_files !info.driver_dir;
      Unix.rmdir !info.multi_test_dir;
      Unix.rmdir !info.driver_dir;
      Unix._exit 0)

let get_test_path path base_name =
  if path = "" then base_name
  else Utils.dot_to_dir_sep path ^ Filename.dir_sep ^ base_name

let execute_cmd =
  "java -cp with_dependency.jar:./unitcon_tests/:"
  ^ Filename.concat unitcon_path "deps/junit-4.11.jar:. "
  ^ "org.junit.runner.JUnitCore"

let multi_test_execute_cmd =
  "java -cp with_dependency.jar:./unitcon_multi_tests/:"
  ^ Filename.concat unitcon_path "deps/junit-4.11.jar:. "
  ^ "org.junit.runner.JUnitCore"

let is_empty_file file =
  if not (Sys.file_exists file) then failwith (file ^ " not found");
  let ic = open_in file in
  let s = really_input_string ic (in_channel_length ic) in
  close_in ic;
  if Regexp.rm_space s = "" then true else false

let driver_execute_cmd d_file =
  let execute_cmd =
    let common =
      Filename.concat unitcon_path "deps/jazzer "
      ^ "--cp=with_dependency.jar:./unitcon_drivers/:. " ^ "--target_class="
      ^ d_file
      ^ " --keep_going=30 --hooks=false --dedup=true \
         --reproducer_path=./unitcon_drivers/"
      ^ " -artifact_prefix=./unitcon_drivers/ -timeout=10 -max_total_time=10 \
         -seed=1"
    in
    if is_empty_file !info.fuzz_constant_file then common ^ "; "
    else common ^ " -dict=" ^ !info.fuzz_constant_file ^ "; "
  in
  lock_read_only !info.program_dir
  ^ "; "
  ^ unlock_read_only !info.driver_dir
  ^ "; " ^ execute_cmd
  ^ unlock_read_only !info.program_dir

let log_driver_execute_cmd crash_file =
  "java -cp with_dependency.jar:"
  ^ Filename.concat unitcon_path
      "deps/jazzer_standalone.jar:./unitcon_drivers:. "
  ^ crash_file

let run_testfile () =
  let compile_start = Unix.gettimeofday () in
  add_default_class !info.test_dir;
  Logger.info "Start compilation! (# of test files: %d)" !num_of_tc_files;
  build_program !info;
  Logger.info "End compilation! (duration: %f)"
    (Unix.gettimeofday () -. compile_start);
  let execute program_dir test_dir expected_bug t_file num_of_t_file =
    let ic_out, ic_err =
      simple_compiler program_dir (modify_execute_command execute_cmd t_file)
    in
    let data = my_really_read_string ic_err in
    close_in ic_out;
    close_in ic_err;
    num_of_last_exec_tc := num_of_t_file;
    if checking_bug_presence data expected_bug then (
      if !first_success_tc = "" then first_success_tc := t_file;
      last_success_tc := t_file;
      incr num_of_success;
      Logger.info "Success Test: %s" t_file)
    else if not (Sys.file_exists (Filename.concat test_dir (t_file ^ ".java")))
    then ()
    else (
      remove_file (Filename.concat test_dir (t_file ^ ".java"));
      remove_file (Filename.concat test_dir (t_file ^ ".class")))
  in
  let rec execute_test current_f_num program_dir test_dir expected_bug =
    if current_f_num <= !num_of_tc_files then (
      execute program_dir test_dir expected_bug
        (get_test_path !Cmdline.extension test_basename
        ^ string_of_int current_f_num)
        current_f_num;
      execute_test (current_f_num + 1) program_dir test_dir expected_bug)
  in
  execute_test (!num_of_last_exec_tc + 1) !info.program_dir !info.test_dir
    !info.expected_bug

let run_multi_testfile () =
  let compile_start = Unix.gettimeofday () in
  add_default_class !info.driver_dir;
  Logger.info "Start multi-test! (# of multi-test: %d)" !num_of_multi_tc_files;
  build_multi_test !info;
  let mt_file =
    get_test_path !Cmdline.extension multi_test_basename
    ^ string_of_int !num_of_multi_tc_files
  in
  let ic_out, ic_err =
    simple_compiler !info.program_dir
      (modify_execute_command multi_test_execute_cmd mt_file)
  in
  let data = my_really_read_string ic_err in
  close_in ic_out;
  close_in ic_err;
  let found_rep_inputs =
    if checking_bug_presence data !info.expected_bug then (
      Logger.info "Found bug with loop: %s" mt_file;
      get_rep_input data !info.expected_bug)
    else []
  in
  Logger.info "End multi-test! (duration: %f)"
    (Unix.gettimeofday () -. compile_start);
  found_rep_inputs

let run_reproducer crash_file =
  let rec get_input lst =
    match lst with
    | hd :: tl ->
        if check_substring "UnitCon=" hd then
          Str.replace_first (Str.regexp "UnitCon=") "" hd :: get_input tl
        else get_input tl
    | _ -> []
  in
  let compile_start = Unix.gettimeofday () in
  Logger.info "Start reproducer! (# of driver: %d)" !num_of_driver_files;
  build_driver !info;
  let crash_file = get_test_path !Cmdline.extension crash_file in
  let ic_out, ic_err =
    simple_compiler !info.program_dir (log_driver_execute_cmd crash_file)
  in
  let data = my_really_read_string ic_err in
  close_in ic_out;
  close_in ic_err;
  let input = Str.split (Str.regexp "\n") data |> get_input in
  Logger.info "End reproducer! (duration: %f)"
    (Unix.gettimeofday () -. compile_start);
  input

let run_fuzzer () =
  let compile_start = Unix.gettimeofday () in
  add_default_class !info.driver_dir;
  Logger.info "Start fuzzer! (# of driver: %d)" !num_of_driver_files;
  build_driver !info;
  let d_file =
    get_test_path !Cmdline.extension driver_basename
    ^ string_of_int !num_of_driver_files
  in
  let ic_out, ic_err =
    simple_compiler !info.program_dir (driver_execute_cmd d_file)
  in
  let data = my_really_read_string ic_err in
  close_in ic_out;
  close_in ic_err;
  let found_rep_file =
    if checking_bug_presence data !info.expected_bug then (
      Logger.info "Found bug with fuzzer: %s" d_file;
      get_rep_file data !info.expected_bug)
    else ""
  in
  Logger.info "End fuzzer! (duration: %f)"
    (Unix.gettimeofday () -. compile_start);
  found_rep_file

(* queue: (testcase * list(partial testcase)) *)
let rec run_test ~is_start info queue e_method_info p_info =
  let completion, tc, loop_id_map, tc_list =
    make_testcase ~is_start queue e_method_info p_info
  in
  if completion = Need_Loop then (
    (* clean before executing multi tests *)
    remove_all_files info.multi_test_dir;
    let _time = Unix.gettimeofday () -. !time in
    incr num_of_multi_tc_files;
    add_multi_testcase info.multi_test_dir !num_of_multi_tc_files
      (tc, loop_id_map, _time);
    let found_rep_input = run_multi_testfile () in
    if found_rep_input = [] then
      run_test ~is_start:false info tc_list e_method_info p_info
    else
      (* found crash input with loop *)
      let new_tc = loop_index_to_tc found_rep_input loop_id_map (tc |> snd) in
      let _time = Unix.gettimeofday () -. !time in
      incr num_of_tc_files;
      add_testcase info.test_dir !num_of_tc_files ((tc |> fst, new_tc), _time);
      if !num_of_tc_files mod 15 = 0 then run_testfile () else ();
      run_test ~is_start:false info tc_list e_method_info p_info)
  else if completion = Need_Fuzzer then (
    (* clean before running fuzzer *)
    remove_all_files info.driver_dir;
    let _time = Unix.gettimeofday () -. !time in
    incr num_of_driver_files;
    add_driver info.driver_dir !num_of_driver_files (tc, _time);
    let fuzz_seq = get_const_sequence (tc |> snd) in
    let found_rep_file = run_fuzzer () |> Filename.remove_extension in
    if found_rep_file = "" then
      run_test ~is_start:false info tc_list e_method_info p_info
    else
      (* found crash input with fuzzer *)
      let _time = Unix.gettimeofday () -. !time in
      add_log_driver info.driver_dir !num_of_driver_files (tc, _time);
      let input = run_reproducer found_rep_file in
      incr num_of_tc_files;
      let new_tc = driver_to_tc fuzz_seq input (tc |> snd) in
      let _time = Unix.gettimeofday () -. !time in
      add_testcase info.test_dir !num_of_tc_files ((tc |> fst, new_tc), _time);
      if !num_of_tc_files mod 15 = 0 then run_testfile () else ();
      run_test ~is_start:false info tc_list e_method_info p_info)
  else if completion = Incomplete then (
    (* early stopping *)
    if !num_of_last_exec_tc < !num_of_tc_files then run_testfile () else ();
    Unix.kill (Unix.getpid ()) Sys.sigusr1)
  else
    let _time = Unix.gettimeofday () -. !time in
    incr num_of_tc_files;
    add_testcase info.test_dir !num_of_tc_files (tc, _time);
    if !num_of_tc_files mod 15 = 0 then run_testfile () else ();
    run_test ~is_start:false info tc_list e_method_info p_info

(* force stop if generated test cases are not executed and only synthesis is long *)
let abnormal_run_test =
  Sys.Signal_handle
    (fun _ ->
      (* unlock files and folders because they should not be locked when the test cases execute *)
      let ic_out, ic_err =
        unlock_read_only !info.program_dir |> simple_compiler !info.program_dir
      in
      close_in ic_out;
      close_in ic_err;
      if !num_of_tc_files mod 15 <> 0 then (
        Logger.info "Abnormal Run Test";
        run_testfile ();
        Unix.kill (Unix.getpid ()) Sys.sigusr1)
      else Logger.info "Keep Going")

let interrupt pid =
  Unix.sleep (!Cmdline.time_out - 10);
  Unix.kill pid Sys.sigusr2

let run program_dir =
  (* for early stopping *)
  Sys.set_signal Sys.sigusr1 normal_exit;
  Sys.set_signal Sys.sigusr2 abnormal_run_test;
  Thread.create interrupt (Unix.getpid ()) |> ignore;
  time := Unix.gettimeofday ();
  init program_dir;
  let method_info = parse_method_info !info.summary_file in
  let type_info = Summary.from_method_type method_info in
  let summary = parse_summary !info.summary_file method_info in
  let callgraph = parse_callgraph !info.summary_file in
  let setter_map = get_setter summary method_info in
  let class_info = parse_class_info !info.inheritance_file in
  let instance_info =
    parse_enum_info !info.enum_file |> parse_instance_info !info.constant_file
  in
  let primitive_info = parse_primitive_info !info.constant_file in
  let call_prop_map = parse_callprop !info.call_prop_file in
  let error_method_info = parse_error_summary !info.error_summary_file in
  (* for unknown bug detection *)
  error_method_name :=
    Regexp.first_rm (Str.regexp "(.*)") (fst error_method_info)
    |> Str.split Regexp.dot |> List.rev |> List.hd;
  run_test ~is_start:true !info [] error_method_info
    ( callgraph,
      summary,
      call_prop_map,
      method_info,
      type_info,
      class_info,
      setter_map,
      instance_info,
      primitive_info )
