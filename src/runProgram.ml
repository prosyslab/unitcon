open Language
open Utils
module Json = Yojson.Safe
module JsonUtil = Yojson.Safe.Util
module ImportSet = Utils.ImportSet

exception Compilation_Error

let test_basename = "UnitconTest"

let multi_test_basename = "UnitconMultiTest"

let time = ref 0.0

let num_of_tc_files = ref 0

let num_of_multi_tc_files = ref 0

let num_of_last_exec_tc = ref 0

let num_of_success = ref 0

let first_success_tc = ref ""

let last_success_tc = ref ""

let abnormal_keep_going = ref false

let require_enum_class = ref false

let require_interface_class = ref false

let error_method_name = ref ""

let bug_type = ref ""

type t = {
  program_dir : string;
  summary_file : string;
  error_summary_file : string;
  call_prop_file : string;
  class_info_file : string;
  constant_file : string;
  test_dir : string;
  multi_test_dir : string;
  expected_bug : string;
}

type run_type = Compile | Group | Test

let info =
  ref
    {
      program_dir = "";
      summary_file = "";
      error_summary_file = "";
      call_prop_file = "";
      class_info_file = "";
      constant_file = "";
      test_dir = "";
      multi_test_dir = "";
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

let parse_extra_callgraph filename cg =
  if not (Sys.file_exists filename) then failwith (filename ^ " not found");
  let json = Json.from_file filename in
  Callgraph.of_extra_json cg json

let get_setter summary m_info = Setter.from_summary_map summary m_info

let get_bug_type filename =
  if not (Sys.file_exists filename) then bug_type := ""
  else
    let ic = open_in filename in
    bug_type :=
      really_input_string ic (in_channel_length ic)
      |> Str.global_replace Regexp.dollar "\\$"
      |> Regexp.rm_space;
    close_in ic

let parse_error_summary filename =
  if not (Sys.file_exists filename) then failwith (filename ^ " not found");
  let data = Json.lineseq_from_file filename in
  let json =
    `List
      (Seq.fold_left
         (fun lst assoc -> match assoc with `Json j -> j :: lst | _ -> lst)
         [] data
      |> List.rev)
  in
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

let parse_class_info filename summary_map method_map =
  if not (Sys.file_exists filename) then failwith (filename ^ " not found");
  let json = Json.from_file filename in
  Inheritance.of_json summary_map method_map json

let parse_stdlib_info (ct_info, i_info) smap mmap =
  let stdlib_file = Filename.(Utils.unitcon_path / "deps/class-info.json") in
  if not (Sys.file_exists stdlib_file) then ((ct_info, i_info), smap, mmap)
  else
    let json = Json.from_file stdlib_file in
    Inheritance.of_stdlib_json ct_info i_info smap mmap json

let parse_gconstant_info filename =
  if not (Sys.file_exists filename) then InstanceInfo.M.empty
  else Json.from_file filename |> Constant.of_gconst_json

let parse_primitive_info filename =
  let default = Constant.default_primitive in
  if not (Sys.file_exists filename) then default
  else Json.from_file filename |> Constant.of_primitive_json default

(* ************************************** *
   init program
 * ************************************** *)

let remove_file fname =
  if Sys.file_exists fname then
    try Unix.unlink fname with _ -> L.info "Fail delete %s" fname

let remove_files dir (pattern : Str.regexp) =
  let remove_file file =
    if Str.string_match pattern file 0 then Unix.unlink Filename.(dir / file)
  in
  let files = Array.to_list (Sys.readdir dir) in
  List.iter (fun file -> remove_file file) files

let remove_all_test_classes test_dir = remove_files test_dir Regexp.test_class

let remove_all_test_files test_dir = remove_files test_dir Regexp.test_file

let remove_all_files dir = remove_files dir (Str.regexp ".*")

let make_folder path = Filename.mkdir ~exists_ok:true path 0o755

let init_folder dir =
  let folders = Str.split (Str.regexp Filename.dir_sep) dir in
  let rec make_folders path = function
    | [] -> ()
    | f :: dep ->
        let p = Filename.(path / f) in
        make_folder p;
        make_folders p dep
  in
  make_folders "" folders

let init_folders () =
  Filename.unlink_dir !info.test_dir;
  Filename.unlink_dir !info.multi_test_dir;
  Filename.mkpath ~exists_ok:true !info.test_dir 0o755;
  Filename.mkpath ~exists_ok:true !info.multi_test_dir 0o755

let init program_dir out_dir =
  let t_dir =
    if !Cmdline.extension = "" then "unitcon-tests"
    else Utils.dot_to_dir_sep !Cmdline.extension
  in
  let mt_dir =
    if !Cmdline.extension = "" then "unitcon-multi-tests"
    else Utils.dot_to_dir_sep !Cmdline.extension
  in
  let infer_out_dir = Filename.(out_dir / "infer-out") in
  info :=
    {
      program_dir;
      summary_file = Filename.(infer_out_dir / "summary.json");
      error_summary_file = Filename.(infer_out_dir / "error-summaries.json");
      call_prop_file = Filename.(infer_out_dir / "call-proposition.json");
      class_info_file = Filename.(out_dir / "class-info.json");
      constant_file = Filename.(out_dir / "constant-info.json");
      test_dir = Filename.(out_dir / t_dir);
      multi_test_dir = Filename.(out_dir / mt_dir);
      expected_bug =
        Filename.(program_dir / Filename.(Utils.input_path / "expected-bug"));
    };
  init_folders ();
  get_bug_type
    Filename.(
      !info.program_dir / Filename.(Utils.input_path / "expected-bug-type"))

(* ************************************** *
   run program
 * ************************************** *)

let modify_execute_command command t_file_name = command ^ " " ^ t_file_name

let check_substring substr str =
  match Str.search_forward (Str.regexp substr) str 0 with
  | exception Not_found -> false
  | _ -> true

let missing_trace = [ "at java.lang.System.arraycopy(Native Method)[ \t\r\n]+" ]

let compare_stack_trace target_trace error_trace =
  List.fold_left
    (fun check missing_trace ->
      let curr_check =
        check_substring
          (!bug_type ^ ".*" ^ "[ \t\r\n]+[^a]*" ^ missing_trace ^ target_trace)
          error_trace
      in
      if curr_check then true else check)
    false ("" :: missing_trace)

let check_package_name_presence package_name error_trace =
  check_substring package_name error_trace

let check_target_method_presence error_trace =
  (* if you want to target the NPE,
     add "java.lang.NullPointerException.*" in front of the error method name *)
  check_substring !error_method_name error_trace

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
  else failwith "not supported build type"

let string_of_expected_bug file =
  if not (Sys.file_exists file) then ""
  else
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
  (* Exception ... Log=index= ... -----LogEnd----- *)
  let s_idx = get_index_of_substring target error_trace 0 in
  let e_idx =
    match s_idx with
    | None -> None
    | Some i -> get_index_of_substring "-----LogEnd-----" error_trace i
  in
  let trace_and_input =
    match (s_idx, e_idx) with
    | None, _ | _, None -> ""
    | Some s, Some e -> String.sub error_trace s (e - s + 3)
  in
  let rec get_input lst =
    match lst with
    | hd :: tl ->
        if check_substring "Log=" hd then
          let name_value =
            Str.replace_first (Str.regexp "Log=") "" hd
            |> Str.split (Str.regexp "=")
          in
          ( name_value |> List.hd,
            try name_value |> List.tl |> List.hd with _ -> "" )
          :: get_input tl
        else get_input tl
    | _ -> []
  in
  Str.split (Str.regexp "\n") trace_and_input |> get_input

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
  | Compile | Group -> execute command
  | Test -> execute ("timeout 5s " ^ command)

let simple_compiler program_dir command =
  let current_dir = Unix.getcwd () in
  Sys.chdir program_dir;
  let ic_out, ic_err = execute_command command in
  Sys.chdir current_dir;
  (ic_out, ic_err)

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
  remove_file Filename.(test_dir / last_file)

let rec remove_no_exec_files curr_num test_dir =
  if curr_num > !num_of_tc_files then ()
  else
    let curr_tc = "UnitconTest" ^ string_of_int curr_num ^ ".java" in
    let curr_class = "UnitconTest" ^ string_of_int curr_num ^ ".class" in
    remove_file Filename.(test_dir / curr_tc);
    remove_file Filename.(test_dir / curr_class);
    remove_no_exec_files (curr_num + 1) test_dir

let modify_files test_dir data =
  let error_files = get_compilation_error_files data in
  List.iter (fun file -> remove_file Filename.(test_dir / file)) error_files

let checking_init_err data =
  match
    Str.search_forward
      (Str.regexp "Error occurred during initialization of VM")
      data 0
  with
  | exception Not_found -> false
  | _ -> true

let checking_error_presence data =
  match Str.search_forward (Str.regexp "[0-9]+:* error") data 0 with
  | exception Not_found -> ()
  | _ -> raise Compilation_Error

let checking_bug_presence error_trace expected_bug_file =
  let expected_bug = string_of_expected_bug expected_bug_file in
  if !Cmdline.unknown_bug || expected_bug = "" then
    (check_package_name_presence
       (string_of_expected_bug expected_bug)
       error_trace
    || expected_bug = "")
    && check_target_method_presence error_trace
    && check_useless_npe error_trace |> not
  else compare_stack_trace expected_bug error_trace

let is_empty_file file =
  if not (Sys.file_exists file) then failwith (file ^ " not found");
  let ic = open_in file in
  let s = really_input_string ic (in_channel_length ic) in
  close_in ic;
  if Regexp.rm_space s = "" then true else false

(* ************************************** *
   make test contents
 * ************************************** *)

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
    let time = "/* Duration of synthesis: " ^ string_of_float time ^ " */\n" in
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

let print_stack_trace bug_type log =
  let bug =
    try bug_type |> Str.split (Str.regexp "\\.") |> List.rev |> List.hd
    with _ -> ""
  in
  let typ = if bug = "" then "Exception" else bug in
  let common =
    "catch(" ^ typ ^ " e) {\n" ^ "System.err.println(e.toString());\n"
    ^ "StackTraceElement[] stackTrace = e.getStackTrace();\n"
    ^ "for (int i = 0; i < stackTrace.length; i++) {\n"
    ^ "if ((stackTrace[i].toString()).contains(\"UnitconMultiTest\")) break;\n"
    ^ "System.err.println(\"at \" + stackTrace[i]);\n" ^ "}\n" ^ log ^ "}\n"
  in
  if bug = "" then common else common ^ "catch(Exception e) { }\n"

let rec close_bracket count =
  if count <= 0 then "" else "}\n" ^ close_bracket (count - 1)

let insert_multi_test oc
    (file_num, tc, (arrays, loop_stmt, loop_cnt, loop_input_log), time) =
  let insert oc (i_set, m_bodies) =
    let time = "/* Duration of synthesis: " ^ string_of_float time ^ " */\n" in
    let start = "@Test\npublic void test() {\n" in
    let bug_type =
      (* ref: get_bug_type, nested exception can not catch ... *)
      match Str.search_forward Regexp.dollar !bug_type 0 with
      | exception Not_found -> !bug_type
      | _ -> ""
    in
    let import =
      let common = get_imports i_set ^ "import org.junit.Test;\n" in
      if bug_type = "" then common ^ "\n"
      else common ^ "import " ^ bug_type ^ ";\n\n"
    in
    need_default_class m_bodies;
    get_package !Cmdline.extension |> output_string oc;
    (* if package is needed, add package keyword. Cmdline.extension does not contain the class name *)
    import |> output_string oc;
    output_string oc time;
    "public class UnitconMultiTest" ^ string_of_int file_num ^ " {\n"
    |> output_string oc;
    start ^ arrays ^ loop_stmt ^ "try {\n" ^ m_bodies ^ "}\n"
    ^ print_stack_trace bug_type loop_input_log
    ^ close_bracket loop_cnt ^ "}\n}\n"
    |> output_string oc;
    flush oc;
    close_out oc
  in
  insert oc tc

let add_default_class test_dir =
  let need_default_interface () =
    if !require_interface_class then (
      let oc = open_out Filename.(test_dir / "UnitconInterface.java") in
      get_package !Cmdline.extension |> output_string oc;
      output_string oc "interface UnitconInterface {}\n";
      close_out oc)
  in
  let need_default_enum () =
    if !require_enum_class then (
      let oc = open_out Filename.(test_dir / "UnitconEnum.java") in
      get_package !Cmdline.extension |> output_string oc;
      output_string oc "enum UnitconEnum {}\n";
      close_out oc)
  in
  need_default_interface ();
  need_default_enum ()

let add_testcase test_dir file_num (tc, time) =
  let oc =
    open_out
      Filename.(test_dir / (test_basename ^ string_of_int file_num ^ ".java"))
  in
  insert_test oc (file_num, tc, time);
  close_out oc

let add_multi_testcase test_dir file_num (tc, loop_info, time) =
  let oc =
    open_out
      Filename.(
        test_dir / (multi_test_basename ^ string_of_int file_num ^ ".java"))
  in
  insert_multi_test oc (file_num, tc, loop_info, time);
  close_out oc

(* ************************************** *
   run test cases
 * ************************************** *)

let compile_cmd info =
  "find " ^ info.test_dir ^ " -name \"*.java\" > "
  ^ Filename.(!Cmdline.out_dir / "test-files")
  ^ "; javac -cp with-dependency.jar:"
  ^ Filename.(Utils.unitcon_path / "deps/junit-4.13.2.jar")
  ^ ":"
  ^ Filename.(Utils.unitcon_path / "deps/hamcrest-core-1.3.jar")
  ^ ":" ^ info.program_dir ^ " @"
  ^ Filename.(!Cmdline.out_dir / "test-files")

let multi_test_compile_cmd info =
  "find " ^ info.multi_test_dir ^ " -name \"*.java\" > "
  ^ Filename.(!Cmdline.out_dir / "multi-test-files")
  ^ "; javac -cp with-dependency.jar:"
  ^ Filename.(Utils.unitcon_path / "deps/junit-4.13.2.jar")
  ^ ":"
  ^ Filename.(Utils.unitcon_path / "deps/hamcrest-core-1.3.jar")
  ^ ":" ^ info.program_dir ^ " @"
  ^ Filename.(!Cmdline.out_dir / "multi-test-files")

let build_program info =
  let rec compile_loop () =
    let ic_out, ic_err = simple_compiler !Cmdline.out_dir (compile_cmd info) in
    let data_out = read_all_string ic_out in
    let data_err = read_all_string ic_err in
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
    simple_compiler !Cmdline.out_dir (multi_test_compile_cmd info)
  in
  close_in ic_out;
  close_in ic_err

let normal_exit =
  Sys.Signal_handle
    (fun _ ->
      L.info "Normal End UnitCon for %s: %b(%d) (total time: %f)"
        !info.program_dir
        (if !num_of_success > 0 then true else false)
        !num_of_success
        (Unix.gettimeofday () -. !time);
      L.info "First Success Test: %s" !first_success_tc;
      L.info "Last Success Test: %s" !last_success_tc;
      (* clean up useless files and directories *)
      if !Cmdline.save_temp then ()
      else (
        remove_no_exec_files (!num_of_last_exec_tc + 1) !info.test_dir;
        remove_file Filename.(!info.program_dir / "multi-test-files");
        remove_all_files !info.multi_test_dir;
        Unix.rmdir !info.multi_test_dir);
      Unix._exit 0)

let get_test_path path base_name =
  if path = "" then base_name
  else Utils.dot_to_dir_sep path ^ Filename.dir_sep ^ base_name

(* Relative path should be used instead of absolute path
   e.g., ./unitcon-tests *)
let execute_cmd info =
  "java -cp with-dependency.jar:./unitcon-tests/:"
  ^ Filename.(Utils.unitcon_path / "deps/junit-4.13.2.jar")
  ^ ":"
  ^ Filename.(Utils.unitcon_path / "deps/hamcrest-core-1.3.jar")
  ^ ":" ^ info.program_dir ^ ":. " ^ "org.junit.runner.JUnitCore"

(* Relative path should be used instead of absolute path
   e.g., ./unitcon-multi-tests *)
let multi_test_execute_cmd info =
  "java -cp with-dependency.jar:./unitcon-multi-tests/:"
  ^ Filename.(Utils.unitcon_path / "deps/junit-4.13.2.jar")
  ^ ":"
  ^ Filename.(Utils.unitcon_path / "deps/hamcrest-core-1.3.jar")
  ^ ":" ^ info.program_dir ^ ":. " ^ "org.junit.runner.JUnitCore"

let run_testfile () =
  let compile_start = Unix.gettimeofday () in
  add_default_class !info.test_dir;
  L.info "Start compilation! (# of test files: %d)" !num_of_tc_files;
  build_program !info;
  L.info "End compilation! (duration: %f)"
    (Unix.gettimeofday () -. compile_start);
  let execute _ test_dir expected_bug t_file num_of_t_file =
    let ic_out, ic_err =
      simple_compiler !Cmdline.out_dir
        (modify_execute_command (execute_cmd !info) t_file)
    in
    let data = read_all_string ic_err in
    close_in ic_out;
    close_in ic_err;
    num_of_last_exec_tc := num_of_t_file;
    if checking_bug_presence data expected_bug then (
      if !first_success_tc = "" then first_success_tc := t_file;
      last_success_tc := t_file;
      incr num_of_success;
      L.info "Success Test: %s" t_file;
      Unix.kill (Unix.getpid ()) Sys.sigusr1)
    else if not (Sys.file_exists Filename.(test_dir / (t_file ^ ".java"))) then
      ()
    else (
      remove_file Filename.(test_dir / (t_file ^ ".java"));
      remove_file Filename.(test_dir / (t_file ^ ".class")))
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
  add_default_class !info.multi_test_dir;
  Filename.copy
    Filename.(Utils.unitcon_path / "deps/UnitconCombinator.java")
    Filename.(!info.multi_test_dir / "UnitconCombinator.java");
  L.info "Start multi-test! (# of multi-test: %d)" !num_of_multi_tc_files;
  build_multi_test !info;
  let mt_file =
    get_test_path !Cmdline.extension multi_test_basename
    ^ string_of_int !num_of_multi_tc_files
  in
  let ic_out, ic_err =
    simple_compiler !Cmdline.out_dir
      (modify_execute_command (multi_test_execute_cmd !info) mt_file)
  in
  let data = read_all_string ic_err in
  close_in ic_out;
  close_in ic_err;
  let found_rep_inputs =
    if checking_bug_presence data !info.expected_bug then (
      L.info "Found bug with loop: %s" mt_file;
      get_rep_input data !info.expected_bug)
    else []
  in
  L.info "End multi-test! (duration: %f)" (Unix.gettimeofday () -. compile_start);
  found_rep_inputs

(* force stop if generated test cases are not executed and only synthesis is long *)
let abnormal_run_test =
  Sys.Signal_handle
    (fun _ ->
      if !num_of_tc_files mod !Cmdline.batch_size <> 0 then (
        L.info "Abnormal Run Test";
        run_testfile ();
        Unix.kill (Unix.getpid ()) Sys.sigusr1)
      else (
        L.info "Keep Going";
        abnormal_keep_going := true))

let interrupt pid =
  Unix.sleep (!Cmdline.time_out - 10);
  Unix.kill pid Sys.sigusr2

let setup program_dir out_dir =
  (* for early stopping *)
  Sys.set_signal Sys.sigusr1 normal_exit;
  Sys.set_signal Sys.sigusr2 abnormal_run_test;
  Thread.create interrupt (Unix.getpid ()) |> ignore;
  time := Unix.gettimeofday ();
  init program_dir out_dir;
  let m_info = parse_method_info !info.summary_file in
  let t_info = Summary.from_method_type m_info in
  let summary = parse_summary !info.summary_file m_info in
  let cg =
    parse_callgraph !info.summary_file
    |> parse_extra_callgraph !info.class_info_file
  in
  let setter_map = get_setter summary m_info in
  let c_info, summary, m_info =
    parse_class_info !info.class_info_file summary m_info
  in
  let c_info, summary, m_info = parse_stdlib_info c_info summary m_info in
  let inst_info = parse_gconstant_info !info.constant_file in
  let prim_info = parse_primitive_info !info.constant_file in
  let cp_map = parse_callprop !info.call_prop_file in
  let error_method_info = parse_error_summary !info.error_summary_file in
  (* for unknown bug detection *)
  error_method_name :=
    Regexp.first_rm (Str.regexp "(.*)") (fst error_method_info)
    |> Str.split Regexp.dot |> List.rev |> List.hd;
  let data =
    {
      Generator.cg;
      summary;
      cp_map;
      m_info;
      t_info;
      c_info;
      setter_map;
      inst_info;
      prim_info;
    }
  in
  (error_method_info, data)
