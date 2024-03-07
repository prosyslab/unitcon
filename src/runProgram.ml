open Language
module F = Format
module Json = Yojson.Safe
module JsonUtil = Yojson.Safe.Util
module ImportSet = Utils.ImportSet

exception Compilation_Error

let con_path = "unitcon_properties"

let test_basename = "UnitconTest"

let time = ref 0.0

let num_of_tc_files = ref 1

let num_of_success = ref 0

let first_success_tc = ref ""

let last_success_tc = ref ""

let require_enum_class = ref false

let require_interface_class = ref false

let error_method_name = ref ""

type t = {
  program_dir : string;
  summary_file : string;
  error_summary_file : string;
  call_prop_file : string;
  inheritance_file : string;
  enum_file : string;
  constant_file : string;
  compile_command : string;
  execute_command : string;
  test_dir : string;
  expected_bug : string;
}

type run_type = Compile | Test

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
      compile_command = "";
      execute_command = "";
      test_dir = "";
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
  (info |> fst, info |> snd |> Modeling.add_java_package_inheritance)

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

let compile_command_of_file file =
  if not (Sys.file_exists file) then failwith (file ^ " not found");
  let ic = open_in file in
  let s = really_input_string ic (in_channel_length ic) |> Regexp.rm_space in
  close_in ic;
  s

let execute_command_of_file file =
  if not (Sys.file_exists file) then failwith (file ^ " not found");
  let ic = open_in file in
  let s = really_input_string ic (in_channel_length ic) |> Regexp.rm_space in
  close_in ic;
  s

let modify_execute_command command t_file_name =
  match Str.search_forward ("-encoding" |> Str.regexp) command 0 with
  | exception Not_found -> command ^ " " ^ t_file_name
  | _ ->
      Str.replace_first
        ("-encoding" |> Str.regexp)
        (t_file_name ^ " -encoding")
        command

let check_substring substr str =
  match Str.search_forward (Str.regexp substr) str 0 with
  | exception Not_found -> false
  | _ -> true

let compare_stack_trace target_trace error_trace =
  check_substring
    ("java.lang.NullPointerException" ^ "[ \t\r\n]+" ^ target_trace)
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
  if Str.string_match ("^javac" |> Str.regexp) str 0 then Compile
  else if Str.string_match ("^java" |> Str.regexp) str 0 then Test
  else failwith "not supported build type"

let string_of_expected_bug file =
  if not (Sys.file_exists file) then failwith (file ^ " not found");
  let ic = open_in file in
  let s = really_input_string ic (in_channel_length ic) in
  close_in ic;
  s
  |> Str.global_replace Regexp.dollar "\\$"
  |> Str.global_replace (Str.regexp "\n") "[ \t\r\n]+"

let execute_command command =
  let close_channel (stdout, stdin, stderr) =
    stdout |> close_in;
    stdin |> close_out;
    stderr
  in
  let execute command =
    let stdout, stdin, stderr =
      Unix.open_process_full command (Unix.environment ())
    in
    let pid = Unix.process_full_pid (stdout, stdin, stderr) in
    Unix.waitpid [ Unix.WUNTRACED ] pid |> ignore;
    close_channel (stdout, stdin, stderr)
  in
  match run_type command with
  | Compile -> execute command
  | Test -> execute ("timeout 5s " ^ command)

let simple_compiler program_dir command =
  let current_dir = Unix.getcwd () in
  Sys.chdir program_dir;
  let ic = execute_command command in
  Sys.chdir current_dir;
  ic

let get_imports i_set =
  let is_default_path i = String.contains i '.' |> not in
  let str_set =
    ImportSet.fold
      (fun i s ->
        let path = Utils.rm_object_array_import i in
        if i = "" || (Utils.is_array i && path = i) || is_default_path i then s
        else
          ImportSet.add
            ("import " ^ (path |> Utils.replace_nested_symbol) ^ ";\n")
            s)
      i_set ImportSet.empty
  in
  ImportSet.fold (fun i s -> s ^ i) str_set ""

let insert_test oc (file_num, tc, time) =
  let need_default_interface tc =
    match Str.search_forward ("UnitconInterface" |> Str.regexp) tc 0 with
    | exception _ -> ()
    | _ -> require_interface_class := true
  in
  let need_default_enum tc =
    match Str.search_forward ("UnitconEnum" |> Str.regexp) tc 0 with
    | exception _ -> ()
    | _ -> require_enum_class := true
  in
  let need_default_class tc =
    need_default_interface tc;
    need_default_enum tc
  in
  let insert oc (i_set, m_bodies) =
    let time = "/* Duration of synthesis: " ^ string_of_float time ^ "*/\n" in
    let start =
      "\npublic static void main(String args[]) throws Exception, Throwable {\n"
    in
    need_default_class m_bodies;
    get_imports i_set ^ "\n" |> output_string oc;
    time |> output_string oc;
    "public class UnitconTest" ^ string_of_int file_num ^ " {\n"
    |> output_string oc;
    start ^ m_bodies ^ "}\n}\n" |> output_string oc;
    flush oc;
    close_out oc
  in
  insert oc tc

let add_default_class test_dir =
  let need_default_interface () =
    if !require_interface_class then (
      let oc = open_out (Filename.concat test_dir "UnitconInterface.java") in
      "interface UnitconInterface {}\n" |> output_string oc;
      close_out oc)
  in
  let need_default_enum () =
    if !require_enum_class then (
      let oc = open_out (Filename.concat test_dir "UnitconEnum.java") in
      "enum UnitconEnum {}\n" |> output_string oc;
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

let remove_file fname = if Sys.file_exists fname then Unix.unlink fname

let remove_files dir (pattern : Str.regexp) =
  let remove_file file =
    if Str.string_match pattern file 0 then
      Unix.unlink (Filename.concat dir file)
  in
  let files = Array.to_list (Sys.readdir dir) in
  List.iter (fun file -> remove_file file) files

let remove_all_test_classes test_dir = remove_files test_dir Regexp.test_class

let remove_all_test_files test_dir = remove_files test_dir Regexp.test_file

let init_test_folder test_dir =
  try Unix.mkdir test_dir 0o775
  with Unix.Unix_error (Unix.EEXIST, _, _) ->
    ();
    remove_all_test_classes test_dir;
    remove_all_test_files test_dir;
    remove_file (Filename.concat test_dir "UnitconInterface.java");
    remove_file (Filename.concat test_dir "UnitconEnum.java");
    remove_file (Filename.concat test_dir "UnitconInterface.class");
    remove_file (Filename.concat test_dir "UnitconEnum.class")

let get_compilation_error_files data =
  let get_f_name line =
    String.split_on_char ':' line |> List.hd |> Filename.basename
  in
  let data = data |> String.split_on_char '\n' in
  List.fold_left
    (fun f_list line ->
      if Str.string_match (".*UnitconTest[0-9]+\\.java" |> Str.regexp) line 0
      then
        let file_name = get_f_name line in
        file_name :: f_list
      else f_list)
    [] data

let modify_files test_dir data =
  let error_files = get_compilation_error_files data in
  List.iter
    (fun file -> remove_file (Filename.concat test_dir file))
    error_files

let checking_error_presence data =
  match Str.search_forward ("[0-9]+ error" |> Str.regexp) data 0 with
  | exception Not_found -> ()
  | _ -> raise Compilation_Error

(* let checking_bug_presence data expected_bug =
   let check_bug bug = compare_stack_trace bug data in
   check_bug (string_of_expected_bug expected_bug) *)

let checking_bug_presence error_trace expected_bug =
  if !Cmdline.unknown_bug then
    check_package_name_presence
      (string_of_expected_bug expected_bug)
      error_trace
    && check_target_method_presence error_trace
    && check_useless_npe error_trace |> not
  else compare_stack_trace (string_of_expected_bug expected_bug) error_trace

let init program_dir =
  let cons = Filename.concat in
  let program_dir =
    if Filename.is_relative program_dir then cons (Unix.getcwd ()) program_dir
    else program_dir
  in
  info :=
    {
      program_dir;
      summary_file = cons con_path "summary.json" |> cons program_dir;
      error_summary_file =
        cons con_path "error_summarys.json" |> cons program_dir;
      call_prop_file = cons con_path "call_proposition.json" |> cons program_dir;
      inheritance_file =
        cons con_path "inheritance_info.json" |> cons program_dir;
      enum_file = cons con_path "enum_info.json" |> cons program_dir;
      constant_file = cons con_path "extra_constant.json" |> cons program_dir;
      compile_command = cons con_path "compile_command" |> cons program_dir;
      execute_command = cons con_path "execute_command" |> cons program_dir;
      test_dir = cons program_dir "unitcon_tests";
      expected_bug = cons con_path "expected_bug" |> cons program_dir;
    };
  init_test_folder !info.test_dir;
  cons !info.test_dir "log.txt" |> Logger.from_file;
  Logger.info "Start UnitCon for %s" program_dir

(* return: (testcase * list(partial testcase)) *)
let make_testcase ~is_start queue e_method_info program_info =
  Generator.mk_testcases ~is_start queue e_method_info program_info

let build_program info =
  let compile_cmd = compile_command_of_file info.compile_command in
  (* javac *)
  let rec compile_loop () =
    let ic = simple_compiler info.program_dir compile_cmd in
    let data = my_really_read_string ic in
    ic |> close_in;
    match checking_error_presence data with
    | exception Compilation_Error ->
        modify_files info.test_dir data;
        compile_loop ()
    | _ -> ()
  in
  compile_loop ()

let abnormal_exit =
  Sys.Signal_handle
    (fun _ ->
      Logger.info "Abnormal End UnitCon for %s: %b(%d) (total time: %f)"
        !info.program_dir
        (if !num_of_success > 0 then true else false)
        !num_of_success
        (Unix.gettimeofday () -. !time);
      Logger.info "First Success Test: %s" !first_success_tc;
      Logger.info "Last Success Test: %s" !last_success_tc;
      Unix._exit 0)

(* if the max running time is exceeded, UnitCon is forced to shut down *)
let interrupt pid =
  Unix.sleep !Cmdline.max_run_time;
  Unix.kill pid Sys.sigusr2

let run_testfile () =
  Sys.set_signal Sys.sigusr2 abnormal_exit;
  Thread.create interrupt (Unix.getpid ()) |> ignore;
  let compile_start = Unix.gettimeofday () in
  add_default_class !info.test_dir;
  Logger.info "Start compilation! (# of test files: %d)" (!num_of_tc_files - 1);
  build_program !info;
  Logger.info "End compilation! (duration: %f)"
    (Unix.gettimeofday () -. compile_start);
  let execute_cmd = execute_command_of_file !info.execute_command in
  let execute program_dir test_dir expected_bug t_file =
    let ic =
      simple_compiler program_dir (modify_execute_command execute_cmd t_file)
    in
    let data = my_really_read_string ic in
    ic |> close_in;
    if checking_bug_presence data expected_bug then (
      if !first_success_tc = "" then first_success_tc := t_file;
      last_success_tc := t_file;
      incr num_of_success)
    else if not (Sys.file_exists (Filename.concat test_dir (t_file ^ ".java")))
    then ()
    else (
      remove_file (Filename.concat test_dir (t_file ^ ".java"));
      remove_file (Filename.concat test_dir (t_file ^ ".class")))
  in
  let rec execute_test current_f_num program_dir test_dir expected_bug =
    if current_f_num < !num_of_tc_files then (
      execute program_dir test_dir expected_bug
        (test_basename ^ string_of_int current_f_num);
      execute_test (current_f_num + 1) program_dir test_dir expected_bug)
  in
  execute_test 1 !info.program_dir !info.test_dir !info.expected_bug;
  Logger.info "Normal End UnitCon for %s: %b(%d) (total time: %f)\n"
    !info.program_dir
    (if !num_of_success > 0 then true else false)
    !num_of_success
    (Unix.gettimeofday () -. !time);
  Logger.info "First Success Test: %s" !first_success_tc

let abnormal_run =
  Sys.Signal_handle
    (fun _ ->
      Unix.alarm 0 |> ignore;
      run_testfile ())

(* queue: (testcase * list(partial testcase)) *)
let rec run_test ~is_start info queue e_method_info p_info =
  let tc, tc_list = make_testcase ~is_start queue e_method_info p_info in
  if tc = (ImportSet.empty, "") then
    (* early stopping *)
    Unix.kill (Unix.getpid ()) Sys.sigusr1
  else
    let time = Unix.gettimeofday () -. !time in
    add_testcase info.test_dir !num_of_tc_files (tc, time);
    incr num_of_tc_files;
    run_test ~is_start:false info tc_list e_method_info p_info

let run program_dir =
  (* for early stopping *)
  Sys.set_signal Sys.sigusr1 abnormal_run;
  time := Unix.gettimeofday ();
  init program_dir;
  let method_info = parse_method_info !info.summary_file in
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
    Regexp.first_rm ("(.*)" |> Str.regexp) (error_method_info |> fst)
    |> Str.split Regexp.dot |> List.rev |> List.hd;
  run_test ~is_start:true !info [] error_method_info
    ( callgraph,
      summary,
      call_prop_map,
      method_info,
      class_info,
      setter_map,
      instance_info,
      primitive_info )
