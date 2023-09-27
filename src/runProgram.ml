module F = Format
module Json = Yojson.Safe
module JsonUtil = Yojson.Safe.Util
module EnumInfo = Language.EnumInfo

let con_path = "unitcon_properties"

let trial = ref 0

let time = ref 0.0

type t = {
  program_dir : string;
  summary_file : string;
  error_summary_file : string;
  call_prop_file : string;
  inheritance_file : string;
  enum_file : string;
  build_command : string;
  test_command : string;
  test_file : string;
  expected_bug : string;
}

type build_type = Maven | Javac of string

type expected_bug_type = TESTCASE | TRACE of string

let get_pkg str =
  str
  |> Regexp.first_rm (".*/java/" |> Str.regexp)
  |> Regexp.first_rm ("[a-zA-Z0-9]*\\.java$" |> Str.regexp)
  |> Str.global_replace ("/" |> Str.regexp) "."

(* ************************************** *
   parse analyzer's output
 * ************************************** *)

let output name data =
  let dirname = !Cmdline.out_dir ^ "/marshal" in
  if not (Sys.file_exists dirname) then failwith (dirname ^ " not found");
  let chan = open_out (dirname ^ "/" ^ name) in
  Marshal.to_channel chan data [];
  close_out chan

let input name =
  let dirname = !Cmdline.out_dir ^ "/marshal" in
  if not (Sys.file_exists dirname) then failwith (dirname ^ " not found");
  let chan = open_in (dirname ^ "/" ^ name) in
  let data = Marshal.from_channel chan in
  close_in chan;
  data

let parse_method_info filename =
  let json = Json.from_file filename in
  let filename = Filename.basename filename in
  output filename json;
  let data = input filename in
  Summary.from_method_json data

let parse_summary filename minfo =
  let filename = Filename.basename filename in
  let data = input filename in
  Summary.from_summary_json minfo data

let parse_callgraph filename =
  let filename = Filename.basename filename in
  let data = input filename in
  Callgraph.of_json data

let get_setter summary m_info = Setter.from_summary_map summary m_info

let parse_error_summary filename =
  Parser.parse_errprop filename;
  let filename = Filename.basename filename in
  let data = input (filename ^ ".json") in
  ErrorSummary.from_error_summary_json data

let parse_callprop filename =
  Parser.parse_callprop filename;
  let filename = Filename.basename filename in
  let data = input (filename ^ ".json") in
  CallProposition.from_callprop_json data

let parse_class_info filename =
  let json = Json.from_file filename in
  let elem = JsonUtil.to_list json |> List.hd in
  let info = Inheritance.of_json elem in
  (info |> fst, info |> snd |> Modeling.add_java_package_inheritance)

let parse_enum_info filename =
  if not (Sys.file_exists filename) then EnumInfo.M.empty
  else Json.from_file filename |> Enum.of_json

(* ************************************** *
   build program
 * ************************************** *)

let build_command_of_file file =
  if not (Sys.file_exists file) then failwith (file ^ " not found");
  let ic = open_in file in
  let s = really_input_string ic (in_channel_length ic) in
  close_in ic;
  s

let test_command_of_file file =
  if not (Sys.file_exists file) then ""
  else
    let ic = open_in file in
    let s = really_input_string ic (in_channel_length ic) in
    close_in ic;
    s

let test_file_of_file file =
  if not (Sys.file_exists file) then failwith (file ^ " not found");
  let ic = open_in file in
  let s = input_line ic in
  close_in ic;
  s

(* copy test file to unitcon folder *)
let cp_test_file p_dir file =
  let filename =
    Filename.basename file |> Filename.concat con_path |> Filename.concat p_dir
  in
  if Sys.file_exists filename then ()
  else
    let ic = open_in file in
    let oc = open_out filename in
    output_string oc (really_input_string ic (in_channel_length ic));
    close_in ic;
    flush oc;
    close_out oc

let find word str =
  match Str.search_forward (word |> Str.regexp) str 0 with
  | exception Not_found -> false
  | _ -> true

let build_type_of_string str =
  if Str.string_match (".*mvn" |> Str.regexp) str 0 then Maven
  else if Str.string_match ("^javac" |> Str.regexp) str 0 then Javac "compile"
  else if Str.string_match ("^java" |> Str.regexp) str 0 then Javac "run"
  else failwith "not supported build type"

let string_of_expected_bug file =
  if not (Sys.file_exists file) then failwith (file ^ " not found");
  match open_in file |> input_line with
  | s when Str.string_match ("^test_case" |> Str.regexp) s 0 -> TESTCASE
  | s -> TRACE (Str.global_replace Regexp.dollar "\\$" s)

let simple_compiler program_dir build_command =
  let current_dir = Unix.getcwd () in
  Sys.chdir program_dir;
  let stdout, stdin, stderr = Unix.open_process_full build_command [| "" |] in
  Sys.chdir current_dir;
  close_out stdin;
  match build_type_of_string build_command with
  | Maven when Str.string_match (Str.regexp ".*Java-WebSocket") program_dir 0 ->
      close_in stdout;
      Event.always stderr |> Event.sync
  | Maven ->
      close_in stderr;
      Event.always stdout |> Event.sync
  | Javac typ ->
      if typ = "compile" then (
        close_in stderr;
        Event.always stdout |> Event.sync)
      else (
        close_in stdout;
        Event.always stderr |> Event.sync)

(* test: (string * string) *)
let insert_test test_type test org_file new_file =
  let modify_test_code test_type code =
    match test_type with
    | "JUnit" -> code
    | "Not_JUnit" -> Regexp.first_rm (Str.regexp "@.*\\\n") code
    | "Javac" -> Regexp.first_rm (Str.regexp "@.*\\\n.*{\\\n") code
    | _ -> failwith "not supported"
  in
  let need_default_class tc =
    match Str.search_forward ("unitcon_interface" |> Str.regexp) tc 0 with
    | exception _ -> (
        match Str.search_forward ("unitcon_enum" |> Str.regexp) tc 0 with
        | exception _ -> None
        | _ -> Some "unitcon_enum")
    | _ -> Some "unitcon_interface"
  in
  let insert_default_class c =
    match c with
    | Some "unitcon_interface" -> "interface unitcon_interface {}\n"
    | Some "unitcon_enum" -> "enum unitcon_enum {}\n"
    | _ -> ""
  in
  let check_symbol = function
    | "JUnit" -> ".*@Test"
    | "Not_JUnit" -> ".*class"
    | _ -> failwith "not supported"
  in
  let rec insert_maven test_type check_import check_test ic oc =
    match input_line ic with
    | s when Str.string_match Regexp.package s 0 && not check_import ->
        output_string oc (s ^ "\n");
        output_string oc ((test |> fst) ^ "\n");
        insert_maven test_type true check_test ic oc
    | s
      when Str.string_match (Str.regexp (check_symbol test_type)) s 0
           && not check_test ->
        insert_default_class (test |> snd |> need_default_class)
        |> output_string oc;
        output_string oc ((test |> snd |> modify_test_code test_type) ^ "\n");
        output_string oc (s ^ "\n");
        insert_maven test_type check_import true ic oc
    | s ->
        output_string oc (s ^ "\n");
        insert_maven test_type check_import check_test ic oc
    | exception End_of_file ->
        flush oc;
        close_out oc
  in
  let insert_javac oc =
    output_string oc
      ((test |> fst) ^ "\n" ^ "public class Main {\n"
     ^ "public static void main(String args[]) throws Exception {"
      ^ (test |> snd |> modify_test_code test_type)
      ^ "}\n");
    flush oc;
    close_out oc
  in
  let ic = open_in org_file in
  let oc = open_out new_file in
  match test_type with
  | "Javac" -> insert_javac oc
  | _ -> insert_maven test_type false false ic oc

(* new_tc: (string * string) *)
let add_testcase new_tc cmd org_file file_in_program =
  if Sys.file_exists file_in_program then Sys.remove file_in_program else ();
  let ic = open_in org_file in
  let org_data = really_input_string ic (in_channel_length ic) in
  match build_type_of_string cmd with
  | Maven when find "@Test" org_data ->
      insert_test "JUnit" new_tc org_file file_in_program
  | Maven -> insert_test "Not_JUnit" new_tc org_file file_in_program
  | Javac _ -> insert_test "Javac" new_tc org_file file_in_program

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

let checking_bug_presence ic expected_bug =
  (* print_endline "checking ..."; *)
  let data = my_really_read_string ic in
  close_in ic;
  match string_of_expected_bug expected_bug with
  | TESTCASE when find "There are test failures" data ->
      find "unitcon_test" data
  | TRACE s -> find s data && find "NullPointerException" data
  | _ -> false

let init program_dir =
  let cons = Filename.concat in
  let program_dir =
    if Filename.is_relative program_dir then cons (Unix.getcwd ()) program_dir
    else program_dir
  in
  {
    program_dir;
    summary_file = cons con_path "summary.json" |> cons program_dir;
    error_summary_file = cons con_path "error_summarys" |> cons program_dir;
    call_prop_file = cons con_path "call_proposition" |> cons program_dir;
    inheritance_file = cons con_path "inheritance_info.json" |> cons program_dir;
    enum_file = cons con_path "enum_info.json" |> cons program_dir;
    build_command = cons con_path "build_command" |> cons program_dir;
    test_command = cons con_path "test_command" |> cons program_dir;
    test_file =
      test_file_of_file (cons con_path "test_file" |> cons program_dir)
      |> cons program_dir;
    expected_bug = cons con_path "expected_bug" |> cons program_dir;
  }

(* return: (testcase * list(partial testcase)) *)
let make_testcase ~is_start queue e_method_info program_info =
  Generator.mk_testcases ~is_start queue e_method_info program_info

let build_program info tc =
  let build_cmd = build_command_of_file info.build_command in
  let test_cmd = test_command_of_file info.test_command in
  add_testcase tc build_cmd
    (Filename.basename info.test_file
    |> Filename.concat con_path
    |> Filename.concat info.program_dir)
    info.test_file;
  match test_cmd with
  | "" ->
      (* maven *)
      simple_compiler info.program_dir build_cmd
  | _ ->
      (* javac *)
      simple_compiler info.program_dir build_cmd |> close_in;
      Unix.wait () |> ignore;
      let x = simple_compiler info.program_dir test_cmd in
      Unix.wait () |> ignore;
      x

(* queue: (testcase * list(partial testcase)) *)
let rec run_test ~is_start pkg info queue e_method_info p_info =
  incr trial;
  let tc, tc_list = make_testcase ~is_start pkg queue e_method_info p_info in
  if tc = ("", "") then failwith "can't proceed anymore";
  let result_ic = build_program info tc in
  if checking_bug_presence result_ic info.expected_bug then (
    "# of trial: " ^ (!trial |> string_of_int) |> print_endline;
    "duration: " ^ (Float.sub (Unix.time ()) !time |> string_of_float)
    |> print_endline;
    if !Cmdline.until_time_out then (
      tc |> fst |> print_endline;
      tc |> snd |> print_endline;
      close_in result_ic |> ignore;
      run_test ~is_start:false pkg info tc_list e_method_info p_info)
    else (
      close_in result_ic |> ignore;
      tc))
  else (
    close_in result_ic |> ignore;
    run_test ~is_start:false pkg info tc_list e_method_info p_info)

let run program_dir =
  time := Unix.time ();
  let info = init program_dir in
  cp_test_file info.program_dir info.test_file;
  let method_info = parse_method_info info.summary_file in
  let summary = parse_summary info.summary_file method_info in
  let callgraph = parse_callgraph info.summary_file in
  let setter_map = get_setter summary method_info in
  let class_info = parse_class_info info.inheritance_file in
  let enum_info = parse_enum_info info.enum_file in
  let call_prop_map = parse_callprop info.call_prop_file in
  let error_method_info = parse_error_summary info.error_summary_file in
  run_test ~is_start:true (get_pkg info.test_file) info [] error_method_info
    ( callgraph,
      summary,
      call_prop_map,
      method_info,
      class_info,
      setter_map,
      enum_info )
  |> snd |> print_endline
