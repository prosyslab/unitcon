open Language
module F = Format
module Json = Yojson.Safe
module JsonUtil = Yojson.Safe.Util
module ImportSet = Utils.ImportSet

let con_path = "unitcon_properties"

let time = ref 0.0

let imports = ref ImportSet.empty

let codes : string list ref = ref []

let test_file = ref ""

type t = {
  program_dir : string;
  summary_file : string;
  error_summary_file : string;
  call_prop_file : string;
  inheritance_file : string;
  enum_file : string;
  constant_file : string;
  extra_callee_file : string;
  compile_command : string;
  test_command : string;
  test_file : string;
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
      extra_callee_file = "";
      compile_command = "";
      test_command = "";
      test_file = "";
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

let parse_extra_callee filename minfo callgraph =
  if not (Sys.file_exists filename) then callgraph
  else Json.from_file filename |> Callgraph.of_extra_json minfo callgraph

(* ************************************** *
   run program
 * ************************************** *)

let compile_command_of_file file =
  if not (Sys.file_exists file) then failwith (file ^ " not found");
  let ic = open_in file in
  let s = really_input_string ic (in_channel_length ic) in
  close_in ic;
  s

let test_command_of_file file =
  if not (Sys.file_exists file) then failwith (file ^ " not found");
  let ic = open_in file in
  let s = really_input_string ic (in_channel_length ic) in
  close_in ic;
  s

let find word str =
  match
    Str.search_forward
      (".*java.lang.NullPointerException" ^ "[ \t\r\n]+" ^ word |> Str.regexp)
      str 0
  with
  | exception Not_found -> false
  | _ -> true

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

let simple_compiler program_dir command =
  let current_dir = Unix.getcwd () in
  Sys.chdir program_dir;
  let stdout, stdin, stderr =
    Unix.open_process_full command (Unix.environment ())
  in
  let pid = Unix.process_full_pid (stdout, stdin, stderr) in
  match run_type command with
  | Compile ->
      Unix.waitpid [] pid |> ignore;
      Sys.chdir current_dir;
      close_out stdin;
      close_in stderr;
      stdout
  | Test ->
      Unix.waitpid [ Unix.WNOHANG ] pid |> ignore;
      Sys.chdir current_dir;
      close_out stdin;
      close_in stdout;
      stderr

let get_test_method num body =
  let method_name = "test" ^ string_of_int num ^ "()" in
  let start = "public static void " ^ method_name ^ " throws Exception {\n" in
  let catch = "catch(Exception e){\n  e.printStackTrace();\n}\n" in
  let code = start ^ "try{\n" ^ body ^ "}\n" ^ catch ^ "}\n\n" in
  (method_name, code)

let get_test_methods code_list =
  List.fold_left
    (fun (num, method_names, methods) code ->
      let m_name, m_body = get_test_method num code in
      (num + 1, method_names ^ m_name ^ ";\n", methods ^ m_body ^ "\n"))
    (1, "", "") code_list

let get_imports i_set =
  let str_set =
    ImportSet.fold
      (fun i s ->
        let path = Utils.rm_object_array_import i in
        if i = "" || (Utils.is_array i && path = i) then s
        else
          ImportSet.add
            ("import " ^ (path |> Utils.replace_nested_symbol) ^ ";\n")
            s)
      i_set ImportSet.empty
  in
  ImportSet.fold (fun i s -> s ^ i) str_set ""

let insert_test test_file =
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
  let insert oc =
    let start =
      "\npublic static void main(String args[]) throws Exception {\n"
    in
    let _, method_names, m_bodies = get_test_methods (!codes |> List.rev) in
    get_imports !imports ^ "\n" |> output_string oc;
    insert_default_class (m_bodies |> need_default_class) |> output_string oc;
    "public class UnitconTest {\n" |> output_string oc;
    start ^ method_names ^ "}" ^ m_bodies ^ "}" |> output_string oc;
    flush oc;
    close_out oc
  in
  let oc = open_out test_file in
  insert oc

let add_testcase test_file =
  if Sys.file_exists (Filename.remove_extension test_file ^ ".class") then
    Sys.remove (Filename.remove_extension test_file ^ ".class")
  else ();
  insert_test test_file

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
  let check_bug bug = find bug data in
  check_bug (string_of_expected_bug expected_bug)

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
      extra_callee_file = cons con_path "extra_callee.json" |> cons program_dir;
      compile_command = cons con_path "compile_command" |> cons program_dir;
      test_command = cons con_path "test_command" |> cons program_dir;
      test_file = cons program_dir "UnitconTest.java";
      expected_bug = cons con_path "expected_bug" |> cons program_dir;
    }

(* return: (testcase * list(partial testcase)) *)
let make_testcase ~is_start queue e_method_info program_info =
  Generator.mk_testcases ~is_start queue e_method_info program_info

let build_program info =
  let compile_cmd = compile_command_of_file info.compile_command in
  let test_cmd = test_command_of_file info.test_command in
  add_testcase info.test_file;
  (* javac *)
  simple_compiler info.program_dir compile_cmd |> close_in;
  simple_compiler info.program_dir test_cmd

(* queue: (testcase * list(partial testcase)) *)
let rec run_test ~is_start pkg info queue e_method_info p_info =
  let tc, tc_list = make_testcase ~is_start pkg queue e_method_info p_info in
  if tc = (ImportSet.empty, "") then ( (* TODO: early stopping *) )
  else (
    imports := ImportSet.union !imports (tc |> fst);
    codes := (tc |> snd) :: !codes);
  run_test ~is_start:false pkg info tc_list e_method_info p_info

let run program_dir =
  time := Unix.time ();
  init program_dir;
  let method_info = parse_method_info !info.summary_file in
  let summary = parse_summary !info.summary_file method_info in
  let callgraph =
    parse_callgraph !info.summary_file
    |> parse_extra_callee !info.extra_callee_file method_info
  in
  let setter_map = get_setter summary method_info in
  let class_info = parse_class_info !info.inheritance_file in
  let instance_info =
    parse_enum_info !info.enum_file |> parse_instance_info !info.constant_file
  in
  let primitive_info = parse_primitive_info !info.constant_file in
  let call_prop_map = parse_callprop !info.call_prop_file in
  let error_method_info = parse_error_summary !info.error_summary_file in
  run_test ~is_start:true "FIXME" !info [] error_method_info
    ( callgraph,
      summary,
      call_prop_map,
      method_info,
      class_info,
      setter_map,
      instance_info,
      primitive_info )

let run_testfile () =
  let result_ic = build_program !info in
  if checking_bug_presence result_ic !info.expected_bug then (
    close_in result_ic |> ignore;
    "true" |> print_endline)
  else (
    close_in result_ic |> ignore;
    "false" |> print_endline)
