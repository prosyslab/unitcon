open Utils
module C = Cmdliner
module Cmd = C.Cmd
module Arg = C.Arg
module Manpage = C.Manpage
module Term = C.Term

type command = Build | Analyze | Synthesize

let command = ref Synthesize

let debug = ref false

let quiet = ref false

let target_program : string ref = ref ""

let out_dir = ref "unitcon-out"

(* build options *)
let class_info = ref false

let constant_info = ref false

let command_maker = ref false

(* analyze options *)

let keep_going = ref false

let interproc = ref false

let skip_procedures : string ref = ref ""

let java_version = ref 8

(* analyze and synthesize options *)
let target = ref ""

(* synthesize options *)
let basic_mode = ref false

let pruning_mode = ref false

let priority_mode = ref false

let test_case_ast = ref false

let time_out = ref (10 * 60) (* total synthesis running time *)

let margin = ref 10 (* margin for not yet running test cases *)

let unknown_bug = ref false

let mock = ref false

let extension = ref ""

let with_loop = ref true

let batch_size = ref 15

let save_temp = ref false

let ignore = ref []

let docs = Manpage.s_common_options

let _debug =
  let doc = "Enable debug mode (verbose logging)" in
  Arg.(value & flag & info [ "debug" ] ~docs ~doc)

let _quiet =
  Arg.(
    value & flag & info [ "q"; "quiet" ] ~docs ~doc:"Turn off detailed outputs")

let _target_program =
  Arg.(last & pos_all string [] & info [] ~doc:"Target program")

let _out_dir =
  let default = Filename.((Filename.cwd |> Filename.resolve) / "unitcon-out") in
  Arg.(
    value & opt string default
    & info [ "o"; "out-dir" ] ~docs ~docv:"DIR" ~doc:"Output directory")

let _class_info =
  let doc = "Analyze syntactic properties of a given Java bytecode file" in
  Arg.(value & flag & info [ "class-info" ] ~doc)

let _constant_info =
  let doc = "Parse constant values of a given Java bytecode file" in
  Arg.(value & flag & info [ "constant-info" ] ~doc)

let _command_maker =
  let doc =
    "Compile a given target program, and make it into a jar file for \
     dependencies of test cases"
  in
  Arg.(value & flag & info [ "command-maker" ] ~doc)

let _keep_going =
  let doc = "Keep going when the analysis encounters a failure" in
  Arg.(value & flag & info [ "keep-going" ] ~doc)

let _interproc =
  let doc = "Make force alarm when interprocedure analyze" in
  Arg.(value & flag & info [ "interproc" ] ~doc)

let _skip_procedures =
  let doc = "Procedures that do not want to analyze" in
  Arg.(value & opt string "" & info [ "skip-procedures" ] ~doc)

let _java_version =
  let doc = "Set Java version" in
  Arg.(value & opt int 8 & info [ "java-version" ] ~doc)

let _target =
  let doc = "Set target location in form of [file]:[line]" in
  Arg.(value & opt string "" & info [ "target" ] ~doc)

let _basic_mode =
  let doc = "Run without optimization (default: false)" in
  Arg.(value & flag & info [ "basic-mode" ] ~doc)

let _pruning_mode =
  let doc = "Run with only pruning (default: false)" in
  Arg.(value & flag & info [ "pruning-mode" ] ~doc)

let _priority_mode =
  let doc = "Run with only prioritization (default: false)" in
  Arg.(value & flag & info [ "priority-mode" ] ~doc)

let _test_case_ast =
  let doc =
    "Set structure of test case to AST (default structure: def-use-graph)"
  in
  Arg.(value & flag & info [ "test-case-ast" ] ~doc)

let _time_out =
  let doc = "Time Budget except Static Analysis (default: 10m)" in
  Arg.(value & opt int (10 * 60) & info [ "time-out" ] ~doc)

let _unknown_bug =
  let doc = "Run unknown bug searching mode (default: false)" in
  Arg.(value & flag & info [ "unknown-bug" ] ~doc)

let _mock =
  Arg.(value & flag & info [ "mock" ] ~doc:"Use mock (default: false)")

let _extension =
  let doc =
    "Extend the available modifiers from public to package (e.g., \
     \"com.a.b.c\")"
  in
  Arg.(value & opt string "" & info [ "modifier-extension" ] ~doc)

let _batch_size =
  let doc = "Compile batch size (default: 15)" in
  Arg.(value & opt int 15 & info [ "batch-size" ] ~doc)

let _save_temp =
  let doc = "Save the all files (default: false)" in
  Arg.(value & flag & info [ "save-temp" ] ~doc)

let _ignore =
  Arg.(
    value
    & opt (list ~sep:' ' string) []
    & info [ "ignore" ] ~doc:"Ignore methods (sep: \' \')")

let init _debug _quiet _target_program _out_dir =
  Filename.mkdir _out_dir 0o755 ~exists_ok:true;
  Filename.mkdir Filename.(_out_dir / "marshal") 0o755 ~exists_ok:true;
  Filename.(_out_dir / "log.txt") |> L.from_file ~console_fmt:F.std_formatter;
  if _debug then L.set_level L.DEBUG else L.set_level L.INFO;
  L.info "%s" (String.concat " " (Array.to_list Sys.argv));
  debug := _debug;
  quiet := _quiet;
  target_program := Filename.resolve _target_program;
  out_dir := Filename.resolve _out_dir

let common_opt =
  Term.(const init $ _debug $ _quiet $ _target_program $ _out_dir)

module Build = struct
  let opt _copt _class_info _constant_info _command_maker =
    command := Build;
    class_info := _class_info;
    constant_info := _constant_info;
    command_maker := _command_maker

  let cmd =
    let name = "build" in
    let doc =
      "build the program and preprocess the information of the program"
    in
    let man = [ `S Manpage.s_description ] in
    let info = Cmd.info name ~doc ~man in
    Cmd.v info
      Term.(
        const opt $ common_opt $ _class_info $ _constant_info $ _command_maker)
end

module Analyze = struct
  let opt _copt _target _keep_going _interproc _skip_procedures _java_version =
    command := Analyze;
    target := _target;
    keep_going := _keep_going;
    interproc := _interproc;
    skip_procedures := _skip_procedures;
    java_version := _java_version

  let cmd =
    let name = "analyze" in
    let doc = "Analyze the program" in
    let man = [ `S Manpage.s_description ] in
    let info = C.Cmd.info name ~doc ~man in
    Cmd.v info
      Term.(
        const opt $ common_opt $ _target $ _keep_going $ _interproc
        $ _skip_procedures $ _java_version)
end

module Synthesize = struct
  let opt _copt _target _basic_mode _pruning_mode _priority_mode _test_case_ast
      _time_out _unknown_bug _mock _extension _batch_size _save_temp _ignore =
    command := Synthesize;
    target := _target;
    basic_mode := _basic_mode;
    pruning_mode := _pruning_mode;
    priority_mode := _priority_mode;
    test_case_ast := _test_case_ast;
    time_out := _time_out;
    margin := if _time_out / 60 >= 10 then 10 else _time_out / 60;
    unknown_bug := _unknown_bug;
    mock := _mock;
    extension := _extension;
    batch_size := _batch_size;
    save_temp := _save_temp;
    ignore := _ignore

  let cmd =
    let name = "synthesize" in
    let doc = "Synthesize the test cases that triggering given locations" in
    let man = [ `S Manpage.s_description ] in
    let info = C.Cmd.info name ~doc ~man in
    Cmd.v info
      Term.(
        const opt $ common_opt $ _target $ _basic_mode $ _pruning_mode
        $ _priority_mode $ _test_case_ast $ _time_out $ _unknown_bug $ _mock
        $ _extension $ _batch_size $ _save_temp $ _ignore)
end

let main_cmd =
  let name = "unitcon" in
  let doc = "A test case synthesizer" in
  let man = [ `S Manpage.s_description ] in
  let info = Cmd.info name ~version:"0.0.1" ~doc ~man in
  Cmd.group info [ Build.cmd; Analyze.cmd; Synthesize.cmd ]

let parse () =
  match Cmd.eval_value main_cmd with
  | Ok v -> ( match v with `Ok t -> t | _ -> exit 1)
  | _ -> exit 1
