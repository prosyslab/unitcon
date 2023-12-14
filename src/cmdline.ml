let out_dir = ref "unitcon-out"

let print_callgraph = ref false

let target_program : string option ref = ref None

let basic_mode = ref false

let syn_priority = ref false

let sem_priority = ref false

let time_out = ref (5 * 60)

let until_time_out = ref false

let mock = ref []

let class_file = ref ""

let constant_type = ref ""

let constant = ref []

let options =
  [
    ( "-outdir",
      Arg.Set_string out_dir,
      "Output directory (default: unitcon-out)" );
    ("-print-callgraph", Arg.Set print_callgraph, "Print callgraph");
    ("-basic-mode", Arg.Set basic_mode, "Run basic mode (default: false)");
    ( "-syn-priority",
      Arg.Set syn_priority,
      "Run using syntactic priority only (default: false)" );
    ( "-sem-priority",
      Arg.Set sem_priority,
      "Run using semantic priority only (default: false)" );
    ("-time-out", Arg.Set_int time_out, "Time out (default: 30m)");
    ( "-until-time-out",
      Arg.Set until_time_out,
      "Synthesis until time out (default: false)" );
    ( "-mock",
      Arg.String (fun x -> mock := x :: !mock),
      "Using mock for test case generation" );
    ( "-class-file",
      Arg.Set_string class_file,
      "Using predefined class file for test case generation" );
    ( "-constant-type",
      Arg.Set_string constant_type,
      "Using type of predefined constant for test case generation. e.g., \
       String, Integer" );
    ( "-constant",
      Arg.String (fun x -> constant := x :: !constant),
      "Using predefined constant for test case generation" );
  ]

let parse_arg (x : string) =
  target_program := Some x;
  ()
