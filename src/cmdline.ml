let out_dir = ref "unitcon-out"

let print_callgraph = ref false

let target_program : string option ref = ref None

let basic_mode = ref false

let syn_priority = ref false

let time_out = ref (3 * 60) (* max synthesis time *)

let max_run_time = ref (60 * 60) (* max running time except synthesis time *)

let until_time_out = ref false

let unknown_bug = ref false

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
    ("-time-out", Arg.Set_int time_out, "Time out (default: 5m)");
    ( "-until-time-out",
      Arg.Set until_time_out,
      "Synthesis until time out (default: false)" );
    ( "-unknown-bug",
      Arg.Set unknown_bug,
      "Run unknown bug searching mode (default: false)" );
  ]

let parse_arg (x : string) =
  target_program := Some x;
  ()
