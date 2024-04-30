let out_dir = ref "unitcon-out"

let target_program : string option ref = ref None

let basic_mode = ref false

let pruning_mode = ref false

let priority_mode = ref false

let time_out = ref (5 * 60) (* max synthesis time *)

let max_run_time = ref (20 * 60) (* max running time except synthesis time *)

let unknown_bug = ref false

let mock = ref false

let options =
  [
    ( "-outdir",
      Arg.Set_string out_dir,
      "Output directory (default: unitcon-out)" );
    ( "-basic-mode",
      Arg.Set basic_mode,
      "Run without optimization (default: false)" );
    ( "-pruning-mode",
      Arg.Set pruning_mode,
      "Run with only pruning (default: false)" );
    ( "-priority-mode",
      Arg.Set priority_mode,
      "Run with only prioritization (default: false)" );
    ( "-time-out",
      Arg.Set_int time_out,
      "Time Budget except Static Analysis (default: 5m)" );
    ( "-unknown-bug",
      Arg.Set unknown_bug,
      "Run unknown bug searching mode (default: false)" );
    ( "-mock",
      Arg.Set mock,
      "Use mock (default: false)" );
  ]

let parse_arg (x : string) =
  target_program := Some x;
  ()
