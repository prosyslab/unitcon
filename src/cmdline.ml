let out_dir = ref "unitcon-out"

let target_program : string option ref = ref None

let basic_mode = ref false

let pruning_mode = ref false

let priority_mode = ref false

let time_out = ref (10 * 60) (* total running time *)

let unknown_bug = ref false

let mock = ref false

let extension = ref ""

let with_loop = ref true

let with_fuzz = ref false

let class_info = ref false

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
      "Time Budget except Static Analysis (default: 20m)" );
    ( "-unknown-bug",
      Arg.Set unknown_bug,
      "Run unknown bug searching mode (default: false)" );
    ("-mock", Arg.Set mock, "Use mock (default: false)");
    ( "-modifier-extension",
      Arg.Set_string extension,
      "Extend the available modifiers from public to package (default: \"\", \
       e.g., \"com.a.b.c\")" );
    ( "-with-loop",
      Arg.Set with_loop,
      "Execute multiple test cases using loop at once (default: true)" );
    ( "-with-fuzz",
      Arg.Set with_fuzz,
      "Use fuzzer for searching constant (default: false)" );
    ( "-class-info",
      Arg.Set class_info,
      "Analyze syntactic properties of a given Java bytecode file" );
  ]

let parse_arg (x : string) =
  target_program := Some x;
  ()
