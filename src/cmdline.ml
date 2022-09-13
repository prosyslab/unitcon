let out_dir = ref "unitgen-out"

let print_callgraph = ref false

let parse_summary = ref false

let options =
  [
    ( "-outdir",
      Arg.Set_string out_dir,
      "Output directory (default: unitgen-out)" );
    ("-print-callgraph", Arg.Set print_callgraph, "Print callgraph");
    ("-parse-summary", Arg.Set parse_summary, "Parse summary");
  ]

let input_files = ref []

let parse_arg (x : string) = input_files := x :: !input_files
