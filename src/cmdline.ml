let out_dir = ref "unitgen-out"

let print_callgraph = ref false

let options =
  [
    ( "-outdir",
      Arg.Set_string out_dir,
      "Output directory (default: unitgen-out)" );
    ("-print-callgraph", Arg.Set print_callgraph, "Print callgraph");
  ]

let input_file = ref ""

let parse_arg x = input_file := x
