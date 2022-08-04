module F = Format
module MethodMap = Language.MethodMap

let parse_json filename =
  let json = Yojson.Safe.from_file filename in
  let method_map = Yojson.Safe.Util.member "node" json |> MethodMap.of_json in
  let call_graph = Yojson.Safe.Util.member "edge" json |> Callgraph.of_json in
  (method_map, call_graph)

let print_callgraph call_graph =
  let oc = open_out (Filename.concat !Cmdline.out_dir "callgraph.dot") in
  Callgraph.Graphviz.output_graph oc call_graph

let initialize () =
  (try Unix.mkdir !Cmdline.out_dir 0o775
   with Unix.Unix_error (Unix.EEXIST, _, _) -> ());
  print_endline ("Logging to " ^ !Cmdline.out_dir);
  Filename.concat !Cmdline.out_dir "log.txt" |> Logger.from_file

let synthesize method_map call_graph =
  (* generate Spoon class here *)
  ()

let main () =
  let usage = "Usage: unitgen [options] input" in
  Arg.parse Cmdline.options Cmdline.parse_arg usage;
  initialize ();
  let method_map, call_graph = parse_json !Cmdline.input_file in
  if !Cmdline.print_callgraph then print_callgraph call_graph;
  synthesize method_map call_graph

let _ = main ()
