module F = Format
module MethodMap = Language.MethodMap

let parse_json filename =
  let json = Yojson.Safe.from_file filename in
  let method_map = Yojson.Safe.Util.member "node" json |> MethodMap.of_json in
  let call_graph = Yojson.Safe.Util.member "edge" json |> Callgraph.of_json in
  (method_map, call_graph)

let parse_summary filename =
  let json = Yojson.Safe.from_file filename in
  let list = Yojson.Safe.Util.to_list json in
  Summary.from_json list

let parse_for_finding filename =
  let json = Yojson.Safe.from_file filename in
  let list = Yojson.Safe.Util.to_list json in
  Summary.making_methodmap list

let parse_trace filename =
  let json = Yojson.Safe.from_file filename in
  Trace.from_json json

let get_target_method filename =
  let json = Yojson.Safe.from_file filename in
  Trace.target_method json

let print_callgraph call_graph =
  let oc = open_out (Filename.concat !Cmdline.out_dir "callgraph.dot") in
  Callgraph.Graphviz.output_graph oc call_graph

let print_summary summary = ()

let initialize () =
  (try Unix.mkdir !Cmdline.out_dir 0o775
   with Unix.Unix_error (Unix.EEXIST, _, _) -> ());
  print_endline ("Logging to " ^ !Cmdline.out_dir);
  Filename.concat !Cmdline.out_dir "log.txt" |> Logger.from_file

let synthesize method_map call_graph =
  (* generate Spoon class here *)
  ()

let main () =
  let usage = "Usage: unitgen [options] input_files" in
  Arg.parse Cmdline.options Cmdline.parse_arg usage;
  initialize ();
  (*
  let method_map, call_graph =
    parse_json (!Cmdline.input_files |> List.tl |> List.hd)
  in
  *)
  let trace = parse_trace (!Cmdline.input_files |> List.tl |> List.hd) in
  let target_method =
    get_target_method (!Cmdline.input_files |> List.tl |> List.hd)
  in
  let summary = parse_summary (!Cmdline.input_files |> List.hd) in
  let for_finding = parse_for_finding (!Cmdline.input_files |> List.hd) in
  (*if !Cmdline.print_callgraph then print_callgraph call_graph;*)
  let precond = Calculation.calc_precond trace summary for_finding in
  MakeTC.mk_testcase target_method summary precond |> print_endline;
  if !Cmdline.parse_summary then print_summary summary

let _ = main ()
