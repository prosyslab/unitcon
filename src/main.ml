module F = Format
module MethodMap = Language.MethodMap

let parse_json filename =
  let json = Yojson.Safe.from_file filename in
  (* let method_map = Yojson.Safe.Util.member "method" json |> MethodMap.of_json in *)
  let call_graph = Callgraph.of_json json in
  (* (method_map, call_graph) *)
  ((), call_graph)

let parse_summary filename =
  let json = Yojson.Safe.from_file filename in
  let list = Yojson.Safe.Util.to_list json in
  Summary.from_json list

let parse_error_summary filename target_method =
  let json = Yojson.Safe.from_file filename in
  let list = Yojson.Safe.Util.to_list json in
  ErrorSummary.from_json list target_method

let parse_trace filename =
  let json = Yojson.Safe.from_file filename in
  Trace.from_json json

let get_target_method filename =
  let json = Yojson.Safe.from_file filename in
  Trace.target_method json

let print_callgraph call_graph =
  let oc = open_out (Filename.concat !Cmdline.out_dir "callgraph.dot") in
  Callgraph.Graphviz.output_graph oc call_graph

let initialize () =
  (try Unix.mkdir !Cmdline.out_dir 0o775
   with Unix.Unix_error (Unix.EEXIST, _, _) -> ());
  print_endline ("Logging to " ^ !Cmdline.out_dir)
(* Filename.concat !Cmdline.out_dir "log.txt" |> Logger.from_file *)

let synthesize method_map call_graph =
  (* generate Spoon class here *)
  ()

let main () =
  let usage = "Usage: unitgen [options] input_files" in
  Arg.parse Cmdline.options Cmdline.parse_arg usage;
  initialize ();
  match !Cmdline.input_files with
  | [ summary_file; error_summary_file; trace_file ] ->
      let trace = parse_trace trace_file in
      let target_method = get_target_method trace_file in
      let summary = parse_summary summary_file in
      let method_map, call_graph = parse_json summary_file in
      let error_summary =
        parse_error_summary error_summary_file target_method
      in
      let precond, precond_obj =
        Calculation.calc_precond trace target_method summary error_summary
      in
      MakeTC.mk_testcase target_method summary precond precond_obj
      |> print_endline;
      if !Cmdline.print_callgraph then print_callgraph call_graph
  | _ -> failwith "Invalid Inputs"

let _ = main ()
