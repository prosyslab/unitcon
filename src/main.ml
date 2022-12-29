module F = Format
module MethodMap = Language.MethodMap
module Method = Language.Method

let parse_method_list filename =
  let json = Yojson.Safe.from_file filename in
  Language.MethodMap.of_json json

let parse_callgraph filename =
  let json = Yojson.Safe.from_file filename in
  Callgraph.of_json json

let parse_summary filename method_map =
  let json = Yojson.Safe.from_file filename in
  let list = Yojson.Safe.Util.to_list json in
  Summary.from_json list method_map

let parse_error_summary filename target_method method_map =
  let json = Yojson.Safe.from_file filename in
  let list = Yojson.Safe.Util.to_list json in
  ErrorSummary.from_json list target_method method_map

let parse_trace filename method_map =
  let json = Yojson.Safe.from_file filename in
  Trace.from_json json method_map

let get_target_method filename method_map =
  let json = Yojson.Safe.from_file filename in
  Trace.target_method json method_map

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
  Cmdline.input_files := List.rev !Cmdline.input_files;
  initialize ();
  match !Cmdline.input_files with
  | [ method_list; summary_file; error_summary_file; trace_file ] ->
      let method_map = parse_method_list method_list in
      let trace = parse_trace trace_file method_map in
      let target_method = get_target_method trace_file method_map in
      let summary = parse_summary summary_file method_map in
      let call_graph = parse_callgraph summary_file in
      let error_summary =
        parse_error_summary error_summary_file target_method method_map
      in
      let precond, precond_obj =
        Calculation.calc_precond trace target_method summary error_summary
      in
      MakeTC.mk_testcase target_method call_graph summary method_map precond
        precond_obj
      |> print_endline;
      if !Cmdline.print_callgraph then print_callgraph call_graph
  | _ -> failwith "Invalid Inputs"

let _ = main ()
