module F = Format
module Json = Yojson.Safe
module JsonUtil = Yojson.Safe.Util

let parse_callgraph filename =
  let json = Json.from_file filename in
  Callgraph.of_json json

let parse_hierarchy filename =
  let json = Json.from_file filename in
  let elem = JsonUtil.to_list json |> List.hd in
  Hierarchy.of_json elem

let parse_summary filename =
  let json = Json.from_file filename in
  let list = JsonUtil.to_list json in
  Summary.from_summary_json list

let parse_method_info filename =
  let json = Json.from_file filename in
  let list = JsonUtil.to_list json in
  Summary.from_method_json list

let parse_error_summary source_method filename =
  let json = Json.from_file filename in
  let list = JsonUtil.to_list json in
  ErrorSummary.from_error_summary_json source_method list

let parse_callprop filename =
  let json = Json.from_file filename in
  let list = JsonUtil.to_list json in
  CallProposition.from_callprop_json list

let get_source_method filename =
  let json = Yojson.Safe.from_file filename in
  ErrorSummary.source_method json

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
  | [ summary_file; error_summary_file; call_proposition_file; hierarchy_file ]
    ->
      let source_method = get_source_method error_summary_file in
      let method_info = parse_method_info summary_file in
      let summary = parse_summary summary_file in
      let call_prop_map = parse_callprop call_proposition_file in
      let call_graph = parse_callgraph summary_file in
      let hierarchy_graph = parse_hierarchy hierarchy_file in
      let error_summary =
        parse_error_summary source_method error_summary_file
        |> Language.SummaryMap.M.find source_method
      in
      MakeTC.mk_testcases source_method error_summary call_graph summary
        call_prop_map method_info hierarchy_graph
      |> print_endline;
      if !Cmdline.print_callgraph then print_callgraph call_graph
  | _ -> failwith "Invalid Inputs"

let _ =
  Printexc.record_backtrace true;
  main ()
