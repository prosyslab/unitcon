module F = Format
module Json = Yojson.Safe
module JsonUtil = Yojson.Safe.Util

let parse_callgraph filename =
  let json = Json.from_file filename in
  Callgraph.of_json json

let parse_class_info filename =
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

let parse_error_summary filename =
  let json = Json.from_file filename in
  let list = JsonUtil.to_list json in
  ErrorSummary.from_error_summary_json list

let parse_callprop filename =
  let json = Json.from_file filename in
  let list = JsonUtil.to_list json in
  CallProposition.from_callprop_json list

let get_setter summary = Setter.from_summary_map summary

let print_callgraph call_graph =
  let oc = open_out (Filename.concat !Cmdline.out_dir "callgraph.dot") in
  Callgraph.Graphviz.output_graph oc call_graph

let initialize () =
  (try Unix.mkdir !Cmdline.out_dir 0o775
   with Unix.Unix_error (Unix.EEXIST, _, _) -> ());
  print_endline ("Logging to " ^ !Cmdline.out_dir)
(* Filename.concat !Cmdline.out_dir "log.txt" |> Logger.from_file *)

let main () =
  let usage = "Usage: unitgen [options] input_files" in
  Arg.parse Cmdline.options Cmdline.parse_arg usage;
  Cmdline.input_files := List.rev !Cmdline.input_files;
  initialize ();
  match !Cmdline.input_files with
  | [ summary_file; error_summary_file; call_proposition_file; hierarchy_file ]
    ->
      let method_info = parse_method_info summary_file in
      let summary = parse_summary summary_file in
      let setter_map = get_setter summary in
      let call_prop_map = parse_callprop call_proposition_file in
      let call_graph = parse_callgraph summary_file in
      let class_info = parse_class_info hierarchy_file in
      let error_summary_map = parse_error_summary error_summary_file in
      Language.SummaryMap.M.iter
        (fun source_method error_summary ->
          MakeTC.mk_testcases source_method error_summary call_graph summary
            call_prop_map method_info class_info setter_map
          |> print_endline)
        error_summary_map
      (* if !Cmdline.print_callgraph then print_callgraph call_graph *)
  | _ -> failwith "Invalid Inputs"

let _ =
  Printexc.record_backtrace true;
  main ()
