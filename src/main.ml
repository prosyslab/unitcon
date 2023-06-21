module F = Format
module Json = Yojson.Safe
module JsonUtil = Yojson.Safe.Util

let output name data =
  let dirname = !Cmdline.out_dir ^ "/marshal" in
  if not (Sys.file_exists dirname) then Unix.mkdir dirname 0o755;
  let chan = open_out (dirname ^ "/" ^ name) in
  Marshal.to_channel chan data [];
  close_out chan

let input name =
  let dirname = !Cmdline.out_dir ^ "/marshal" in
  if not (Sys.file_exists dirname) then failwith (dirname ^ " not found");
  let chan = open_in (dirname ^ "/" ^ name) in
  let data = Marshal.from_channel chan in
  close_in chan;
  data

let get_filename filename =
  Str.split (Str.regexp "/") filename |> List.rev |> List.hd

let parse_callgraph filename =
  let filename = get_filename filename in
  let data = input filename in
  Callgraph.of_json data

let parse_class_info filename =
  let json = Json.from_file filename in
  let elem = JsonUtil.to_list json |> List.hd in
  Hierarchy.of_json elem

let parse_summary filename =
  let json = Json.from_file filename in
  let filename = get_filename filename in
  output filename json;
  let data = input filename in
  Summary.from_summary_json data

let parse_method_info filename =
  let filename = get_filename filename in
  let data = input filename in
  Summary.from_method_json data

let parse_error_summary filename =
  Parser.parse_errprop filename;
  let filename = get_filename filename in
  let data = input (filename ^ ".json") in
  ErrorSummary.from_error_summary_json data

let parse_callprop filename =
  Parser.parse_callprop filename;
  let filename = get_filename filename in
  let data = input (filename ^ ".json") in
  CallProposition.from_callprop_json data

let get_setter summary = Setter.from_summary_map summary

let print_callgraph callgraph =
  let oc = open_out (Filename.concat !Cmdline.out_dir "callgraph.dot") in
  Callgraph.Graphviz.output_graph oc callgraph

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
      let summary = parse_summary summary_file in
      let method_info = parse_method_info summary_file in
      let setter_map = get_setter summary in
      let call_prop_map = parse_callprop call_proposition_file in
      let callgraph = parse_callgraph summary_file in
      let class_info = parse_class_info hierarchy_file in
      let error_summary_map = parse_error_summary error_summary_file in
      Language.SummaryMap.M.iter
        (fun source_method error_summary ->
          MakeTC.mk_testcases source_method error_summary callgraph summary
            call_prop_map method_info class_info setter_map
          |> print_endline)
        error_summary_map
      (* if !Cmdline.print_callgraph then print_callgraph callgraph *)
  | _ -> failwith "Invalid Inputs"

let _ =
  Printexc.record_backtrace true;
  main ()
