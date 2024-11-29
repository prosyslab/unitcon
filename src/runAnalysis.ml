open Utils

type analyzer_run_type =
  | Capture of (string * string)
  | Analyze of (string * string * (string * int))
  | Summary of (string * string)
  | Normal

let run_type_to_str = function
  | Capture _ -> "Capture"
  | Analyze _ -> "Analyze"
  | Summary _ -> "Summary"
  | Normal -> "Normal"

let is_int str =
  match int_of_string_opt str with Some _ -> true | None -> false

let target_loc target =
  (* Not set target location *)
  if target = "" then ("", -1)
  else
    match String.split_on_char ':' target with
    | [ file; line ] when is_int line -> (file, int_of_string line)
    | _ -> failwith ("Invalid target location: " ^ target)

let execute_command run_type command =
  match run_type with
  | Capture (infer_bin, out_dir) ->
      let set_out_dir = "--results-dir " ^ out_dir in
      let no_pb = "--no-progress-bar" in
      let command =
        infer_bin ^ " capture " ^ set_out_dir ^ " " ^ no_pb ^ " -- " ^ command
      in
      L.info "Capturing step!";
      execute command
  | Analyze (infer_bin, out_dir, (t_file, t_line)) ->
      let set_out_dir = "--results-dir " ^ out_dir in
      let no_pb = "--no-progress-bar" in
      let set_target_file =
        if t_file = "" then "" else "--target-file-name " ^ "\"" ^ t_file ^ "\""
      in
      let set_target_line =
        if t_line = -1 then "" else "--target-file-line " ^ string_of_int t_line
      in
      let keep_going = if !Cmdline.keep_going then " --keep-going " else "" in
      let interproc = if !Cmdline.interproc then " --interproc " else "" in
      let skip_procedures =
        if !Cmdline.skip_procedures <> "" then
          " --pulse-skip-procedures " ^ !Cmdline.skip_procedures
        else ""
      in
      let command =
        infer_bin ^ " analyze " ^ set_out_dir ^ " " ^ no_pb
        ^ " --pulse-only --show-latent " ^ set_target_file ^ " "
        ^ set_target_line ^ keep_going ^ interproc ^ skip_procedures
      in
      L.info "Analyzing step!";
      execute command
  | Summary (infer_bin, out_dir) ->
      let set_out_dir = "--results-dir " ^ out_dir in
      let command =
        infer_bin ^ " debug " ^ set_out_dir
        ^ " --procedures --procedures-summary-json"
      in
      L.info "Extracting step!";
      execute command
  | Normal -> execute command

let simple_compiler program_dir run_type command =
  let current_dir = Unix.getcwd () in
  Sys.chdir program_dir;
  let ret = execute_command run_type command in
  Sys.chdir current_dir;
  if ret <> 0 then
    failwith ("Failed to " ^ run_type_to_str run_type ^ " Step ...")

let execute_build_cmd p infer_bin out_dir =
  let build_cmd_file = Filename.(Filename.(p / input_path) / "build-command") in
  let ic = open_in build_cmd_file in
  let cmds = read_all_string ic |> Str.split (Str.regexp "\n") in
  close_in ic;
  let rec execute cmds =
    match cmds with
    | c :: tl ->
        if String.starts_with ~prefix:"mvn clean" c then (
          simple_compiler p (Capture (infer_bin, out_dir)) c;
          execute tl)
        else if String.starts_with ~prefix:"javac" c then (
          simple_compiler p (Capture (infer_bin, out_dir)) c;
          execute tl)
        else (
          simple_compiler p Normal c;
          execute tl)
    | _ -> ()
  in
  execute cmds

let execute_analyze_cmd p infer_bin out_dir target =
  simple_compiler p (Analyze (infer_bin, out_dir, target_loc target)) ""

let execute_summary_cmd p infer_bin out_dir =
  simple_compiler p (Summary (infer_bin, out_dir)) ""

let run p out_dir =
  let infer_bin =
    Filename.concat Utils.unitcon_path "unitcon-infer/infer/bin/infer"
  in
  let infer_out_dir = Filename.(out_dir / "infer-out") in
  execute_build_cmd p infer_bin infer_out_dir;
  execute_analyze_cmd p infer_bin infer_out_dir !Cmdline.target;
  execute_summary_cmd p infer_bin infer_out_dir
