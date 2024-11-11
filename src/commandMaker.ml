open Utils

let manifest_file out_dir = Filename.(out_dir / "Manifest")

let dep_files out_dir = Filename.(out_dir / "jar-files")

let dependency_jar out_dir = Filename.(out_dir / "with-dependency.jar")

let flush_buffer_from ic =
  match Unix.select [ Unix.descr_of_in_channel ic ] [] [] 1.0 with
  | [], _, _ -> ""
  | fd :: _, _, _ -> read_all_string (Unix.in_channel_of_descr fd)

let execute_command command =
  let close_channel (stdout, stdin, stderr) =
    close_out stdin;
    (stdout, stderr)
  in
  let execute command =
    let stdout, stdin, stderr =
      Unix.open_process_full command (Unix.environment ())
    in
    flush_buffer_from stdout |> ignore;
    flush_buffer_from stderr |> ignore;
    let pid = Unix.process_full_pid (stdout, stdin, stderr) in
    (try Unix.waitpid [ Unix.WUNTRACED ] pid |> ignore with _ -> ());
    close_channel (stdout, stdin, stderr)
  in
  execute command

let simple_compiler program_dir command =
  let current_dir = Unix.getcwd () in
  Sys.chdir program_dir;
  let ic_out, ic_err = execute_command command in
  Sys.chdir current_dir;
  close_in ic_out;
  close_in ic_err

let chop_prefix prefix str =
  let prefix_len = String.length prefix in
  let str_len = String.length str in
  if str_len < prefix_len then str
  else if String.sub str 0 prefix_len = prefix then
    String.sub str prefix_len (str_len - prefix_len)
  else str

(* Relative path should be used instead of absolute path *)
let rec collect_classpaths ?(prefix = "") dir =
  if Sys.is_directory dir then
    Array.fold_left
      (fun acc file ->
        let abspath = Filename.(dir / file) |> Filename.resolve in
        if Sys.is_directory abspath then
          List.rev_append (collect_classpaths ~prefix abspath) acc
        else if
          List.mem (Filename.extension file) [ ".jar"; ".class"; ".properties" ]
        then
          let relpath = chop_prefix prefix abspath in
          relpath :: acc
        else acc)
      [] (Sys.readdir dir)
  else []

let write_manifest_file oc paths =
  output_string oc "Class-Path: ";
  let rec write paths =
    match paths with
    | p :: tl when tl = [] ->
        output_string oc (p ^ "\n");
        write tl
    | p :: tl ->
        output_string oc (p ^ "\n  ");
        write tl
    | _ -> flush oc
  in
  write paths

let write_dep_files oc paths =
  let rec write paths =
    match paths with
    | p :: tl ->
        output_string oc (p ^ "\n");
        write tl
    | _ -> flush oc
  in
  write paths

let make_jar_with_dependencies p =
  let m_file = manifest_file !Cmdline.out_dir in
  let jar_files = dep_files !Cmdline.out_dir in
  let dep_jar = dependency_jar !Cmdline.out_dir in
  let manifest_oc = open_out m_file in
  let jar_files_oc = open_out jar_files in
  let abspaths = collect_classpaths ~prefix:(p ^ Filename.dir_sep) p in
  write_manifest_file manifest_oc abspaths;
  write_dep_files jar_files_oc abspaths;
  close_out manifest_oc;
  close_out jar_files_oc;
  simple_compiler p ("jar -cmf " ^ m_file ^ " " ^ dep_jar ^ " @" ^ jar_files)

let execute_build_cmd p =
  let build_cmd_file = Filename.(Filename.(p / input_path) / "build-command") in
  let ic = open_in build_cmd_file in
  let cmds = read_all_string ic |> Str.split (Str.regexp "\n") in
  close_in ic;
  let rec execute cmds =
    match cmds with
    | c :: tl ->
        simple_compiler p c;
        execute tl
    | _ -> ()
  in
  execute cmds

let run p =
  execute_build_cmd p;
  make_jar_with_dependencies p
