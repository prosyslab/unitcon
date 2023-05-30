module Json = Yojson.Safe
module JsonUtil = Yojson.Safe.Util

type call_prop = {
  caller : string;
  callee : string;
  boitv : string;
  citv : string;
  precond : string;
  postcond : string;
  arg : string list;
}

type err_prop = {
  method_name : string;
  boitv : string;
  citv : string;
  precond : string;
  postcond : string;
}

let empty_call_prop =
  {
    caller = "";
    callee = "";
    boitv = "";
    citv = "";
    precond = "";
    postcond = "";
    arg = [];
  }

let empty_err_prop =
  { method_name = ""; boitv = ""; citv = ""; precond = ""; postcond = "" }

let is_start = ref false

let is_boitv = ref false

let is_citv = ref false

let is_precond = ref false

let is_postcond = ref false

let call_prop_list = ref []

let err_prop_list = ref []

let output name data =
  let dirname = !Cmdline.out_dir ^ "/marshal" in
  if not (Sys.file_exists dirname) then Unix.mkdir dirname 0o755;
  let chan = open_out (dirname ^ "/" ^ name ^ ".json") in
  Marshal.to_channel chan data [];
  close_out chan

let input name =
  let dirname = !Cmdline.out_dir ^ "/marshal" in
  if not (Sys.file_exists dirname) then failwith (dirname ^ " not found");
  let chan = open_in (dirname ^ "/" ^ name) in
  let data = Marshal.from_channel chan in
  close_in chan;
  data

let caller_call_prop str prop =
  let name = String.split_on_char ':' str |> List.tl |> List.hd in
  {
    caller = name |> Regexp.rm_space;
    callee = prop.callee;
    boitv = prop.boitv;
    citv = prop.citv;
    precond = prop.precond;
    postcond = prop.postcond;
    arg = prop.arg;
  }

let callee_call_prop str prop =
  let name = String.split_on_char ':' str |> List.tl |> List.hd in
  {
    caller = prop.caller;
    callee = name |> Regexp.rm_space;
    boitv = prop.boitv;
    citv = prop.citv;
    precond = prop.precond;
    postcond = prop.postcond;
    arg = prop.arg;
  }

let boitv_call_prop str prop =
  let lst = String.split_on_char ':' str |> List.tl in
  let boitv =
    if List.hd lst |> Regexp.rm_space = "BoItv" then
      List.tl lst |> List.hd |> Regexp.rm_space
    else List.hd lst |> Regexp.rm_space
  in
  {
    caller = prop.caller;
    callee = prop.callee;
    boitv;
    citv = prop.citv;
    precond = prop.precond;
    postcond = prop.postcond;
    arg = prop.arg;
  }

let citv_call_prop str prop =
  let citv = String.split_on_char ':' str |> List.tl |> List.hd in
  {
    caller = prop.caller;
    callee = prop.callee;
    boitv = prop.boitv;
    citv = citv |> Regexp.rm_space;
    precond = prop.precond;
    postcond = prop.postcond;
    arg = prop.arg;
  }

let pre_call_prop str prop =
  let pre = String.split_on_char ':' str |> List.tl |> List.hd in
  {
    caller = prop.caller;
    callee = prop.callee;
    boitv = prop.boitv;
    citv = prop.citv;
    precond = pre |> Regexp.rm_space;
    postcond = prop.postcond;
    arg = prop.arg;
  }

let post_call_prop str prop =
  let post = String.split_on_char ':' str |> List.tl |> List.hd in
  {
    caller = prop.caller;
    callee = prop.callee;
    boitv = prop.boitv;
    citv = prop.citv;
    precond = prop.precond;
    postcond = post |> Regexp.rm_space;
    arg = prop.arg;
  }

let arg_call_prop str prop =
  let args =
    String.split_on_char ':' str |> List.tl |> List.hd |> Regexp.rm_space
  in
  let arg_list = Str.split (Str.regexp "  ") args in
  let arg_list = List.map Regexp.rm_space arg_list in
  {
    caller = prop.caller;
    callee = prop.callee;
    boitv = prop.boitv;
    citv = prop.citv;
    precond = prop.precond;
    postcond = prop.postcond;
    arg = arg_list;
  }

let append_boitv_call_prop str prop =
  let next_boitv = Regexp.rm_space str in
  {
    caller = prop.caller;
    callee = prop.callee;
    boitv = prop.boitv ^ next_boitv;
    citv = prop.citv;
    precond = prop.precond;
    postcond = prop.postcond;
    arg = prop.arg;
  }

let append_citv_call_prop str prop =
  let next_citv = Regexp.rm_space str in
  {
    caller = prop.caller;
    callee = prop.callee;
    boitv = prop.boitv;
    citv = prop.citv ^ next_citv;
    precond = prop.precond;
    postcond = prop.postcond;
    arg = prop.arg;
  }

let append_pre_call_prop str prop =
  let next_precond = Regexp.rm_space str in
  {
    caller = prop.caller;
    callee = prop.callee;
    boitv = prop.boitv;
    citv = prop.citv;
    precond = prop.precond ^ next_precond;
    postcond = prop.postcond;
    arg = prop.arg;
  }

let append_post_call_prop str prop =
  let next_postcond = Regexp.rm_space str in
  {
    caller = prop.caller;
    callee = prop.callee;
    boitv = prop.boitv;
    citv = prop.citv;
    precond = prop.precond;
    postcond = prop.postcond ^ next_postcond;
    arg = prop.arg;
  }

let method_name_err_prop str prop =
  let name = String.split_on_char ':' str |> List.rev |> List.hd in
  {
    method_name = name |> Regexp.rm_space;
    boitv = prop.boitv;
    citv = prop.citv;
    precond = prop.precond;
    postcond = prop.postcond;
  }

let boitv_err_prop str prop =
  let boitv = String.split_on_char ':' str |> List.rev |> List.hd in
  {
    method_name = prop.method_name;
    boitv = boitv |> Regexp.rm_space;
    citv = prop.citv;
    precond = prop.precond;
    postcond = prop.postcond;
  }

let citv_err_prop str prop =
  let citv = String.split_on_char ':' str |> List.rev |> List.hd in
  {
    method_name = prop.method_name;
    boitv = prop.boitv;
    citv = citv |> Regexp.rm_space;
    precond = prop.precond;
    postcond = prop.postcond;
  }

let pre_err_prop str prop =
  let pre = String.split_on_char ':' str |> List.rev |> List.hd in
  {
    method_name = prop.method_name;
    boitv = prop.boitv;
    citv = prop.citv;
    precond = pre |> Regexp.rm_space;
    postcond = prop.postcond;
  }

let post_err_prop str prop =
  let post = String.split_on_char ':' str |> List.rev |> List.hd in
  {
    method_name = prop.method_name;
    boitv = prop.boitv;
    citv = prop.citv;
    precond = prop.precond;
    postcond = post |> Regexp.rm_space;
  }

let append_boitv_err_prop str prop =
  let next_boitv = Regexp.rm_space str in
  {
    method_name = prop.method_name;
    boitv = prop.boitv ^ next_boitv;
    citv = prop.citv;
    precond = prop.precond;
    postcond = prop.postcond;
  }

let append_citv_err_prop str prop =
  let next_citv = Regexp.rm_space str in
  {
    method_name = prop.method_name;
    boitv = prop.boitv;
    citv = prop.citv ^ next_citv;
    precond = prop.precond;
    postcond = prop.postcond;
  }

let append_pre_err_prop str prop =
  let next_precond = Regexp.rm_space str in
  {
    method_name = prop.method_name;
    boitv = prop.boitv;
    citv = prop.citv;
    precond = prop.precond ^ next_precond;
    postcond = prop.postcond;
  }

let append_post_err_prop str prop =
  let next_postcond = Regexp.rm_space str in
  {
    method_name = prop.method_name;
    boitv = prop.boitv;
    citv = prop.citv;
    precond = prop.precond;
    postcond = prop.postcond ^ next_postcond;
  }

let rec parse_call_prop_dict data call_prop =
  match input_line data with
  | s ->
      let str = s |> Regexp.rm_space in
      if str = "{start" then (
        is_start := true;
        parse_call_prop_dict data empty_call_prop)
      else if str = "end}" then (
        is_start := false;
        is_boitv := false;
        is_citv := false;
        is_precond := false;
        is_postcond := false;
        call_prop_list := call_prop :: !call_prop_list)
      else if Str.string_match (Str.regexp "caller:") str 0 then
        parse_call_prop_dict data (caller_call_prop str call_prop)
      else if Str.string_match (Str.regexp "callee:") str 0 then
        parse_call_prop_dict data (callee_call_prop str call_prop)
      else if Str.string_match (Str.regexp "^.*BoItv:") str 0 then (
        is_boitv := true;
        parse_call_prop_dict data (boitv_call_prop str call_prop))
      else if Str.string_match (Str.regexp "^.*CItv:") str 0 then (
        is_citv := true;
        is_boitv := false;
        parse_call_prop_dict data (citv_call_prop str call_prop))
      else if Str.string_match (Str.regexp "^.*Precond:") str 0 then (
        is_precond := true;
        is_citv := false;
        parse_call_prop_dict data (pre_call_prop str call_prop))
      else if Str.string_match (Str.regexp "^.*Postcond:") str 0 then (
        is_postcond := true;
        is_precond := false;
        parse_call_prop_dict data (post_call_prop str call_prop))
      else if Str.string_match (Str.regexp "^.*actual:") str 0 then
        parse_call_prop_dict data (arg_call_prop str call_prop)
      else if !is_boitv then
        parse_call_prop_dict data (append_boitv_call_prop str call_prop)
      else if !is_citv then
        parse_call_prop_dict data (append_citv_call_prop str call_prop)
      else if !is_precond then
        parse_call_prop_dict data (append_pre_call_prop str call_prop)
      else if !is_postcond then
        parse_call_prop_dict data (append_post_call_prop str call_prop)
      else parse_call_prop_dict data call_prop
  | exception End_of_file -> raise End_of_file

let rec parse_err_prop_dict data err_prop =
  match input_line data with
  | s ->
      let str = s |> Regexp.rm_space in
      if str = "{start" then (
        is_start := true;
        parse_err_prop_dict data empty_err_prop)
      else if str = "end}" then (
        is_start := false;
        is_boitv := false;
        is_citv := false;
        is_precond := false;
        is_postcond := false;
        err_prop_list := err_prop :: !err_prop_list)
      else if Str.string_match (Str.regexp "^.*procname:") str 0 then
        parse_err_prop_dict data (method_name_err_prop str err_prop)
      else if Str.string_match (Str.regexp "^.*BoItv:") str 0 then (
        is_boitv := true;
        parse_err_prop_dict data (boitv_err_prop str err_prop))
      else if Str.string_match (Str.regexp "^.*CItv:") str 0 then (
        is_citv := true;
        is_boitv := false;
        parse_err_prop_dict data (citv_err_prop str err_prop))
      else if Str.string_match (Str.regexp "^.*Precond:") str 0 then (
        is_precond := true;
        is_citv := false;
        parse_err_prop_dict data (pre_err_prop str err_prop))
      else if Str.string_match (Str.regexp "^.*Postcond:") str 0 then (
        is_postcond := true;
        is_precond := false;
        parse_err_prop_dict data (post_err_prop str err_prop))
      else if !is_boitv then
        parse_err_prop_dict data (append_boitv_err_prop str err_prop)
      else if !is_citv then
        parse_err_prop_dict data (append_citv_err_prop str err_prop)
      else if !is_precond then
        parse_err_prop_dict data (append_pre_err_prop str err_prop)
      else if !is_postcond then
        parse_err_prop_dict data (append_post_err_prop str err_prop)
      else parse_err_prop_dict data err_prop
  | exception End_of_file -> raise End_of_file

let rec parse_call_prop_dict_all data =
  match parse_call_prop_dict data empty_call_prop with
  | exception End_of_file -> ()
  | _ -> parse_call_prop_dict_all data

let rec parse_err_prop_dict_all data =
  match parse_err_prop_dict data empty_err_prop with
  | exception End_of_file -> ()
  | _ -> parse_err_prop_dict_all data

let to_call_prop_json data =
  let mk_assoc elem =
    `Assoc
      [
        ("Caller", `String elem.caller);
        ("Callee", `String elem.callee);
        ("BoItv", `String elem.boitv);
        ("CItv", `String elem.citv);
        ("Precond", `String elem.precond);
        ("Postcond", `String elem.postcond);
        ("Arg", `List (List.map (fun x -> `String x) elem.arg));
      ]
  in
  parse_call_prop_dict_all data;
  let json = `List (List.map (fun elem -> mk_assoc elem) !call_prop_list) in
  json

let to_err_prop_json data =
  let mk_assoc elem =
    `Assoc
      [
        ("method", `String elem.method_name);
        ("BoItv", `String elem.boitv);
        ("CItv", `String elem.citv);
        ("Precond", `String elem.precond);
        ("Postcond", `String elem.postcond);
      ]
  in
  parse_err_prop_dict_all data;
  let json = `List (List.map (fun elem -> mk_assoc elem) !err_prop_list) in
  json

let parse_callprop filename =
  let name = Str.split (Str.regexp "/") filename |> List.rev |> List.hd in
  let data = open_in filename in
  is_start := false;
  is_boitv := false;
  is_citv := false;
  is_precond := false;
  is_postcond := false;
  let json = to_call_prop_json data in
  output name json

let parse_errprop filename =
  let name = Str.split (Str.regexp "/") filename |> List.rev |> List.hd in
  let data = open_in filename in
  is_start := false;
  is_boitv := false;
  is_citv := false;
  is_precond := false;
  is_postcond := false;
  let json = to_err_prop_json data in
  output name json
