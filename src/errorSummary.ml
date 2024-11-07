open Language
module Json = Yojson.Safe
module JsonUtil = Yojson.Safe.Util

let add_use_field value_map field_set =
  Condition.M.fold
    (fun field _ field_set ->
      match field with
      | Condition.RH_Var id ->
          FieldSet.add { used_in_error = true; name = id } field_set
      | _ -> field_set)
    value_map field_set

(* map the fields used when executing the error method
   from the parameters of the error method into a set of fields. *)
let get_use_field pre_var pre_mem =
  Condition.M.fold
    (fun sym _ ufset ->
      match Condition.M.find_opt (get_next_symbol sym pre_mem) pre_mem with
      | Some value_map ->
          UseFieldMap.M.add sym (add_use_field value_map FieldSet.empty) ufset
      | _ -> ufset)
    pre_var UseFieldMap.M.empty

let parse_summary summary =
  let relation =
    JsonUtil.member "BoItv" summary |> JsonUtil.to_string |> Parser.parse_boitv
  in
  let pre_var =
    JsonUtil.member "Precond_Stack" summary
    |> JsonUtil.to_string |> Parser.parse_var
  in
  let pre_mem =
    JsonUtil.member "Precond_Heap" summary
    |> JsonUtil.to_string |> Parser.parse_mem
  in
  let value =
    JsonUtil.member "CItv" summary
    |> JsonUtil.to_string
    |> Parser.parse_citv true pre_mem
  in
  let post_var =
    JsonUtil.member "Postcond_Stack" summary
    |> JsonUtil.to_string |> Parser.parse_var
  in
  let post_mem =
    JsonUtil.member "Postcond_Heap" summary
    |> JsonUtil.to_string |> Parser.parse_mem
  in
  {
    relation;
    value;
    use_field = get_use_field pre_var pre_mem;
    precond = (pre_var, pre_mem);
    postcond = (post_var, post_mem);
    args = [];
  }

let get_method_name assoc =
  JsonUtil.member "Procname" assoc |> JsonUtil.to_string |> Parser.split_name

let get_file_name assoc = JsonUtil.member "Filename" assoc |> JsonUtil.to_string

let get_start_line assoc = JsonUtil.member "StartLine" assoc |> JsonUtil.to_int

let get_last_line assoc = JsonUtil.member "LastLine" assoc |> JsonUtil.to_int

let is_int str =
  match int_of_string_opt str with Some _ -> true | None -> false

let target_loc target =
  (* Not set target location *)
  if target = "" then ("", -1)
  else
    match String.split_on_char ':' target with
    | [ file; line ] when is_int line -> (file, int_of_string line)
    | _ -> failwith ("Invalid target location: " ^ target)

let is_target_error (t_file, t_line) assoc =
  let file_name = get_file_name assoc in
  let start_line = get_start_line assoc in
  let last_line = get_last_line assoc in
  if t_file = file_name && start_line <= t_line && t_line <= last_line then true
  else false

let find_error assoc =
  if !Cmdline.basic_mode then (get_method_name assoc, empty_summary)
  else (get_method_name assoc, parse_summary assoc)

let from_error_summary_json json =
  let target_loc = target_loc !Cmdline.target in
  let json = JsonUtil.to_list json in
  if json = [] then failwith "Error summaries file is empty. Unitcon exits."
  else if target_loc = ("", -1) then (
    Logger.info
      "Target location is not specified. Unitcon synthesizes test cases using \
       the first error summary";
    find_error (List.hd json))
  else
    List.fold_left
      (fun (found_error_m, found_error_s) assoc ->
        if found_error_m = "" && is_target_error target_loc assoc then
          find_error assoc
        else (found_error_m, found_error_s))
      ("", empty_summary) json
