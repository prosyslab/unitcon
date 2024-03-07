open Language
module Json = Yojson.Safe
module JsonUtil = Yojson.Safe.Util

(* calculate memory effect for method *)
let contains_symbol symbol memory =
  let inner_contains_symbol mem =
    Condition.M.fold
      (fun _ hd check -> if hd = symbol then true else check)
      mem false
  in
  match Condition.M.find_opt symbol memory with
  | Some _ -> true
  | _ ->
      Condition.M.fold
        (fun _ hd check -> check || inner_contains_symbol hd)
        memory false

let is_new_loc_field field summary =
  let is_null symbol =
    match Value.M.find_opt symbol summary.value with
    | Some x when x.Value.value = Eq Null -> true
    | Some _ -> false
    | _ -> true (* T considers same as null *)
  in
  let _, post_mem = summary.postcond in
  let field_var = AST.get_tail_symbol "" field post_mem in
  match Condition.M.find_opt field_var post_mem with
  | None -> false
  | Some m ->
      Condition.M.fold
        (fun _ x check ->
          match x with
          | Condition.RH_Symbol _ ->
              if
                is_null (AST.get_rh_name x) |> not
                && contains_symbol x (summary.precond |> snd) |> not
              then true
              else check
          | _ -> check)
        m false

let collect_new_loc_field summary =
  let post_var, post_mem = summary.postcond in
  let post_this =
    AST.get_next_symbol (AST.get_id_symbol post_var "this") post_mem
  in
  match Condition.M.find_opt post_this post_mem with
  | None -> []
  | Some value_map ->
      Condition.M.fold
        (fun fld sym fld_lst ->
          match fld with
          | Condition.RH_Var id ->
              if is_new_loc_field sym summary then id :: fld_lst else fld_lst
          | _ -> fld_lst)
        value_map []

let collect_new_loc_fields lst =
  let rec collect_for lst =
    match lst with
    | hd :: tl -> collect_for tl |> List.rev_append (collect_new_loc_field hd)
    | _ -> []
  in
  collect_for lst

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
    |> Parser.parse_citv false pre_mem
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
    use_field = UseFieldMap.M.empty;
    precond = (pre_var, pre_mem);
    postcond = (post_var, post_mem);
    args = [];
  }

let get_method_name assoc =
  let method_name =
    JsonUtil.member "method" assoc
    |> JsonUtil.to_list |> List.hd |> JsonUtil.to_string |> Parser.split_name
  in
  method_name

let get_return assoc =
  let return =
    JsonUtil.member "method" assoc
    |> JsonUtil.to_list |> List.hd |> JsonUtil.to_string |> Parser.split_return
  in
  return

let is_unnes_method fparam =
  let check_anony_class t =
    match t with
    | Object o ->
        let clist = Str.split Regexp.dollar o in
        List.fold_left
          (fun check name ->
            match name |> int_of_string_opt with Some _ -> true | _ -> check)
          false clist
    | _ -> false
  in
  let check_lambda id =
    if Str.string_match ("\\$bcvar" |> Str.regexp) id 0 then true else false
  in
  let check_unnes p =
    match p with
    | This _ -> false
    | Var (typ, id) -> check_anony_class typ || check_lambda id
  in
  List.fold_left
    (fun check param -> if check_unnes param then true else check)
    false fparam

let mapping_method_info method_info mmap =
  let method_name = get_method_name method_info in
  let return = get_return method_info in
  let modifier =
    JsonUtil.member "modifier" method_info
    |> JsonUtil.to_list |> List.hd |> modifier_of_json
  in
  let is_static =
    JsonUtil.member "is_static" method_info
    |> JsonUtil.to_list |> List.hd |> JsonUtil.to_string |> bool_of_string
  in
  let formal_params =
    JsonUtil.member "param" method_info
    |> JsonUtil.to_list
    |> List.fold_left
         (fun l p -> (JsonUtil.to_string p |> Parser.parse_param) :: l)
         []
    |> List.rev
  in
  let filename =
    JsonUtil.member "filename" method_info
    |> JsonUtil.to_list |> List.hd |> JsonUtil.to_string
  in
  let info =
    MethodInfo.{ modifier; is_static; formal_params; return; filename }
  in
  if
    Str.string_match (".*access\\$.*" |> Str.regexp) method_name 0
    || Str.string_match (".*access_.*" |> Str.regexp) method_name 0
    || Str.string_match (".*\\.clone()$" |> Str.regexp) method_name 0
    || Str.string_match
         (".*\\[specialized with aliases\\]" |> Str.regexp)
         method_name 0
    || is_unnes_method formal_params
  then mmap
  else MethodInfo.M.add method_name info mmap

let mapping_summary method_summaries minfo mmap =
  let method_name = get_method_name method_summaries in
  let summaries =
    JsonUtil.member "summary" method_summaries
    |> JsonUtil.to_list
    |> List.fold_left (fun lst summary -> parse_summary summary :: lst) []
    |> List.rev
  in
  let summaries =
    if summaries = [] then ([ empty_summary ], [])
    else (summaries, collect_new_loc_fields summaries)
  in
  if
    Str.string_match (".*access\\$.*" |> Str.regexp) method_name 0
    || Str.string_match (".*access_.*" |> Str.regexp) method_name 0
    || Str.string_match (".*\\.clone()$" |> Str.regexp) method_name 0
    || Str.string_match
         (".*\\[specialized with aliases\\]" |> Str.regexp)
         method_name 0
    || MethodInfo.M.mem method_name minfo |> not
  then mmap
  else SummaryMap.M.add method_name summaries mmap

let from_method_json json =
  let json = JsonUtil.to_list json in
  let method_info =
    List.fold_left
      (fun mmap method_info -> mapping_method_info method_info mmap)
      MethodInfo.M.empty json
  in
  Modeling.add_java_package_method method_info

let from_summary_json minfo json =
  let json = JsonUtil.to_list json in
  let summary_map =
    List.fold_left
      (fun mmap method_summaries -> mapping_summary method_summaries minfo mmap)
      SummaryMap.M.empty json
  in
  Modeling.add_java_package_summary summary_map
