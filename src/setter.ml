module Relation = Language.Relation
module Value = Language.Value
module Condition = Language.Condition
module SummaryMap = Language.SummaryMap
module SetterMap = Language.SetterMap
module FieldMap = Language.FieldMap

let get_this_symbol variable =
  Condition.M.fold
    (fun symbol id this_symbol ->
      match id with
      | Condition.RH_Var v when v = "this" -> symbol
      | _ -> this_symbol)
    variable Condition.RH_Any

let merge_field_map m1 m2 =
  FieldMap.M.merge
    (fun _ v1 v2 ->
      match (v1, v2) with Some _, _ -> v1 | _, Some _ -> v2 | _ -> None)
    m1 m2

let rec get_change_field post_key field_name pre_mem post_mem field_map =
  match Condition.M.find_opt post_key post_mem with
  | None -> field_map
  | Some value_map -> (
      match Condition.M.find_opt post_key pre_mem with
      | None -> FieldMap.M.add field_name (Value.Eq (Int 0)) field_map
      | Some _ ->
          Condition.M.fold
            (fun field value old_field_map ->
              let new_field_map =
                match field with
                | Condition.RH_Var id ->
                    get_change_field value id pre_mem post_mem field_map
                | _ ->
                    get_change_field value field_name pre_mem post_mem field_map
              in
              merge_field_map new_field_map old_field_map)
            value_map field_map)

let get_change_fields
    Language.{ precond = _, pre_mem; postcond = post_var, post_mem; _ } =
  let post_this = get_this_symbol post_var in
  get_change_field post_this "" pre_mem post_mem FieldMap.M.empty

let get_class_name method_name = String.split_on_char '.' method_name |> List.hd

let is_constructor method_name =
  Str.string_match (".*\\.<init>" |> Str.regexp) method_name 0

let find_setter method_name method_summarys mmap =
  let class_name = get_class_name method_name in
  let change_fields =
    List.fold_left
      (fun field_map summary ->
        get_change_fields summary |> merge_field_map field_map)
      FieldMap.M.empty method_summarys
  in
  if FieldMap.M.is_empty change_fields || is_constructor method_name then mmap
  else
    let fields =
      FieldMap.M.fold
        (fun field _ field_list -> field :: field_list)
        change_fields []
    in
    if SetterMap.M.mem class_name mmap then
      let setter_list =
        SetterMap.M.find class_name mmap |> List.cons (method_name, fields)
      in
      SetterMap.M.add class_name setter_list mmap
    else SetterMap.M.add class_name [ (method_name, fields) ] mmap

let from_summary_map summary =
  SummaryMap.M.fold
    (fun method_name method_summarys mmap ->
      find_setter method_name method_summarys mmap)
    summary SetterMap.M.empty
