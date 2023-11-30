module Relation = Language.Relation
module Value = Language.Value
module Condition = Language.Condition
module SummaryMap = Language.SummaryMap
module SetterMap = Language.SetterMap
module FieldSet = Language.FieldSet
module MethodInfo = Language.MethodInfo

let get_this_symbol variable =
  Condition.M.fold
    (fun symbol id this_symbol ->
      match id with
      | Condition.RH_Var v when v = "this" -> symbol
      | _ -> this_symbol)
    variable Condition.RH_Any

let get_next_symbol symbol memory =
  let next_symbol = Condition.M.find_opt symbol memory in
  match next_symbol with
  | Some sym -> (
      match Condition.M.find_opt Condition.RH_Any sym with
      | Some s -> s
      | None -> symbol)
  | None -> symbol

let rec get_tail_symbol symbol memory =
  let next_symbol = Condition.M.find_opt symbol memory in
  match next_symbol with
  | Some sym -> (
      let m_any_symbol = Condition.M.find_opt Condition.RH_Any sym in
      match m_any_symbol with
      | Some any_s -> get_tail_symbol any_s memory
      | None -> symbol)
  | None -> symbol

let get_head_of_tail symbol memory =
  Condition.M.fold
    (fun head value t ->
      match Condition.M.find_opt Condition.RH_Any value with
      | Some any_s when symbol = any_s -> head
      | _ -> t)
    memory symbol

let get_change_field post_key pre_mem post_mem field_set =
  match Condition.M.find_opt post_key post_mem with
  | None -> field_set
  | Some value_map -> (
      match Condition.M.find_opt post_key pre_mem with
      | None -> field_set
      | Some _ ->
          Condition.M.fold
            (fun field value old_field_set ->
              let new_field_set =
                match field with
                | Condition.RH_Var id ->
                    let pre = get_tail_symbol value pre_mem in
                    let post = get_tail_symbol value post_mem in
                    let change_field = if pre = post then false else true in
                    if change_field then FieldSet.S.add id field_set
                    else field_set
                | _ -> field_set
              in
              FieldSet.S.union new_field_set old_field_set)
            value_map field_set)

let get_change_fields
    Language.{ precond = _, pre_mem; postcond = post_var, post_mem; _ } =
  let post_this = get_next_symbol (get_this_symbol post_var) post_mem in
  get_change_field post_this pre_mem post_mem FieldSet.S.empty

let get_class_name method_name =
  let m_name =
    Regexp.first_rm ("(.*)" |> Str.regexp) method_name
    |> Str.split Regexp.dot |> List.rev |> List.hd
  in
  Regexp.first_rm ("\\." ^ m_name ^ "(.*)" |> Str.regexp) method_name

let find_setter m_name m_summarys m_infos mmap =
  let class_name = get_class_name m_name in
  let change_fields =
    List.fold_left
      (fun field_set summary ->
        get_change_fields summary |> FieldSet.S.union field_set)
      FieldSet.S.empty m_summarys
  in
  match MethodInfo.M.find_opt m_name m_infos with
  | Some i ->
      if i.MethodInfo.return = "" || i.MethodInfo.return <> "void" then mmap
      else if SetterMap.M.mem class_name mmap then
        let setter_list =
          SetterMap.M.find class_name mmap |> List.cons (m_name, change_fields)
        in
        SetterMap.M.add class_name setter_list mmap
      else SetterMap.M.add class_name [ (m_name, change_fields) ] mmap
  | _ -> mmap

let from_summary_map summary m_infos =
  SummaryMap.M.fold
    (fun method_name method_summarys mmap ->
      find_setter method_name method_summarys m_infos mmap)
    summary SetterMap.M.empty
