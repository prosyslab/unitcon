open Language

module TailsSet = Set.Make (struct
  type t = Condition.rh

  let compare = compare
end)

let rec get_tail_set symbol memory tails =
  match Condition.M.find_opt symbol memory with
  | Some sym ->
      Condition.M.fold
        (fun _ symbol set ->
          if TailsSet.mem symbol set then set
          else get_tail_set symbol memory (TailsSet.add symbol set))
        sym tails
  | None -> tails

let is_tail_symbol symbol memory =
  match Condition.M.find_opt symbol memory with Some _ -> false | None -> true

let equal_value v1 v2 =
  let normalize v =
    match v with
    | Value.Int 0 | Long 0 | Byte 0 | Float 0.0 | Double 0.0 | Bool false | Null
      ->
        Value.Null
    | _ -> v
  in
  match (v1, v2) with
  | Value.Eq NonValue, _ | _, Value.Eq NonValue -> false
  | Neq Null, Neq Null ->
      (* Kinds of objects are enormous. So it doesn't mean that both values are the same *)
      false
  | _ when v1 = v2 -> true
  | Eq c1, Eq c2
  | Neq c1, Neq c2
  | Le c1, Le c2
  | Lt c1, Lt c2
  | Ge c1, Ge c2
  | Gt c1, Gt c2
    when normalize c1 = normalize c2 ->
      true
  | _ -> false

let get_value symbol vmap =
  match Value.M.find_opt (get_rh_name symbol) vmap with
  | Some v -> v.Value.value
  | _ -> Value.Eq NonValue

let equal_values set1 set2 vmap =
  let filter (set, mem) = TailsSet.filter (fun x -> is_tail_symbol x mem) set in
  let inner_equal v set =
    if Value.Eq NonValue = v then false
    else
      TailsSet.fold
        (fun value equal ->
          if equal_value v (get_value value vmap) then true else equal)
        set false
  in
  TailsSet.fold
    (fun v equal ->
      if inner_equal (get_value v vmap) (filter set2) then true else equal)
    (filter set1) false

let collect_field_set field value pre_mem post_mem vmap old_set =
  match field with
  | Condition.RH_Var id ->
      let pre = get_tail_set value pre_mem TailsSet.empty in
      let post = get_tail_set value post_mem TailsSet.empty in
      let compare_value = equal_values (pre, pre_mem) (post, post_mem) vmap in
      let change_field = if pre = post || compare_value then false else true in
      if change_field then
        FieldSet.add { used_in_error = false; name = id } old_set
      else old_set
  | _ -> old_set

let get_change_field post_key pre_mem post_mem vmap field_set =
  match Condition.M.find_opt post_key post_mem with
  | None -> field_set
  | Some value_map -> (
      match Condition.M.find_opt post_key pre_mem with
      | None -> field_set
      | Some _ ->
          Condition.M.fold
            (fun field value old_field_set ->
              collect_field_set field value pre_mem post_mem vmap old_field_set)
            value_map field_set)

let get_change_fields
    { precond = _, pre_mem; postcond = post_var, post_mem; value; _ } =
  let post_this = get_next_symbol (get_id_symbol post_var "this") post_mem in
  (* e.g., post_this = v3 *)
  get_change_field post_this pre_mem post_mem value FieldSet.empty

let find_setter m_name m_summaries m_infos mmap =
  let class_name = Utils.get_class_name m_name in
  let change_fields =
    List.fold_left
      (fun field_set summary ->
        get_change_fields summary |> FieldSet.union field_set)
      FieldSet.empty m_summaries
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
    (fun m_name (m_summaries, _) mmap ->
      find_setter m_name m_summaries m_infos mmap)
    summary SetterMap.M.empty
