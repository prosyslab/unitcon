open Language
open Generator
open Dug
module TypeSet = Set.Make (String)

module VarSet = Set.Make (struct
  type t = variable [@@deriving compare]
end)

(* Set of VarSet *)
module VarSets = Set.Make (VarSet)

module ReturnStmtSet = Set.Make (struct
  type t = DUGIR.t [@@deriving compare]
end)

module StmtMap = struct
  module M = Map.Make (struct
    type t = DUGIR.t [@@deriving compare]
  end)

  type t = (DUGIR.t * DUG.t) list M.t
end

module ArgSet = Set.Make (struct
  type t = DUGIR.id [@@deriving compare]
end)

let reusable_arg = ref []

type partial_tc = {
  unroll : int;
  nt_cost : int;
  t_cost : int;
  prec : int; (* number of precise statement *)
  tc : DUG.t;
  loop_ids : LoopIdMap.t;
  obj_types : ObjTypeMap.t;
}

(* non-terminal cost for p, terminal cost for p, precision for p *)
let get_cost p =
  if p.unroll > 1 then (p.nt_cost, p.t_cost, p.prec) else (0, 0, 0)

let mk_cost prev_p curr_tc curr_loop_id curr_obj_type prec =
  {
    unroll = prev_p.unroll + 1;
    nt_cost = DUG.count_nt curr_tc;
    t_cost = DUG.count_t curr_tc;
    prec;
    tc = curr_tc;
    loop_ids = curr_loop_id;
    obj_types = curr_obj_type;
  }

let empty_id_map = LoopIdMap.M.empty

let empty_obj_type_map = ObjTypeMap.M.empty

let empty_p =
  {
    unroll = 0;
    nt_cost = 0;
    t_cost = 0;
    prec = 0;
    tc = DUG.empty;
    loop_ids = empty_id_map;
    obj_types = empty_obj_type_map;
  }

let is_string x = DUG.get_vinfo x |> fst |> is_string

let is_primitive_from_id x = DUG.get_vinfo x |> fst |> is_primitive

let is_primitive_from_v v = get_type (fst v.DUGIR.variable) |> is_primitive

let get_m_lst x0 m_info (c_info, ig) =
  let c_name = DUG.get_vinfo x0 |> fst |> get_class_name in
  let c_to_find = get_subtypes c_name ig in
  MethodInfo.M.fold
    (fun m_name _ method_list ->
      if IgnoredMethods.mem m_name !ignored_methods then method_list
      else if !Cmdline.debug && List.mem m_name !Cmdline.ignore then method_list
      else
        List.fold_left
          (fun lst_tuple c_name_to_find ->
            get_m_lst_from_one_c c_name m_name m_info c_info ig c_to_find
              lst_tuple c_name_to_find)
          method_list c_to_find)
    m_info ([], [], [])

let collect_recv m_info (ret_type, m_type) c_info s_map subtypes =
  (* cond_r is same as cond_common *)
  let cond_common typ m_name =
    is_available_method m_name m_info && is_available_class typ (fst c_info)
  in
  let cond_c typ m_name =
    cond_common typ m_name && match_constructor_name typ m_name
  in
  let cond_s typ (m_name, field_set) =
    cond_common typ m_name && FieldSet.is_empty field_set |> not
  in
  let get_r_list typ =
    get_ret_methods typ ret_type
    |> List.fold_left
         (fun lst x -> if cond_common typ x then x :: lst else lst)
         []
  in
  let get_c_list typ =
    get_methods_of_class typ m_type
    |> List.fold_left (fun lst x -> if cond_c typ x then x :: lst else lst) []
  in
  let get_s_list typ =
    get_setters typ s_map
    |> List.fold_left
         (fun lst setter -> if cond_s typ setter then setter :: lst else lst)
         []
  in
  TypeSet.fold
    (fun typ (ret_list, set_list) ->
      ( List.rev_append (get_r_list typ) (get_c_list typ)
        |> List.rev_append ret_list,
        List.rev_append (get_s_list typ) set_list ))
    subtypes ([], [])

let default_value_list typ import p_info =
  let predef = get_predef_value_list typ p_info in
  let extra = get_extra_value_list typ import p_info in
  let lst = List.rev_append predef extra in
  match typ with
  | Int | Long | Short | Byte ->
      let f acc x =
        match int_of_string_opt x with
        | Some i -> DUGIR.Primitive (Z i) :: acc
        | _ -> acc
      in
      List.fold_left f [] lst
  | Float | Double ->
      let f acc x =
        match float_of_string_opt x with
        | Some i -> DUGIR.Primitive (R i) :: acc
        | _ -> acc
      in
      List.fold_left f [] lst
  | Bool ->
      let f acc x =
        match bool_of_string_opt x with
        | Some i -> DUGIR.Primitive (B i) :: acc
        | _ -> acc
      in
      List.fold_left f [] lst
  | Char ->
      let f acc x =
        if String.length x = 1 then DUGIR.Primitive (C x.[0]) :: acc else acc
      in
      List.fold_left f [] lst
  | String ->
      (* String constant is already expanded when finding error entries *)
      let f acc x =
        if List.mem (DUGIR.Primitive (S x)) acc then acc
        else if x = "NULL" then DUGIR.Null :: acc
        else DUGIR.Primitive (S x) :: acc
      in
      List.fold_left f [] predef
  | _ ->
      let f acc x = if x = "NULL" then DUGIR.Null :: acc else acc in
      List.fold_left f [] lst

let filter_size id lst =
  if id = "size" || id = "index" || id = "capacity" then
    List.filter
      (fun x -> match snd x with DUGIR.Primitive (Z x) -> x >= 0 | _ -> false)
      lst
  else lst

let calc_value id value default =
  let prec = if value.Value.from_error then 2 else 0 in
  let calc_int result =
    match int_of_string_opt result with
    | Some i ->
        calc_value_list value.Value.from_error
          [ (prec, DUGIR.Primitive (Z i)) ]
          default
        |> filter_size id
    | _ -> calc_value_list false [] default |> filter_size id
  in
  let calc_float result =
    match float_of_string_opt result with
    | Some f ->
        calc_value_list value.Value.from_error
          [ (prec, DUGIR.Primitive (R f)) ]
          default
    | _ -> calc_value_list false [] default
  in
  match value.Value.value with
  | Eq v -> (
      match v with
      | Int _ | Long _ | Short _ | Byte _ ->
          let result = get_z3_result value.Value.value id in
          calc_int result
      | Float _ | Double _ ->
          let result = get_z3_result value.Value.value id in
          calc_float result
      | Bool b ->
          calc_value_list value.Value.from_error
            [ (prec, DUGIR.Primitive (B b)) ]
            default
      | Char c ->
          calc_value_list value.Value.from_error
            [ (prec, DUGIR.Primitive (C c)) ]
            default
      | String s ->
          calc_value_list value.Value.from_error
            [ (prec, DUGIR.Primitive (S s)) ]
            default
      | Null -> [ (prec, DUGIR.Null) ]
      | _ -> failwith "not implemented eq")
  | Neq v -> (
      match v with
      | Int _ | Long _ | Short _ | Byte _ ->
          let result = get_z3_result value.Value.value id in
          calc_int result
      | Float _ | Double _ ->
          let result = get_z3_result value.Value.value id in
          calc_float result
      | Bool b ->
          calc_value_list value.Value.from_error
            [ (prec, DUGIR.Primitive (B (not b))) ]
            default
      | String s ->
          calc_value_list value.Value.from_error
            [ (prec, DUGIR.Primitive (S ("not_" ^ s))) ]
            default
      | Null ->
          (* Among the const, only the string can be defined as null *)
          List.fold_left
            (fun lst x ->
              if x = DUGIR.Null then (-prec, x) :: lst else (prec, x) :: lst)
            [] default
      | _ -> failwith "not implemented neq")
  | Le v -> (
      match v with
      | Int _ | Long _ | Short _ | Byte _ ->
          let result = get_z3_result value.Value.value id in
          calc_int result
      | Float _ | Double _ ->
          let result = get_z3_result value.Value.value id in
          calc_float result
      | _ -> failwith "not implemented le")
  | Lt v -> (
      match v with
      | Int _ | Long _ | Short _ | Byte _ ->
          let result = get_z3_result value.Value.value id in
          calc_int result
      | Float _ | Double _ ->
          let result = get_z3_result value.Value.value id in
          calc_float result
      | _ -> failwith "not implemented lt")
  | Ge v -> (
      match v with
      | Int _ | Long _ | Short _ | Byte _ ->
          let result = get_z3_result value.Value.value id in
          calc_int result
      | Float _ | Double _ ->
          let result = get_z3_result value.Value.value id in
          calc_float result
      | _ -> failwith "not implemented ge")
  | Gt v -> (
      match v with
      | Int _ | Long _ | Short _ | Byte _ ->
          let result = get_z3_result value.Value.value id in
          calc_int result
      | Float _ | Double _ ->
          let result = get_z3_result value.Value.value id in
          calc_float result
      | _ -> failwith "not implemented gt")
  | Between (v1, v2) -> (
      match (v1, v2) with
      | Int _, _ | Long _, _ ->
          let result = get_z3_result value.Value.value id in
          calc_int result
      | Float _, _ | Double _, _ ->
          let result = get_z3_result value.Value.value id in
          calc_float result
      | MinusInf, PlusInf -> calc_value_list value.Value.from_error [] default
      | _ -> failwith "not implemented between")
  | Outside (v1, v2) -> (
      match (v1, v2) with
      | Int _, _ | Long _, _ ->
          let result = get_z3_result value.Value.value id in
          calc_int result
      | Float _, _ | Double _, _ ->
          let result = get_z3_result value.Value.value id in
          calc_float result
      | _ -> failwith "not implemented outside")

let get_value v p_info =
  let typ, id = DUG.get_vinfo v in
  let find_value1 = find_target_value id (DUG.get_v v).summary in
  let find_value2 = find_target_value_from_this id (DUG.get_v v).summary in
  let default = default_value_list typ (DUG.get_v v).import p_info in
  let found_value =
    if not_found_value find_value1 then
      if not_found_value find_value2 then
        let default_value =
          List.fold_left (fun lst x -> (0, x) :: lst) [] default
        in
        if typ = Int then filter_size id default_value else default_value
      else calc_value id find_value2 default
    else calc_value id find_value1 default
  in
  found_value

let mk_new_set summary params p =
  let get_type p = match p with Var (t, _) -> t | _ -> NonType in
  let equal_value (v1 : Value.v) (v2 : Value.v) =
    if not_found_value v1 || not_found_value v2 then true else v1 = v2
  in
  let is_same_precond p op_p =
    let p_val = get_p_value p summary in
    let op_p_val = get_p_value op_p summary in
    equal_value p_val op_p_val
  in
  let t1 = get_type p in
  if t1 = NonType then VarSet.empty
  else
    List.fold_left
      (fun set op_p ->
        let t2 = get_type op_p in
        if t1 = t2 && is_same_precond p op_p then VarSet.add op_p set else set)
      (VarSet.add p VarSet.empty)
      params

let get_same_params_set summary params =
  List.fold_left
    (fun sets p ->
      let new_set = mk_new_set summary params p in
      if VarSet.cardinal new_set < 2 then sets else VarSets.add new_set sets)
    VarSets.empty params

let find_class_file =
  List.fold_left
    (fun gvar_list const ->
      (0, DUGIR.GlobalConstant (const ^ ".class")) :: gvar_list)
    []
    [ "UnitconInterface"; "UnitconEnum" ]

let mk_gvar c_name var = (0, DUGIR.GlobalConstant (c_name ^ "." ^ var))

let find_all_global_var_list c_name i_info =
  match InstanceInfo.M.find_opt c_name i_info with
  | None -> []
  | Some info ->
      List.fold_left
        (fun lst const -> (0, DUGIR.GlobalConstant const) :: lst)
        [] info

let compare_global_var c_name t_var s_trace =
  Condition.M.fold
    (fun head _ gvar ->
      match head with
      | Condition.RH_Var var when var = t_var -> c_name ^ "." ^ var |> mk_some
      | _ -> gvar)
    s_trace None

(* If a global constant is revealed in the summary, it only finds this global constant. *)
let find_target_global_var c_name t_var mem summary common_gvs =
  let mk_gvar gv summaries =
    (is_from_error false (List.hd summaries), DUGIR.GlobalConstant gv)
  in
  let get_compared_global_var v init_summary =
    (Condition.M.fold (fun _ s_trace found_gv ->
         match compare_global_var c_name v s_trace with
         | Some gv ->
             if List.mem (0, DUGIR.GlobalConstant gv) common_gvs then
               Some (mk_gvar gv init_summary)
             else found_gv
         | None -> found_gv))
      mem None
  in
  let get_target_global_var var =
    match SummaryMap.M.find_opt (c_name ^ ".<clinit>()") summary with
    | Some (init_summary, _) -> get_compared_global_var var init_summary
    | None -> None
  in
  match t_var with Some v -> get_target_global_var v | None -> None

let global_var_list class_name t_summary summary i_info =
  let get_gv_symbol var symbol found =
    (* e.g., var: c.Class, class_name: a.b.c.Class *)
    match var with
    | Condition.RH_Var var
      when Str.string_match (".*\\." ^ var |> Str.regexp) class_name 0 ->
        get_rh_name symbol |> mk_some
    | _ -> found
  in
  let vars, mem = t_summary.precond in
  let t_var =
    Condition.M.fold
      (fun symbol var find_var -> get_gv_symbol var symbol find_var)
      vars None
  in
  match t_var with
  | None when class_name = "java.lang.Class" -> find_class_file
  | None -> find_all_global_var_list class_name i_info
  | Some x -> (
      let common = find_all_global_var_list class_name i_info in
      match
        find_target_global_var class_name (get_target_var x mem) mem summary
          common
      with
      | Some gv -> gv :: common
      | None -> common)

let get_param v summary =
  let get_field id =
    DUG.get_field_from_ufmap id (fst summary.precond) summary.use_field
  in
  let make_new_var id =
    DUGIR.
      {
        import = get_package_from_v v;
        variable = (v, mk_some !new_var);
        field = get_field id;
        summary;
      }
  in
  match v with
  | Var (typ, _) when typ = NonType -> None
  | This _ ->
      incr new_var;
      make_new_var "this" |> mk_some
  | Var (_, id) ->
      incr new_var;
      make_new_var id |> mk_some

let get_org_params_list summary org_param =
  List.fold_left
    (fun params v ->
      match get_param v summary with Some p -> p :: params | _ -> params)
    [] org_param
  |> List.rev

(* variable -> variable * unique int id *)
let find_org_param org_params_list p =
  List.fold_left
    (fun param real_arg ->
      if p = fst real_arg.DUGIR.variable then real_arg else param)
    DUG.empty_var org_params_list

(* return representative parameter of the set containing the target parameter.
   Set.choose is deterministic at same set. *)
let get_same_param target p_set =
  let t = fst target.DUGIR.variable in
  VarSets.fold
    (fun set find -> if VarSet.mem t set then VarSet.choose set else find)
    p_set t

let get_param_list param std_param curr_param_list =
  if curr_param_list = [] then [ [ param ] ]
  else if param = std_param then
    (* not found the same parameter *)
    List.fold_left (fun acc list -> (param :: list) :: acc) [] curr_param_list
  else
    List.fold_left
      (fun acc list -> (param :: list) :: (std_param :: list) :: acc)
      [] curr_param_list

let mk_params_list summary p_set org_param =
  let org_params_list = get_org_params_list summary org_param in
  let rec mk_params org_params params_list =
    match org_params with
    | hd :: tl ->
        let same_param =
          get_same_param hd p_set |> find_org_param org_params_list
        in
        get_param_list hd same_param params_list |> mk_params tl
    | _ -> params_list
  in
  mk_params org_params_list []

let mk_arg ~is_s param s =
  let param = if is_s then param else List.tl param in
  let same_params_set = get_same_params_set s param in
  mk_params_list s same_params_set param
  |> List.fold_left (fun args lst -> List.rev lst :: args) []

let get_field_set ret s_map =
  let c_name = DUG.get_vinfo ret |> fst |> get_class_name in
  let fields =
    List.fold_left
      (fun fm (_, fields) -> FieldSet.union fields fm)
      (DUG.get_v ret).field (get_setters c_name s_map)
  in
  FieldSet.fold
    (fun x new_fields ->
      let dup = Field.{ used_in_error = false; name = x.name } in
      if x.used_in_error && FieldSet.mem dup new_fields then
        FieldSet.remove dup new_fields
      else new_fields)
    fields fields

let error_entry_func ee es m_info c_info =
  let param = get_formal_params ee m_info in
  let f_arg_list = mk_arg ~is_s:(is_static ee m_info) param es in
  let c_name = Utils.get_class_name ee in
  let typ_list = get_usable_types c_name c_info in
  List.fold_left
    (fun lst typ ->
      let f = DUGIR.F { typ; method_name = ee; import = typ; summary = es } in
      if f_arg_list = [] then (0, f, []) :: lst
      else List.fold_left (fun acc f_arg -> (0, f, f_arg) :: acc) lst f_arg_list)
    [] typ_list

let is_file_obj x = is_file_obj (DUG.get_vinfo x |> fst)

let is_instream_obj x = is_instream_obj (DUG.get_vinfo x |> fst)

let is_outstream_obj x = is_outstream_obj (DUG.get_vinfo x |> fst)

let is_reader_obj x = is_reader_obj (DUG.get_vinfo x |> fst)

let is_writer_obj x = is_writer_obj (DUG.get_vinfo x |> fst)

let not_null_obj x =
  if
    is_file_obj x || is_instream_obj x || is_outstream_obj x || is_reader_obj x
    || is_writer_obj x
  then true
  else false

let is_comparable x = is_comparable (DUG.get_vinfo x |> fst)

let is_object x = is_object (DUG.get_vinfo x |> fst)

let is_list x = is_list (DUG.get_vinfo x |> fst)

let is_number x = is_number (DUG.get_vinfo x |> fst)

let mk_void_func (var : DUGIR.var) id class_name m_info s_lst =
  let get_arg_list s =
    mk_arg ~is_s:(is_static s m_info) (get_formal_params s m_info) var.summary
  in
  let typ =
    if Utils.is_array class_name then
      DUG.get_vinfo id |> fst |> get_array_class_name
    else class_name
  in
  let get_f s =
    DUGIR.F { typ; method_name = s; import = var.import; summary = var.summary }
  in
  let get_prec s fields =
    if contains_used_in_error var.field fields || Utils.is_modeling_set s then 0
    else -2
  in
  List.fold_left
    (fun lst (s, fields, _) ->
      let f_arg_list = get_arg_list s in
      let prec = get_prec s fields in
      let f = get_f s in
      if f_arg_list = [] then (prec, f, []) :: lst
      else
        List.fold_left (fun acc f_arg -> (prec, f, f_arg) :: acc) lst f_arg_list)
    [] s_lst

(* id is receiver variable *)
let get_void_func id ?(ee = "") ?(es = empty_summary)
    { summary; m_info; c_info; setter_map; _ } =
  if DUG.is_id id then error_entry_func ee es m_info c_info
  else
    let var = DUG.get_v id in
    let class_name = DUG.get_vinfo id |> fst |> get_class_name in
    if class_name = "" || class_name = "String" then []
    else
      get_setters class_name setter_map
      |> List.filter (fun (s, _) ->
             (not (IgnoredMethods.mem s !ignored_methods))
             && (not (!Cmdline.debug && List.mem s !Cmdline.ignore))
             && is_available_method s m_info)
      |> get_setter_list summary
      |> mk_void_func var id class_name m_info

let get_cfunc id constructor m_info =
  let cost, c, s = constructor in
  let t = Utils.get_class_name c in
  let t =
    if Utils.is_array t then DUG.get_vinfo id |> fst |> get_array_class_name
    else t
  in
  let func = DUGIR.F { typ = t; method_name = c; import = t; summary = s } in
  let arg_list =
    mk_arg ~is_s:(is_static c m_info) (get_formal_params c m_info) s
  in
  if arg_list = [] then [ (cost, (func, DUGIR.Arg [])) ]
  else
    List.fold_left
      (fun cfuncs arg -> (cost, (func, DUGIR.Arg arg)) :: cfuncs)
      [] arg_list

let get_cfuncs id list m_info =
  List.fold_left
    (fun lst (cost, c, s) ->
      List.rev_append (get_cfunc id (cost, c, s) m_info) lst)
    [] list

let get_c ret c_lst summary m_info =
  let class_name = DUG.get_vinfo ret |> fst |> get_class_name in
  if class_name = "" then []
  else
    let id = DUG.get_vinfo ret |> snd in
    let s_list =
      satisfied_c_list id (DUG.get_v ret).summary summary c_lst
      |> summary_filtering class_name m_info
      |> prune_dup_summary ~is_constructor:true m_info
    in
    get_cfuncs ret s_list m_info

let get_recv_type c_info summary_lst =
  List.fold_left
    (fun need_typ_set (_, c, _) ->
      let recv_type = Utils.get_class_name c in
      let subtypes = get_subtypes recv_type (snd c_info) in
      TypeSet.union (TypeSet.of_list subtypes) need_typ_set)
    TypeSet.empty summary_lst

let memory_effect_filtering summary m_info type_info c_info s_map smy_lst =
  let smy_lst = List.rev smy_lst in
  if !Cmdline.basic_mode || !Cmdline.priority_mode then List.rev smy_lst
  else
    let recv_type = get_recv_type c_info smy_lst in
    let ret_recv_methods, set_recv_methods =
      collect_recv m_info type_info c_info s_map recv_type
    in
    List.fold_left
      (fun lst (i, c, c_smy) ->
        let fld_name = ret_fld_name_of c_smy in
        let recv_type = Utils.get_class_name c in
        let subtypes =
          if is_static c m_info then [] else get_subtypes recv_type (snd c_info)
        in
        let check_getter = is_getter_with_memory_effect c_smy fld_name in
        if subtypes = [] && check_getter then (i, c, c_smy) :: lst
        else if
          check_getter
          || is_ret_recv_mem_effect fld_name subtypes summary m_info
               ret_recv_methods
          || is_set_recv_mem_effect fld_name summary m_info set_recv_methods
        then (i, c, c_smy) :: lst
        else lst)
      [] smy_lst

let get_ret_c ret ret_obj_lst summary m_info type_info c_info s_map =
  let class_name = DUG.get_vinfo ret |> fst |> get_class_name in
  if class_name = "" then []
  else if !Cmdline.unknown_bug && is_instream_obj ret then []
  else
    let id = DUG.get_vinfo ret |> snd in
    let s_list =
      satisfied_c_list id (DUG.get_v ret).summary summary ret_obj_lst
      |> summary_filtering class_name m_info
      |> prune_dup_summary m_info
      |> memory_effect_filtering summary m_info type_info c_info s_map
    in
    get_cfuncs ret s_list m_info

let get_inner_func f arg =
  let fname =
    Str.split Regexp.dollar (DUG.get_func f).method_name |> List.rev |> List.hd
  in
  let n_f =
    DUGIR.mk_f (DUG.get_func f).typ fname (DUG.get_func f).import
      (DUG.get_func f).summary
  in
  (* outer class variable *)
  let recv = try DUG.get_arg arg |> List.hd with _ -> DUG.empty_var in
  let n_recv =
    let escaped_fname =
      Str.global_replace Regexp.open_bk "\\[" fname
      |> Str.global_replace Regexp.end_bk "\\]"
    in
    let var =
      Object
        ((DUG.get_func f).method_name
        |> Regexp.first_rm (Str.regexp ("\\$" ^ escaped_fname)))
    in
    DUGIR.mk_var recv.import
      (Var (var, "con_outer"), mk_some !outer)
      FieldSet.empty recv.summary
    |> DUGIR.mk_variable
  in
  (n_recv, n_f, DUGIR.Arg (try DUG.get_arg arg |> List.tl with _ -> []))

let cname_condition m_name m_info c_info =
  match MethodInfo.M.find_opt m_name m_info with
  | Some info ->
      info.MethodInfo.return <> ""
      && (is_static m_name m_info || is_static_class m_name c_info)
      || Utils.is_init_method m_name
  | _ -> Utils.is_init_method m_name

let get_cname f = DUGIR.ClassName (DUG.get_func f).DUGIR.typ

let is_matched_variable already_var new_var =
  let summary1 = (DUG.get_v already_var).summary in
  let summary2 = (DUG.get_v new_var).summary in
  let this_sym1 = get_id_symbol (fst summary1.precond) "this" |> get_rh_name in
  let this_sym2 = get_id_symbol (fst summary2.precond) "this" |> get_rh_name in
  let check =
    check_intersect ~is_init:true summary1 summary2 [ (this_sym1, this_sym2) ]
    |> List.filter (fun (_, c) -> c = false)
  in
  if check = [] then true else false

let get_reusable_arg s prev_num stmt tc arg =
  let var_to_find = (DUG.get_v arg).variable in
  let node_to_find = DUGIR.Const (prev_num + 1, var_to_find, (arg, Exp)) in
  if DUG.is_already_node stmt node_to_find tc then
    List.fold_left
      (fun lst (ids, x) ->
        let found_node = DUG.find_node stmt node_to_find tc in
        let found_id = DUG.get_id found_node in
        if is_matched_variable found_id arg then (
          reusable_arg := (arg, found_id) :: !reusable_arg;
          (found_id :: ids, DUG.mk_already_arg found_node var_to_find tc x)
          :: lst)
        else lst)
      [] s
  else []

let get_already_reusable_arg arg_graph arg arg_list reusable_args lst =
  List.fold_left
    (fun acc (target_arg, replace_arg) ->
      if arg = target_arg && List.mem replace_arg arg_list then
        (replace_arg :: arg_list, arg_graph) :: acc
      else acc)
    lst reusable_args

let get_already_arg s arg reusable_args =
  List.fold_left
    (fun lst (arg_list, s) ->
      if List.mem arg arg_list then (arg :: arg_list, s) :: lst
      else get_already_reusable_arg s arg arg_list reusable_args lst)
    [] s

let get_arg_seq prev_num stmt tc (args : DUGIR.id list) =
  let already_arg = ref ArgSet.empty in
  reusable_arg := [];
  let apply_const_rule s arg =
    List.fold_left
      (fun lst (ids, x) ->
        (arg :: ids, DUG.mk_const_arg arg (prev_num + 1) x) :: lst)
      [] s
  in
  let apply_assign_rule s arg =
    List.fold_left
      (fun lst (ids, x) ->
        (arg :: ids, DUG.mk_assign_arg arg (prev_num + 1) x) :: lst)
      [] s
  in
  List.fold_left
    (fun s arg ->
      if ArgSet.mem arg !already_arg then get_already_arg s arg !reusable_arg
      else (
        already_arg := ArgSet.add arg !already_arg;
        let reuse_arg = get_reusable_arg s prev_num stmt tc arg in
        let const_arg = apply_const_rule s arg in
        let acc_arg =
          if reuse_arg = [] then const_arg
          else List.rev_append const_arg reuse_arg
        in
        if is_primitive_from_id arg then acc_arg
        else List.rev_append (apply_assign_rule s arg) acc_arg))
    [ ([], DUG.empty) ]
    args

let mk_arg_seq arg prev_num class_name s tc =
  let modified_x x =
    if is_primitive_from_v x then DUG.modify_import class_name x else x
  in
  get_arg_seq prev_num s tc
    (List.fold_left
       (fun lst x -> DUGIR.Variable (modified_x x) :: lst)
       [] (DUG.get_arg arg))

let loop_id_merge old_ids new_ids =
  LoopIdMap.M.merge
    (fun _ v1 v2 ->
      match (v1, v2) with
      | None, None -> None
      | Some _, _ -> v1
      | None, Some _ -> v2)
    old_ids new_ids

(* low priority --> ... --> high priority *)
let sort_const consts =
  List.stable_sort (fun (c1, _) (c2, _) -> compare c1 c2) consts

let comparable_const s p =
  [
    ( 0,
      DUG.const_rule2 s (DUGIR.GlobalConstant "java.math.BigDecimal.ONE") p.tc,
      empty_id_map,
      ObjTypeMap.M.add "java.lang.Comparable" "java.math.BigDecimal"
        empty_obj_type_map );
  ]

let object_const s p =
  let f =
    DUGIR.mk_f "java.lang.Object" "java.lang.Object.<init>()" "java.lang.Object"
      Modeling.obj_summary
  in
  let param = DUGIR.Param [] in
  [
    ( 0,
      DUG.const_rule2_1 s f param p.tc,
      empty_id_map,
      ObjTypeMap.M.add "java.lang.Object" "java.lang.Object" empty_obj_type_map
    );
  ]

let list_const s p =
  let f =
    DUGIR.mk_f "java.util.List" "java.util.ArrayList.<init>()"
      "java.util.ArrayList" Modeling.array_list_summary
  in
  let param = DUGIR.Param [] in
  [
    ( 0,
      DUG.const_rule2_1 s f param p.tc,
      empty_id_map,
      ObjTypeMap.M.add "java.util.List" "java.util.ArrayList" empty_obj_type_map
    );
  ]

let number_const s p =
  [
    ( 0,
      DUG.const_rule2 s (DUGIR.GlobalConstant "java.math.BigDecimal.ONE") p.tc,
      empty_id_map,
      ObjTypeMap.M.add "java.lang.Number" "java.math.BigDecimal"
        empty_obj_type_map );
  ]

let apply_rule1 s p x =
  (fst x, DUG.const_rule1 s (snd x) p.tc, empty_id_map, empty_obj_type_map)

let apply_rule2 s p x =
  (fst x, DUG.const_rule2 s (snd x) p.tc, empty_id_map, empty_obj_type_map)

let apply_rule3 s p x =
  (fst x, DUG.const_rule3 s p.tc, empty_id_map, empty_obj_type_map)

let apply_loop s p x exps prec =
  ( prec,
    DUG.const_rule_loop s p.tc,
    LoopIdMap.M.add x exps empty_id_map,
    empty_obj_type_map )

let get_loop_appl s p x values =
  let prec, exps =
    List.fold_left
      (fun (prec, lst) x1 ->
        let prec = if prec < fst x1 then fst x1 else prec in
        (prec, snd x1 :: lst))
      (min_int, []) values
  in
  [ apply_loop s p x exps prec ]

let get_r3 s p prim_info x =
  List.fold_left
    (fun lst x1 ->
      match snd x1 with DUGIR.Primitive _ -> lst | _ -> [ apply_rule3 s p x1 ])
    [] (get_value x prim_info)

let get_r2 s p { summary; inst_info; _ } x =
  if is_comparable x then comparable_const s p
  else if is_object x then object_const s p
  else if is_number x then number_const s p
  else if !Cmdline.unknown_bug && is_list x then (* heuristic *)
    list_const s p
  else
    List.fold_left
      (fun lst x1 -> apply_rule2 s p x1 :: lst)
      []
      (global_var_list
         (DUG.get_vinfo x |> fst |> get_class_name)
         (DUG.get_v x).summary summary inst_info)

let get_r2_with_loop s p { summary; inst_info; _ } x =
  let gcs =
    global_var_list
      (DUG.get_vinfo x |> fst |> get_class_name)
      (DUG.get_v x).summary summary inst_info
  in
  if is_comparable x then comparable_const s p
  else if is_object x then object_const s p
  else if is_number x then number_const s p
  else if !Cmdline.unknown_bug && is_list x then (* heuristic *)
    list_const s p
  else if gcs = [] then []
  else if List.length gcs = 1 then
    (* if number of global constant is one, then do not using loop. (optimize) *)
    [ apply_rule2 s p (List.hd gcs) ]
  else get_loop_appl s p x gcs

let const_unroll_with_loop (s : DUGIR.t) p ({ prim_info; _ } as info) =
  match s with
  | Const (_, _, (x, _)) -> (
      if is_primitive_from_id x then
        get_loop_appl s p x (get_value x prim_info |> sort_const)
      else
        match get_r2_with_loop s p info x with
        | [] ->
            if is_receiver (DUG.get_vinfo x |> snd) || not_null_obj x then
              raise Not_found_global_constant
            else get_r3 s p prim_info x
        | r2_with_loop ->
            if is_receiver (DUG.get_vinfo x |> snd) || not_null_obj x then
              r2_with_loop
            else List.rev_append (get_r3 s p prim_info x) r2_with_loop)
  | _ -> failwith "Fail: const_unroll_with_loop"

let const_unroll (s : DUGIR.t) p ({ prim_info; _ } as info) =
  match s with
  | Const (_, _, (x, _)) -> (
      if !Cmdline.with_loop then const_unroll_with_loop s p info
      else if is_primitive_from_id x then
        List.fold_left
          (fun lst x1 -> apply_rule1 s p x1 :: lst)
          [] (get_value x prim_info)
      else
        match get_r2 s p info x with
        | [] ->
            if is_receiver (DUG.get_vinfo x |> snd) || not_null_obj x then
              raise Not_found_global_constant
            else get_r3 s p prim_info x
        | r2 ->
            if is_receiver (DUG.get_vinfo x |> snd) || not_null_obj x then r2
            else List.rev_append (get_r3 s p prim_info x) r2)
  | _ -> failwith "Fail: const_unroll"

let fcall_in_assign_unroll (s : DUGIR.t) p obj_types
    { summary; m_info; t_info; c_info; setter_map; _ } =
  let apply_rule f arg field_set obj_map prec =
    ( prec,
      DUG.fcall_in_assign_rule s field_set f arg p.tc,
      empty_id_map,
      obj_map )
  in
  let set_object_type class_name child_name obj_types =
    match ObjTypeMap.M.find_opt class_name obj_types with
    | Some child when child = child_name -> Some obj_types
    | Some _ -> None
    | None -> Some (ObjTypeMap.M.add class_name child_name obj_types)
  in
  let apply_rule_for_all class_name field_set c_list =
    List.fold_left
      (fun lst (prec, (f, arg)) ->
        let child_name = Utils.get_class_name (DUG.get_func f).method_name in
        match set_object_type class_name child_name obj_types with
        | Some obj -> apply_rule f arg field_set obj prec :: lst
        | None -> lst)
      [] c_list
  in
  match s with
  | Assign (_, _, (x0, _, _, _)) ->
      let field_set = get_field_set x0 setter_map in
      let class_name = DUG.get_vinfo x0 |> fst |> get_class_name in
      let org_c_lst, c_lst, ret_c_lst =
        (* if class is special class, we don't use the methods returning that class type *)
        if List.mem class_name special_class_list then ([], [], [])
        else get_m_lst x0 m_info c_info
      in
      let c_lst = if org_c_lst = [] then c_lst else org_c_lst in
      if c_lst = [] && ret_c_lst = [] then raise Not_found_get_object
      else
        List.rev_append
          (get_c x0 c_lst summary m_info)
          (get_ret_c x0 ret_c_lst summary m_info t_info c_info setter_map)
        |> apply_rule_for_all class_name field_set
  | _ -> failwith "Fail: fcall_in_assign_unroll"

let recv_in_assign_unroll (prec, ((s : DUGIR.t), tc), loop_ids, obj_types)
    { m_info; c_info; _ } =
  match s with
  | Assign (_, _, (x0, _, f, arg)) when DUG.recv_in_assign s ->
      if
        is_nested_class (DUG.get_func f).import
        && is_static_class (DUG.get_func f).import c_info |> not
        && Utils.is_init_method (DUG.get_func f).method_name
      then (
        let recv, f, arg = get_inner_func f arg in
        if (DUG.get_v recv).import = "" then
          (* The import of the inner class function being empty means
             that the receiver is an empty variable *)
          []
        else
          let r2 = DUG.recv_in_assign_rule2_1 s recv f arg tc in
          let r3 = DUG.recv_in_assign_rule3_1 s recv f arg tc in
          incr outer;
          (prec, r2, loop_ids, obj_types) :: [ (prec, r3, loop_ids, obj_types) ])
      else if cname_condition (DUG.get_func f).method_name m_info c_info then
        [
          ( prec,
            DUG.recv_in_assign_rule1 s (get_cname f) tc,
            loop_ids,
            obj_types );
        ]
      else
        let r2 = DUG.recv_in_assign_rule2 s "con_recv" !recv tc in
        let r3 = DUG.recv_in_assign_rule3 s "con_recv" !recv tc in
        incr recv;
        let applied =
          (prec, r2, loop_ids, obj_types) :: [ (prec, r3, loop_ids, obj_types) ]
        in
        if DUG.is_already_node s (fst r2) tc then
          let found_node = DUG.find_node s (fst r2) tc in
          let found_id = DUG.get_id found_node in
          if is_matched_variable found_id x0 then
            let r4 = DUG.recv_in_assign_rule4 s found_node tc in
            (prec, r4, loop_ids, obj_types) :: applied
          else applied
        else applied
  | _ -> failwith "Fail: recv_in_assign_unroll"

let arg_in_assign_unroll (org_s, org_tc)
    (prec, ((s : DUGIR.t), tc), loop_ids, obj_types) =
  let apply_rule x args =
    ( prec,
      DUG.arg_in_assign_rule s x
        (Param (List.map (fun x -> DUG.get_v x) args))
        tc,
      loop_ids,
      obj_types )
  in
  match s with
  | Assign (num, _, (_, _, f, arg)) when DUG.arg_in_assign s ->
      let class_name = Utils.get_class_name (DUG.get_func f).method_name in
      mk_arg_seq arg num class_name org_s org_tc
      |> List.fold_left (fun lst (args, x) -> apply_rule x args :: lst) []
  | _ -> failwith "Fail: arg_in_assign_unroll"

let void_unroll (s : DUGIR.t) p =
  let void_rule2 var =
    List.fold_left
      (fun lst prev ->
        if DUG.check_assign var prev then
          let s', g' = DUG.void_rule2 prev s p.tc in
          if s' = s then lst
          else (0, (s', g'), empty_id_map, empty_obj_type_map) :: lst
        else lst)
      [] (DUG.pred s p.tc)
  in
  match s with
  | Stmt (_, var) ->
      (0, DUG.void_rule1 s p.tc, empty_id_map, empty_obj_type_map)
      :: void_rule2 var
  | _ -> failwith "Fail: void_unroll"

let fcall_in_void_unroll (s : DUGIR.t) p p_data =
  let apply_rule f arg prec =
    ( prec,
      DUG.fcall_in_void_rule s f (Arg arg) p.tc,
      empty_id_map,
      empty_obj_type_map )
  in
  match s with
  | Void (_, _, (x, _, _)) ->
      let lst = get_void_func x p_data in
      if lst = [] then raise Not_found_setter
      else
        List.fold_left
          (fun lst (prec, f, arg) -> apply_rule f arg prec :: lst)
          [] lst
  | _ -> failwith "Fail: fcall_in_void_unroll"

let recv_in_void_unroll (prec, ((s : DUGIR.t), tc), loop_ids, obj_types)
    { m_info; c_info; _ } =
  match s with
  | Void (_, _, (_, f, _)) when DUG.recv_in_void s ->
      if cname_condition (DUG.get_func f).method_name m_info c_info then
        [
          (prec, DUG.recv_in_void_rule1 s (get_cname f) tc, loop_ids, obj_types);
        ]
      else
        let r2 = DUG.recv_in_void_rule2 s "con_recv" !recv tc in
        let r3 = DUG.recv_in_void_rule3 s "con_recv" !recv tc in
        incr recv;
        (prec, r2, loop_ids, obj_types) :: [ (prec, r3, loop_ids, obj_types) ]
  | _ -> failwith "Fail: recv_in_void_unroll"

let arg_in_void_unroll (org_s, org_tc)
    (prec, ((s : DUGIR.t), tc), loop_ids, obj_types) =
  let apply_rule x args =
    ( prec,
      DUG.arg_in_void_rule s x (Param (List.map (fun x -> DUG.get_v x) args)) tc,
      loop_ids,
      obj_types )
  in
  match s with
  | Void (num, _, (_, f, arg)) when DUG.arg_in_void s ->
      let class_name = Utils.get_class_name (DUG.get_func f).method_name in
      mk_arg_seq arg num class_name org_s org_tc
      |> List.fold_left (fun lst (args, x) -> apply_rule x args :: lst) []
  | _ -> failwith "Fail: arg_in_void_unroll"

let apply_mock_rule s p =
  (0, DUG.mk_mock_statement s p.tc, empty_id_map, empty_obj_type_map)

let apply_recv_in_assign_rule_for_all p_data p_list =
  List.fold_left
    (fun acc_lst x -> recv_in_assign_unroll x p_data |> append acc_lst)
    [] p_list

let apply_arg_in_assign_rule_for_all s p p_list =
  List.fold_left
    (fun acc_lst x -> arg_in_assign_unroll (s, p.tc) x |> append acc_lst)
    [] p_list

let is_having_receiver p_list =
  (* at least receiver *)
  let filtered =
    List.filter (fun (_, (x, _), _, _) -> DUG.count_params x < 2) p_list
  in
  if filtered = [] then true else false

let one_unroll (s : DUGIR.t) p obj_types p_data =
  match s with
  | _ when DUG.void p.tc s -> void_unroll s p
  | Const _ when DUG.const s -> const_unroll s p p_data
  | Assign _ when DUG.fcall_in_assign s -> (
      (* fcall_in_assign --> recv_in_assign --> arg_in_assign *)
      match fcall_in_assign_unroll s p obj_types p_data with
      | exception Not_found_get_object ->
          if !Cmdline.mock then [ apply_mock_rule s p ]
          else raise Not_found_get_object
      | p_lst ->
          let lst =
            apply_recv_in_assign_rule_for_all p_data p_lst
            |> apply_arg_in_assign_rule_for_all s p
          in
          if !Cmdline.mock && is_having_receiver p_lst then
            apply_mock_rule s p :: lst
          else lst)
  | Void _ when DUG.fcall1_in_void s ->
      (* fcall1_in_void --> recv_in_void --> arg_in_void *)
      fcall_in_void_unroll s p p_data
      |> List.fold_left
           (fun acc_lst x -> recv_in_void_unroll x p_data |> append acc_lst)
           []
      |> List.fold_left
           (fun acc_lst x -> arg_in_void_unroll (s, p.tc) x |> append acc_lst)
           []
  | Void _ when DUG.fcall2_in_void s ->
      (* fcall2_in_void --> arg_in_void *)
      fcall_in_void_unroll s p p_data
      |> List.fold_left
           (fun acc_lst x -> arg_in_void_unroll (s, p.tc) x |> append acc_lst)
           []
  | Void _ when DUG.recv_in_void s ->
      (* unroll error entry *)
      recv_in_void_unroll
        (0, (s, p.tc), empty_id_map, empty_obj_type_map)
        p_data
      |> List.fold_left
           (fun acc_lst x -> arg_in_void_unroll (s, p.tc) x |> append acc_lst)
           []
  | _ -> failwith "Fail: one_unroll"

let rec all_unroll ?(assign_ground = false) p obj_types p_data stmt_map =
  G.fold_vertex
    (fun stmt map ->
      all_unroll_assign ~assign_ground stmt p obj_types p_data map)
    p.tc stmt_map

and all_unroll_assign ?(assign_ground = false) s p obj_types p_data stmt_map =
  match s with
  | _ when DUG.ground_stmt s -> stmt_map
  | _ when assign_ground -> all_unroll_void s p obj_types p_data stmt_map
  | _ when DUG.is_stmt s && not assign_ground -> stmt_map
  | _ -> StmtMap.M.add s (one_unroll s p obj_types p_data) stmt_map

and all_unroll_void s p obj_types p_data stmt_map =
  match s with
  | _ when DUG.ground_stmt s -> stmt_map
  | _ when DUG.void p.tc s ->
      StmtMap.M.add s (one_unroll s p obj_types p_data) stmt_map
  | _ -> failwith "Fail: all_unroll_void"

let return_stmts graph =
  let is_grounded assign_ground s =
    match (s : DUGIR.t) with
    | _ when DUG.ground_stmt s -> true (* ground check of partial tc is first *)
    | Stmt _ when not assign_ground -> true
    | _ -> false
  in
  let decide_void_unroll = DUG.ground graph |> not && DUG.assign_ground graph in
  G.fold_vertex
    (fun n set ->
      if is_grounded decide_void_unroll n then set else ReturnStmtSet.add n set)
    graph ReturnStmtSet.empty

let to_list set =
  ReturnStmtSet.fold (fun stmt lst -> stmt :: lst) set [] |> List.rev

let sort_stmts map stmts =
  List.stable_sort
    (fun s1 s2 ->
      match (StmtMap.M.find_opt s1 map, StmtMap.M.find_opt s2 map) with
      | Some l1, Some l2 -> compare (List.length l1) (List.length l2)
      | Some _, None -> 1
      | None, Some _ -> -1
      | None, None -> 0)
    stmts

let combinate_stmt (p', tc', loop_ids', obj_types') s new_s_list =
  List.fold_left
    (fun lst (new_p, (new_s, new_tc), new_loop, new_type) ->
      ( p' + new_p,
        DUG.replace_and_union s new_s tc' new_tc,
        loop_id_merge loop_ids' new_loop,
        obj_type_merge obj_types' new_type )
      :: lst)
    [] new_s_list

let combinate_stmts s new_s_lst partial_lst =
  List.fold_left
    (fun l _p -> combinate_stmt _p s new_s_lst |> append l)
    [] partial_lst

let combinate { prec; tc; loop_ids; obj_types; _ } stmt_map =
  (* stmts is all fragments of statements in partial tc *)
  let all_combinate stmts =
    List.fold_left
      (fun lst s ->
        match StmtMap.M.find_opt s stmt_map with
        | Some new_s_list when new_s_list = [] ->
            (* Because these will be never grounded, remove all *)
            []
        | Some new_s_list -> combinate_stmts s new_s_list lst
        | _ -> lst)
      [ (prec, tc, loop_ids, obj_types) ]
      stmts
  in
  return_stmts tc |> to_list |> sort_stmts stmt_map |> all_combinate |> List.rev

(* get methods that calling error method *)
let rec get_caller_methods e_method p_data =
  let org_caller_list =
    try CG.succ p_data.cg e_method |> List.filter (fun x -> x <> e_method)
    with Invalid_argument _ -> []
  in
  let class_name = Utils.get_class_name e_method in
  if org_caller_list = [] then
    (try IG.pred (snd p_data.c_info) class_name with Invalid_argument _ -> [])
    |> get_parent_caller_method e_method class_name p_data
  else org_caller_list

and get_parent_caller_method e_method class_name p_data parent_types =
  let get_caller_list m_name =
    try
      CG.succ p_data.cg m_name
      |> List.filter (fun x -> x <> m_name && x <> e_method)
    with Invalid_argument _ -> []
  in
  let escaped_m_name =
    Str.global_replace Regexp.dot "\\." class_name
    |> Str.global_replace Regexp.dollar "\\$"
  in
  let new_m_name c_name =
    Str.replace_first (Str.regexp escaped_m_name) c_name e_method
  in
  List.fold_left
    (fun acc c_name ->
      List.rev_append (get_caller_list (new_m_name c_name)) acc)
    [] parent_types

(* find error entry *)
let rec find_ee e_method e_summary p_data =
  if
    is_public e_method p_data.m_info || is_usable_default e_method p_data.m_info
  then ErrorEntrySet.add (e_method, e_summary) ErrorEntrySet.empty
  else
    List.fold_left
      (fun set caller_method ->
        (match
           CallPropMap.M.find_opt (caller_method, e_method) p_data.cp_map
         with
        | None ->
            (* It is possible without any specific conditions *)
            find_ee caller_method empty_summary p_data
        | Some prop_list ->
            traverse_all_prop_list e_method e_summary caller_method prop_list
              p_data)
        |> ErrorEntrySet.union set)
      ErrorEntrySet.empty
      (get_caller_methods e_method p_data)

and traverse_all_prop_list e_method e_summary caller_method prop_list p_data =
  List.fold_left
    (fun caller_preconds call_prop ->
      if ExploredMethod.mem caller_method !explored_m then
        (* if the caller method is included in the error entry set,
             avoiding duplicate calculation *)
        caller_preconds
      else (
        explored_m := ExploredMethod.add caller_method !explored_m;
        propagation e_method e_summary caller_method caller_preconds call_prop
          p_data))
    ErrorEntrySet.empty prop_list

(* propagate error condition to caller method *)
and propagation e_method e_summary caller_method caller_preconds call_prop
    p_data =
  let new_value, new_mem, check_match =
    try satisfy e_method e_summary call_prop p_data.m_info
    with _ ->
      Logger.info
        "Given wrong summary of error method! So, the \"find_ee\" step \
         progresses using a temporary summary";
      let tmp_summary = get_first_summary e_method p_data.summary in
      let use_summary = if tmp_summary = empty_summary then false else true in
      (tmp_summary.value, snd tmp_summary.precond, use_summary)
  in
  let new_uf = mk_new_uf e_method e_summary call_prop p_data.m_info in
  if !Cmdline.basic_mode then
    ErrorEntrySet.union caller_preconds
      (find_ee caller_method empty_summary p_data)
  else if !Cmdline.pruning_mode then
    ErrorEntrySet.union caller_preconds (find_ee caller_method call_prop p_data)
  else if check_match then
    let new_call_prop =
      new_value_summary new_value call_prop
      |> new_mem_summary new_mem |> new_uf_summary new_uf
    in
    ErrorEntrySet.union caller_preconds
      (find_ee caller_method new_call_prop p_data)
  else caller_preconds

let stmt_import (s : DUGIR.t) set =
  match s with
  | Const (_, _, (x, _)) -> add_import (DUG.get_v x).import set
  | Assign (_, _, (x0, _, f, arg)) ->
      List.fold_left
        (fun s (a : DUGIR.var) -> add_import a.import s)
        set (DUG.get_param arg)
      |> add_import (DUG.get_v x0).import
      |> add_import (DUG.get_func f).import
  | Void (_, _, (_, f, arg)) ->
      List.fold_left
        (fun s (a : DUGIR.var) -> add_import a.import s)
        set (DUG.get_param arg)
      |> add_import (DUG.get_func f).import
  | _ -> set

let pretty_format tc =
  let imports =
    DUG.fold_vertex (fun s set -> stmt_import s set) tc ImportSet.empty
  in
  (imports, DUG.topological_code tc)

let priority_q queue =
  List.stable_sort
    (fun p1 p2 ->
      let nt1, t1, prec1 = get_cost p1 in
      let nt2, t2, prec2 = get_cost p2 in
      if compare (nt1 + t1 - prec1) (nt2 + t2 - prec2) <> 0 then
        compare (nt1 + t1 - prec1) (nt2 + t2 - prec2)
      else if compare prec1 prec2 <> 0 then compare prec2 prec1
      else compare nt1 nt2)
    queue

let rec mk_testcase p_data queue =
  let queue =
    if !Cmdline.basic_mode || !Cmdline.pruning_mode then queue
    else priority_q queue
  in
  if !Cmdline.debug then Logger.info "# of test cases: %d" (List.length queue);
  match queue with
  | p :: tl ->
      if !Cmdline.debug then
        Logger.info "current tc:\n%s" (pretty_format p.tc |> snd);
      if !Cmdline.with_loop && DUG.ground p.tc && DUG.with_withloop p.tc then
        [ (Need_Loop, pretty_format p.tc, p.loop_ids, tl) ]
      else if DUG.ground p.tc then
        [ (Complete, pretty_format p.tc, p.loop_ids, tl) ]
      else
        (match
           all_unroll ~assign_ground:(DUG.assign_ground p.tc) p p.obj_types
             p_data StmtMap.M.empty
         with
        | exception Not_found_setter ->
            if !Cmdline.debug then
              Logger.info "Exception: not found setter in %s"
                (pretty_format p.tc |> snd);
            tl
        | exception Not_found_get_object ->
            if !Cmdline.debug then
              Logger.info "Exception: not found get object in %s"
                (pretty_format p.tc |> snd);
            tl
        | exception Not_found_global_constant ->
            if !Cmdline.debug then
              Logger.info "Exception: not found global constant in %s"
                (pretty_format p.tc |> snd);
            tl
        | x ->
            List.fold_left
              (fun lst (new_p, new_tc, new_loop, new_type) ->
                mk_cost p new_tc new_loop new_type new_p :: lst)
              [] (combinate p x)
            |> List.rev_append (List.rev tl))
        |> mk_testcase p_data
  | [] -> []

let apply_init_rule list =
  let start_node = DUGIR.Void (0, (This NonType, None), (Id, Func, Arg [])) in
  let empty_graph = DUG.add_vertex start_node DUG.empty in
  List.fold_left
    (fun lst (_, f, arg) ->
      DUG.fcall_in_void_rule start_node f (DUGIR.Arg arg) empty_graph :: lst)
    [] list

let init_cost tcs =
  List.fold_left
    (fun lst (_, new_tc) ->
      mk_cost empty_p new_tc empty_id_map empty_obj_type_map 0 :: lst)
    [] tcs

let mk_testcases ~is_start queue (e_method, error_summary) p_data =
  let p_info, init =
    if is_start then (
      set_methods_to_ignore p_data.m_info p_data.c_info p_data.cp_map;
      ErrorEntrySet.fold
        (fun (ee, ee_s) (p_info_init, init_list) ->
          if !Cmdline.debug then Logger.info "error entry method: %s" ee;
          ( Constant.expand_string_value ee p_info_init,
            apply_init_rule (get_void_func DUGIR.Id ~ee ~es:ee_s p_data)
            |> init_cost |> List.rev_append init_list ))
        (find_ee e_method error_summary p_data)
        (p_data.prim_info, []))
    else (p_data.prim_info, queue)
  in
  let result = mk_testcase (update_prim p_data p_info) init in
  if result = [] then (Incomplete, (ImportSet.empty, ""), empty_id_map, [])
  else List.hd result
