open Language
open Generator
open Ast
module CG = Callgraph.G
module IG = Inheritance.G
module ImportSet = Utils.ImportSet

module TypeSet = Set.Make (struct
  type t = string [@@deriving compare]
end)

module VarSet = Set.Make (struct
  type t = variable [@@deriving compare]
end)

(* Set of VarSet *)
module VarSets = Set.Make (VarSet)

module VarListSet = Set.Make (struct
  type t = ASTIR.var list

  let compare = compare
end)

module StmtMap = struct
  module M = Map.Make (struct
    type t = ASTIR.t

    let compare = compare
  end)

  type t = ASTIR.t list M.t
end

module ObjTypeMap = struct
  module M = Map.Make (struct
    type t = string [@@deriving compare]
  end)

  type t = string M.t
end

type partial_tc = {
  unroll : int;
  nt_cost : int;
  t_cost : int;
  prec : int; (* number of precise statement *)
  tc : ASTIR.t;
  loop_ids : LoopIdMap.t;
  obj_types : ObjTypeMap.t;
}

(* non-terminal cost for p, terminal cost for p, precision for p *)
let get_cost p =
  if p.unroll > 1 then (p.nt_cost, p.t_cost, p.prec) else (0, 0, 0)

let mk_cost prev_p curr_tc curr_loop_id curr_obj_type prec =
  {
    unroll = prev_p.unroll + 1;
    nt_cost = AST.count_nt curr_tc;
    t_cost = AST.count_t curr_tc;
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
    tc = ASTIR.Skip;
    loop_ids = empty_id_map;
    obj_types = empty_obj_type_map;
  }

let is_string x =
  match AST.get_vinfo x |> fst with String -> true | _ -> false

let is_primitive x =
  match AST.get_vinfo x |> fst with
  | Int | Long | Short | Byte | Float | Double | Bool | Char | String -> true
  | _ -> false

let is_primitive_from_v v =
  match get_type (fst v.ASTIR.variable) with
  | Int | Long | Short | Byte | Float | Double | Bool | Char | String -> true
  | _ -> false

let get_m_lst x0 m_info (c_info, ig) =
  let class_name = AST.get_vinfo x0 |> fst |> get_class_name in
  let class_to_find =
    try IG.succ ig class_name |> List.cons class_name
    with Invalid_argument _ -> [ class_name ]
  in
  MethodInfo.M.fold
    (fun m_name _ method_list ->
      List.fold_left
        (fun (org_c_lst, c_lst, ret_c_lst) class_name_to_find ->
          if
            (is_public_class (Utils.get_class_name m_name) c_info
            || is_usable_default_class (Utils.get_class_name m_name) c_info)
            && is_available_method m_name m_info
          then
            if
              is_abstract_class class_name_to_find (c_info, ig) |> not
              && match_constructor_name class_name_to_find m_name
            then
              if class_name = class_name_to_find then
                (m_name :: org_c_lst, m_name :: c_lst, ret_c_lst)
              else (org_c_lst, m_name :: c_lst, ret_c_lst)
            else if
              match_return_object class_name_to_find m_name m_info
              && is_abstract_method m_name class_to_find m_info (c_info, ig)
                 |> not
              && Utils.is_init_method m_name |> not
            then (org_c_lst, c_lst, m_name :: ret_c_lst)
            else (org_c_lst, c_lst, ret_c_lst)
          else (org_c_lst, c_lst, ret_c_lst))
        method_list class_to_find)
    m_info ([], [], [])

let is_new_loc_field field summary =
  let is_null symbol =
    match Value.M.find_opt symbol summary.value with
    | Some x when x.Value.value = Eq Null -> true
    | _ -> false
  in
  let is_new_loc x =
    match x with
    | Condition.RH_Symbol _
      when is_null (get_rh_name x) |> not
           && contains_symbol x (snd summary.precond) |> not ->
        true
    | _ -> false
  in
  let is_new_loc_mem m =
    Condition.M.fold
      (fun _ x check -> if check || is_new_loc x then true else check)
      m false
  in
  let post_var, post_mem = summary.postcond in
  let field_var = get_id_symbol post_var field in
  match Condition.M.find_opt field_var post_mem with
  | None -> false
  | Some m -> is_new_loc_mem m

let ret_fld_name_of summary =
  let collect_field mem full_mem =
    Condition.M.fold
      (fun field symbol acc_lst ->
        match field with
        | Condition.RH_Var v ->
            (v, get_tail_symbol "" symbol full_mem) :: acc_lst
        | _ -> acc_lst)
      mem []
  in
  let pre_var, pre_mem = summary.precond in
  let this_var = get_id_symbol pre_var "this" in
  let candidate_fields =
    match Condition.M.find_opt (get_next_symbol this_var pre_mem) pre_mem with
    | Some m -> collect_field m pre_mem
    | _ -> []
  in
  let post_var, post_mem = summary.postcond in
  let return_var = get_id_symbol post_var "return" in
  let return_tail_symbol = get_tail_symbol "" return_var post_mem in
  let field_name =
    List.fold_left
      (fun found (field, sym) ->
        if sym = return_tail_symbol then field else found)
      "" candidate_fields
  in
  field_name

let is_getter_with_memory_effect m_summary fld_name =
  (* If the field name is empty, it indicates that the method doesn't return its field,
     so it should not be pruned for safety *)
  let new_loc = is_new_loc_field "return" m_summary in
  (fld_name = "" && not new_loc) || new_loc

let collect_recv m_info (ret_type, m_type) c_info s_map subtypes =
  let is_available_class typ c_info =
    match ClassInfo.M.find_opt typ c_info with
    | Some t -> (
        match t.ClassInfo.class_type with
        | Public | Public_Static -> true
        | _ -> false)
    | _ -> true
  in
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
    (try ReturnType.M.find typ ret_type with _ -> [])
    |> List.fold_left
         (fun lst x -> if cond_common typ x then x :: lst else lst)
         []
  in
  let get_c_list typ =
    (try MethodType.M.find typ m_type with _ -> [])
    |> List.fold_left (fun lst x -> if cond_c typ x then x :: lst else lst) []
  in
  let get_s_list typ =
    (try SetterMap.M.find typ s_map with _ -> [])
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

let calc_z3 id z3exp =
  let solver = Z3.Solver.mk_solver z3ctx None in
  Z3.Solver.add solver z3exp;
  let _ = Z3.Solver.check solver [] in
  match Z3.Solver.get_model solver with
  | Some m -> (
      let value = Z3.Model.eval m id false in
      match value with
      | Some v ->
          if Z3.Arithmetic.is_real v then Z3.Arithmetic.Real.numeral_to_string v
          else Z3.Arithmetic.Integer.numeral_to_string v
      | None -> "")
  | None -> ""

let get_predef_value_list typ p_info =
  match PrimitiveInfo.TypeMap.find_opt typ p_info with
  | Some map -> (
      match PrimitiveInfo.ClassMap.find_opt "" map with
      | Some value -> value
      | _ -> [ "NULL" ])
  | _ -> [ "NULL" ]

let get_extra_value_list typ import p_info =
  match PrimitiveInfo.TypeMap.find_opt typ p_info with
  | Some map -> (
      let file = Regexp.first_rm (Str.regexp "\\$.*$") import in
      match
        ( PrimitiveInfo.ClassMap.find_opt import map,
          PrimitiveInfo.ClassMap.find_opt file map )
      with
      | Some value, _ -> value
      | None, Some value -> value
      | _, _ -> [])
  | _ -> []

let default_value_list typ import p_info =
  let predef = get_predef_value_list typ p_info in
  let extra = get_extra_value_list typ import p_info in
  let lst = List.rev_append predef extra in
  match typ with
  | Int | Long | Short | Byte ->
      let f acc x =
        match int_of_string_opt x with
        | Some i -> ASTIR.Primitive (Z i) :: acc
        | _ -> acc
      in
      List.fold_left f [] lst
  | Float | Double ->
      let f acc x =
        match float_of_string_opt x with
        | Some i -> ASTIR.Primitive (R i) :: acc
        | _ -> acc
      in
      List.fold_left f [] lst
  | Bool ->
      let f acc x =
        match bool_of_string_opt x with
        | Some i -> ASTIR.Primitive (B i) :: acc
        | _ -> acc
      in
      List.fold_left f [] lst
  | Char ->
      let f acc x =
        if String.length x = 1 then ASTIR.Primitive (C x.[0]) :: acc else acc
      in
      List.fold_left f [] lst
  | String ->
      (* String constant is already expanded when finding error entries *)
      let f acc x =
        if List.mem (ASTIR.Primitive (S x)) acc then acc
        else if x = "NULL" then ASTIR.Null :: acc
        else ASTIR.Primitive (S x) :: acc
      in
      List.fold_left f [] predef
  | _ ->
      let f acc x = if x = "NULL" then ASTIR.Null :: acc else acc in
      List.fold_left f [] lst

let not_found_value v =
  match v.Value.value with Value.Eq NonValue -> true | _ -> false

let calc_value_list from_error org_list default =
  (* default value have a penalty *)
  let prec = if from_error then -2 else 0 in
  List.fold_left (fun lst x -> (prec, x) :: lst) org_list default

let filter_size id lst =
  if id = "size" || id = "index" || id = "capacity" then
    List.filter
      (fun x -> match snd x with ASTIR.Primitive (Z x) -> x >= 0 | _ -> false)
      lst
  else lst

let get_z3_val (v : Value.const) =
  match v with
  | Int i | Long i | Short i | Byte i ->
      Z3.Arithmetic.Integer.mk_numeral_i z3ctx i
  | Float f | Double f ->
      Z3.Arithmetic.Real.mk_numeral_s z3ctx (string_of_float f)
  | _ -> failwith "not implemented other number"

let get_z3_id (v : Value.const) id =
  match v with
  | Int _ | Long _ | Short _ | Byte _ ->
      Z3.Arithmetic.Integer.mk_const_s z3ctx id
  | Float _ | Double _ -> Z3.Arithmetic.Real.mk_const_s z3ctx id
  | _ -> failwith "not implemented other number"

let get_z3_result (op : Value.op) id =
  match op with
  | Eq v ->
      let var = get_z3_id v id in
      calc_z3 var [ Z3.Boolean.mk_eq z3ctx var (get_z3_val v) ]
  | Neq v ->
      let var = get_z3_id v id in
      calc_z3 var
        [ Z3.Boolean.mk_eq z3ctx var (get_z3_val v) |> Z3.Boolean.mk_not z3ctx ]
  | Le v ->
      let var = get_z3_id v id in
      calc_z3 var [ Z3.Arithmetic.mk_le z3ctx var (get_z3_val v) ]
  | Lt v ->
      let var = get_z3_id v id in
      calc_z3 var [ Z3.Arithmetic.mk_lt z3ctx var (get_z3_val v) ]
  | Ge v ->
      let var = get_z3_id v id in
      calc_z3 var [ Z3.Arithmetic.mk_ge z3ctx var (get_z3_val v) ]
  | Gt v ->
      let var = get_z3_id v id in
      calc_z3 var [ Z3.Arithmetic.mk_gt z3ctx var (get_z3_val v) ]
  | Between (v1, v2) ->
      let var = get_z3_id v1 id in
      calc_z3 var
        [
          Z3.Arithmetic.mk_ge z3ctx var (get_z3_val v1);
          Z3.Arithmetic.mk_le z3ctx var (get_z3_val v2);
        ]
  | Outside (v1, v2) ->
      let var = get_z3_id v1 id in
      calc_z3 var
        [
          Z3.Arithmetic.mk_lt z3ctx var (get_z3_val v1);
          Z3.Arithmetic.mk_gt z3ctx var (get_z3_val v2);
        ]

let calc_value id value default =
  let prec = if value.Value.from_error then 2 else 0 in
  let calc_int result =
    match int_of_string_opt result with
    | Some i ->
        calc_value_list value.Value.from_error
          [ (prec, ASTIR.Primitive (Z i)) ]
          default
        |> filter_size id
    | _ -> calc_value_list false [] default |> filter_size id
  in
  let calc_float result =
    match float_of_string_opt result with
    | Some f ->
        calc_value_list value.Value.from_error
          [ (prec, ASTIR.Primitive (R f)) ]
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
            [ (prec, ASTIR.Primitive (B b)) ]
            default
      | Char c ->
          calc_value_list value.Value.from_error
            [ (prec, ASTIR.Primitive (C c)) ]
            default
      | String s ->
          calc_value_list value.Value.from_error
            [ (prec, ASTIR.Primitive (S s)) ]
            default
      | Null -> [ (prec, ASTIR.Null) ]
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
            [ (prec, ASTIR.Primitive (B (not b))) ]
            default
      | String s ->
          calc_value_list value.Value.from_error
            [ (prec, ASTIR.Primitive (S ("not_" ^ s))) ]
            default
      | Null ->
          (* Among the const, only the string can be defined as null *)
          List.fold_left
            (fun lst x ->
              if x = ASTIR.Null then (-prec, x) :: lst else (prec, x) :: lst)
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

let find_value_from_variable memory value target_variable =
  let target_variable =
    Condition.M.fold
      (fun symbol symbol_trace find_variable ->
        let symbol = get_rh_name symbol in
        if symbol = target_variable then
          Condition.M.fold
            (fun _ trace_tl trace_find_var ->
              match trace_tl with
              | Condition.RH_Symbol s -> s
              | _ -> trace_find_var)
            symbol_trace find_variable
        else find_variable)
      memory target_variable
  in
  Value.M.fold
    (fun symbol value find_value ->
      if symbol = target_variable then value else find_value)
    value
    Value.{ from_error = false; value = Value.Eq NonValue }

let find_target_value id { precond = pre_var, pre_mem; value; _ } =
  Condition.M.fold
    (fun symbol variable find_variable ->
      match variable with
      | Condition.RH_Var var when var = id -> (
          match symbol with Condition.RH_Symbol s -> s | _ -> find_variable)
      | _ -> find_variable)
    pre_var ""
  |> find_value_from_variable pre_mem value

let find_target_value_from_this id summary =
  let this_sym default =
    match
      Condition.M.find_opt
        (org_symbol "this" summary |> mk_symbol)
        (snd summary.precond)
    with
    | Some this_mem ->
        Condition.M.fold
          (fun field symbol find_variable ->
            match field with
            | Condition.RH_Var v when v = id -> get_rh_name symbol
            | _ -> find_variable)
          this_mem default
    | _ -> default
  in
  this_sym "" |> find_value_from_variable (snd summary.precond) summary.value

let get_value v p_info =
  let typ, id = AST.get_vinfo v in
  let find_value1 = find_target_value id (AST.get_v v).summary in
  let find_value2 = find_target_value_from_this id (AST.get_v v).summary in
  let default =
    if !Cmdline.with_fuzz then [ ASTIR.WithFuzz ]
    else default_value_list typ (AST.get_v v).import p_info
  in
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
  if !Cmdline.with_fuzz then
    let null_exists lst =
      List.fold_left
        (fun exist (_, value) -> if value = ASTIR.Null then true else exist)
        false lst
    in
    if typ = String && not (null_exists found_value) then
      (* fuzzer can not generate a null value, so add a null value if needed *)
      (0, ASTIR.Null) :: found_value
    else found_value
  else found_value

let get_array_size array summary =
  let _, memory = summary.precond in
  let array_symbol = org_symbol array summary in
  match Condition.M.find_opt (mk_symbol array_symbol) memory with
  | Some x -> (true, Condition.M.fold (fun _ _ size -> size + 1) x 0)
  | None -> (false, 1)

let get_same_type_param params (_, _) =
  let get_type p = match p with Var (t, _) -> t | _ -> NonType in
  let mk_new_set p =
    let t1 = get_type p in
    List.fold_left
      (fun set op_p ->
        let t2 = get_type op_p in
        if t1 = t2 && get_type p <> NonType then VarSet.add op_p set else set)
      (VarSet.add p VarSet.empty)
      params
  in
  List.fold_left
    (fun sets p -> VarSets.add (mk_new_set p) sets)
    VarSets.empty params

let get_same_precond_param summary param_sets =
  VarSets.fold
    (fun set sets ->
      let filter_singleton set =
        if VarSet.cardinal set < 2 then VarSet.empty else set
      in
      let get_p_value p s =
        match p with
        | Var (_, id) -> find_target_value id s
        | _ -> failwith "Fail: find the target value"
      in
      let new_set =
        VarSet.fold
          (fun p new_set ->
            let v = get_p_value p summary in
            VarSet.fold
              (fun op_p new_set ->
                if v = get_p_value op_p summary then VarSet.add op_p new_set
                else new_set)
              set (VarSet.add p new_set))
          set VarSet.empty
        |> filter_singleton
      in
      VarSets.add new_set sets)
    param_sets VarSets.empty
  |> VarSets.filter (fun x -> VarSet.is_empty x |> not)

let get_same_params_set summary params c_info =
  let new_p = List.fold_left (fun p v -> v :: p) [] params |> List.rev in
  get_same_type_param new_p c_info |> get_same_precond_param summary

let satisfied_c m_summary id candidate_constructor summary =
  let c_summaries, _ = SummaryMap.M.find candidate_constructor summary in
  let target_symbol =
    get_target_symbol (if is_receiver id then "this" else id) m_summary
    |> get_rh_name
  in
  if target_symbol = "" then [ (true, List.hd c_summaries) ]
  else
    let meet lst c_summary =
      ( [
          ( find_relation target_symbol m_summary.relation,
            get_id_symbol (fst c_summary.postcond) "this" |> get_rh_name );
        ]
        |> check_intersect ~is_init:true m_summary c_summary,
        c_summary )
      :: lst
    in
    let sat lst (check_summary, c_summary) =
      if List.filter (fun (_, c) -> c = false) check_summary = [] then
        ( true,
          c_summary
          |> new_value_summary (combine_value c_summary.value check_summary) )
        :: lst
      else (false, c_summary) :: lst
    in
    List.fold_left meet [] c_summaries |> List.fold_left sat []

let find_class_file =
  List.fold_left
    (fun gvar_list const ->
      (0, ASTIR.GlobalConstant (const ^ ".class")) :: gvar_list)
    []
    [ "UnitconInterface"; "UnitconEnum" ]

let find_enum_var_list c_name i_info =
  match InstanceInfo.M.find_opt c_name i_info with
  | None -> []
  | Some info ->
      List.fold_left
        (fun gvar_list const ->
          (0, ASTIR.GlobalConstant (c_name ^ "." ^ const)) :: gvar_list)
        [] info

let all_global_var c_name s_trace =
  Condition.M.fold
    (fun head _ gvar_list ->
      match head with
      | Condition.RH_Var var ->
          (0, ASTIR.GlobalConstant (AST.get_short_class_name c_name ^ "." ^ var))
          :: gvar_list
      | _ -> gvar_list)
    s_trace []

let compare_global_var c_name t_var s_trace =
  Condition.M.fold
    (fun head _ gvar ->
      match head with
      | Condition.RH_Var var when var = t_var ->
          AST.get_short_class_name c_name ^ "." ^ var |> mk_some
      | _ -> gvar)
    s_trace None

let find_global_var_list c_name t_var mem summary m_info =
  let get_compared_global_var v init_summary var_lst =
    let new_gvar gv =
      (is_from_error false (List.hd init_summary), ASTIR.GlobalConstant gv)
    in
    (Condition.M.fold (fun _ s_trace list ->
         match compare_global_var c_name v s_trace with
         | Some gv -> new_gvar gv :: list
         | None -> list))
      mem var_lst
  in
  SummaryMap.M.fold
    (fun init_name (init_summary, _) list ->
      let _, init_mem = (List.hd init_summary).precond in
      if
        Str.string_match (c_name ^ "\\.<clinit>" |> Str.regexp) init_name 0
        && (is_public init_name m_info || is_usable_default init_name m_info)
      then
        match t_var with
        | Some v ->
            get_compared_global_var v init_summary list
            |> (Condition.M.fold (fun _ s_trace list ->
                    List.rev_append (all_global_var c_name s_trace) list))
                 init_mem
        | None ->
            (Condition.M.fold (fun _ s_trace list ->
                 List.rev_append (all_global_var c_name s_trace) list))
              init_mem list
      else list)
    summary []

let find_target_var sym_trace find_var =
  Condition.M.fold
    (fun trace_hd _ trace_find_var ->
      match trace_hd with
      | Condition.RH_Var var -> mk_some var
      | _ -> trace_find_var)
    sym_trace find_var

let get_target_var t_sym mem =
  Condition.M.fold
    (fun symbol symbol_trace find_variable ->
      if get_rh_name symbol = t_sym then
        find_target_var symbol_trace find_variable
      else find_variable)
    mem None

let global_var_list class_name t_summary summary m_info i_info =
  let vars, mem = t_summary.precond in
  let t_var =
    Condition.M.fold
      (fun symbol var find_var ->
        match var with
        | Condition.RH_Var var ->
            if Str.string_match (".*\\." ^ class_name |> Str.regexp) var 0 then
              get_rh_name symbol |> mk_some
            else find_var
        | _ -> find_var)
      vars None
  in
  match t_var with
  | None ->
      if class_name = "java.lang.Class" then find_class_file
      else
        let gvlist = find_global_var_list class_name None mem summary m_info in
        if gvlist = [] then find_enum_var_list class_name i_info else gvlist
  | Some x ->
      find_global_var_list class_name (get_target_var x mem) mem summary m_info

let get_symbol_num symbol =
  match
    Regexp.first_rm Regexp.symbol (get_rh_name symbol) |> int_of_string_opt
  with
  | Some i -> i
  | _ -> 0

let get_fresh_num prev_num = prev_num + 1

let n_forward n start start_map =
  let key_compare k1 k2 =
    match (k1, k2) with
    | Condition.RH_Symbol _, Condition.RH_Symbol _ ->
        get_symbol_num k1 < get_symbol_num k2
    | _ -> false
  in
  let collect_key org_key map =
    Condition.M.fold
      (fun field k lst ->
        if key_compare org_key k then (org_key, field, k) :: lst else lst)
      map []
  in
  let find_key key map =
    match Condition.M.find_opt key map with
    | Some value -> collect_key key value
    | _ -> []
  in
  let rec forwards count key_list =
    if count >= n then key_list
    else
      let keys =
        List.fold_left
          (fun lst (_, _, k) -> find_key k start_map |> List.rev_append lst)
          [] key_list
      in
      forwards (count + 1) keys
  in
  forwards 1 (find_key start start_map)

let check_new_value symbol vmap memory =
  let checker mem =
    Condition.M.fold
      (fun field value check ->
        match
          Value.M.find_opt
            (get_field_symbol field value memory |> get_rh_name)
            vmap
        with
        | Some _ -> true
        | _ -> check)
      mem false
  in
  match Condition.M.find_opt symbol memory with
  | Some x -> checker x
  | _ -> false

let add_new_mmap f1 f2 org_key field map =
  match Condition.M.find_opt org_key map with
  | Some x ->
      Condition.M.add org_key
        (Condition.M.add (get_rh_name ~is_var:true field |> mk_var) f1 x)
        map
      |> Condition.M.add f1 (Condition.M.add RH_Any f2 Condition.M.empty)
  | _ ->
      Condition.M.add org_key
        (Condition.M.add
           (get_rh_name ~is_var:true field |> mk_var)
           f1 Condition.M.empty)
        map
      |> Condition.M.add f1 (Condition.M.add RH_Any f2 Condition.M.empty)

let mk_new_memory org_key t_key_lst t_summary new_mem =
  let func (sym, value, new_pre_mem, new_post_mem) (_, field, key) =
    let field_name = get_rh_name ~is_var:true field in
    if field_name = "" then (sym, value, new_pre_mem, new_post_mem)
    else
      let fn1 = get_fresh_num 1 in
      let fn2 = get_fresh_num fn1 in
      let fv1 = string_of_int fn1 |> String.cat "u" |> mk_symbol in
      let fv2 = string_of_int fn2 |> String.cat "u" |> mk_symbol in
      let new_value =
        try
          Value.M.find
            (get_tail_symbol "" key (snd t_summary.precond) |> get_rh_name)
            t_summary.value
        with _ -> value
      in
      let new_pre_mem = add_new_mmap fv1 fv2 org_key field new_pre_mem in
      let new_post_mem = add_new_mmap fv1 fv2 org_key field new_post_mem in
      (fv2, new_value, new_pre_mem, new_post_mem)
  in
  List.fold_left func new_mem t_key_lst

let rec forward count var_symbol this_symbol t_summary c_summary new_memory =
  let t_key_list = n_forward count var_symbol (snd t_summary.precond) in
  let c_key_list = n_forward count this_symbol (snd c_summary.postcond) in
  if t_key_list = [] then new_memory
  else if List.length t_key_list = List.length c_key_list then
    forward (count + 1) var_symbol this_symbol t_summary c_summary new_memory
  else
    let c_org_key =
      if count = 1 then this_symbol
      else
        let c_org_key, _, _ =
          n_forward (count - 1) this_symbol (snd c_summary.postcond) |> List.hd
        in
        c_org_key
    in
    mk_new_memory c_org_key t_key_list t_summary new_memory

let modify_summary id t_summary c_summary =
  let id = if id = "con_recv" then "this" else id in
  let var_symbol = org_symbol id t_summary |> mk_symbol in
  let this_symbol = org_symbol "this" c_summary |> mk_symbol in
  if check_new_value var_symbol t_summary.value (snd t_summary.precond) |> not
  then c_summary
  else
    let default_value = Value.{ from_error = false; value = Eq NonValue } in
    let symbol, value, pre_mem, post_mem =
      forward 1 var_symbol this_symbol t_summary c_summary
        (RH_Any, default_value, snd c_summary.precond, snd c_summary.postcond)
    in
    {
      relation = c_summary.relation;
      value =
        (if value = default_value then c_summary.value
         else Value.M.add (get_rh_name symbol) value c_summary.value);
      use_field = c_summary.use_field;
      precond = (fst c_summary.precond, pre_mem);
      postcond = (fst c_summary.postcond, post_mem);
      args = c_summary.args;
    }

let new_this_summary old_summary values =
  let this_symbol = org_symbol "this" old_summary |> mk_symbol in
  let new_mem mem =
    Condition.M.find this_symbol mem
    |> Condition.M.add
         (fst values |> fst |> mk_index)
         (snd values |> fst |> mk_symbol)
  in
  let new_premem = new_mem (snd old_summary.precond) in
  let new_postmem = new_mem (snd old_summary.postcond) in
  {
    relation = old_summary.relation;
    value =
      Value.M.add (fst values |> fst) (fst values |> snd) old_summary.value
      |> Value.M.add (snd values |> fst) (snd values |> snd);
    use_field = old_summary.use_field;
    precond =
      ( fst old_summary.precond,
        Condition.M.add this_symbol new_premem (snd old_summary.precond) );
    postcond =
      ( fst old_summary.postcond,
        Condition.M.add this_symbol new_postmem (snd old_summary.postcond) );
    args = old_summary.args;
  }

let modify_array_summary id t_summary a_summary =
  let from_error, value = get_array_size id t_summary in
  let new_value =
    Value.M.add
      (org_symbol "size" a_summary)
      Value.{ from_error; value = Value.Ge (Int value) }
      a_summary.value
  in
  let rec mk_new_summary new_summary summary =
    let tmp = get_array_index id summary in
    if fst tmp |> fst = "" then (new_summary, summary)
    else
      let new_mem = remove_array_index id (fst tmp |> fst) summary in
      mk_new_summary
        (new_this_summary new_summary tmp)
        (new_mem_summary new_mem summary)
  in
  mk_new_summary (new_value_summary new_value a_summary) t_summary |> fst

let get_param v summary =
  let get_field id =
    AST.get_field_from_ufmap id (fst summary.precond) summary.use_field
  in
  let make_new_var id =
    ASTIR.
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

let find_org_param org_params_list p =
  List.fold_left
    (fun param real_arg ->
      if p = fst real_arg.ASTIR.variable then real_arg else param)
    AST.empty_var org_params_list

let mk_params_list summary params_set org_param =
  let find_same_param target =
    let t = fst target.ASTIR.variable in
    VarSets.fold
      (fun set find ->
        let fst_p = VarSet.elements set |> List.hd in
        VarSet.fold (fun p f -> if t = p then fst_p else f) set find)
      params_set t
  in
  let org_params_list = get_org_params_list summary org_param in
  let rec mk_params org_params params_list =
    match org_params with
    | hd :: tl ->
        let same_param = find_same_param hd |> find_org_param org_params_list in
        (if params_list = [] then [ [ hd ] ]
         else if hd = same_param then
           (* not found the same parameter *)
           List.fold_left
             (fun acc list -> List.cons (hd :: list) acc)
             [] params_list
         else
           List.fold_left
             (fun acc list ->
               List.cons (same_param :: list) acc |> List.cons (hd :: list))
             [] params_list)
        |> mk_params tl
    | _ -> params_list
  in
  mk_params org_params_list []

let mk_arg ~is_s param s c_info =
  let param = if is_s then param else List.tl param in
  let same_params_set = get_same_params_set s param c_info in
  mk_params_list s same_params_set param
  |> List.fold_left
       (fun arg_set lst -> VarListSet.add (List.rev lst) arg_set)
       VarListSet.empty

let summary_filtering name m_info list =
  List.filter
    (fun (_, c, _) -> is_public c m_info || is_usable_default c m_info)
    list
  |> List.filter (fun (_, c, _) -> is_recursive_param name c m_info |> not)

let get_field_set ret s_map =
  let c_name = AST.get_vinfo ret |> fst |> get_class_name in
  let fields =
    List.fold_left
      (fun fm (_, fields) -> FieldSet.union fields fm)
      (AST.get_v ret).field
      (try SetterMap.M.find c_name s_map with _ -> [])
  in
  FieldSet.fold
    (fun x new_fields ->
      let dup = Field.{ used_in_error = false; name = x.name } in
      if x.used_in_error && FieldSet.mem dup new_fields then
        FieldSet.remove dup new_fields
      else new_fields)
    fields fields

let error_entry_func ee es m_info c_info =
  let param = (MethodInfo.M.find ee m_info).MethodInfo.formal_params in
  let f_arg_list = mk_arg ~is_s:(is_static_method ee m_info) param es c_info in
  let c_name = Utils.get_class_name ee in
  let typ_list =
    if
      is_public_class c_name (fst c_info) |> not
      && is_usable_default_class c_name (fst c_info) |> not
    then
      try IG.succ (snd c_info) c_name |> List.cons c_name
      with Invalid_argument _ -> [ c_name ]
    else [ c_name ]
  in
  List.fold_left
    (fun lst typ ->
      let f = ASTIR.F { typ; method_name = ee; import = typ; summary = es } in
      if VarListSet.is_empty f_arg_list then (0, f, []) :: lst
      else
        VarListSet.fold (fun f_arg acc -> (0, f, f_arg) :: acc) f_arg_list lst)
    [] typ_list

let get_setter_list summary s_lst =
  List.fold_left
    (fun lst (s, fields) ->
      let smy =
        try SummaryMap.M.find s summary |> fst |> List.hd
        with _ -> empty_summary
      in
      (s, fields, smy) :: lst)
    [] s_lst
  |> List.rev |> prune_dup_summary_setter

let mk_void_func (var : ASTIR.var) id class_name m_info c_info s_lst =
  let get_arg_list s =
    mk_arg
      ~is_s:(is_static_method s m_info)
      (MethodInfo.M.find s m_info).MethodInfo.formal_params var.summary c_info
  in
  let get_f s =
    let typ =
      if Utils.is_array class_name then
        AST.get_vinfo id |> fst |> get_array_class_name
      else class_name
    in
    ASTIR.F { typ; method_name = s; import = var.import; summary = var.summary }
  in
  List.fold_left
    (fun lst (s, fields, _) ->
      let f_arg_list = get_arg_list s in
      let prec =
        if contains_used_in_error var.field fields || Utils.is_modeling_set s
        then 0
        else -2
      in
      let f = get_f s in
      if VarListSet.is_empty f_arg_list then (prec, f, []) :: lst
      else
        VarListSet.fold
          (fun f_arg acc -> (prec, f, f_arg) :: acc)
          f_arg_list lst)
    [] s_lst

(* id is receiver variable *)
let get_void_func id ?(ee = "") ?(es = empty_summary)
    { summary; m_info; c_info; setter_map; _ } =
  if AST.is_id id then error_entry_func ee es m_info c_info
  else
    let var = AST.get_v id in
    let class_name = AST.get_vinfo id |> fst |> get_class_name in
    if class_name = "" || class_name = "String" then []
    else
      (try SetterMap.M.find class_name setter_map with _ -> [])
      |> List.filter (fun (s, _) -> is_available_method s m_info)
      |> get_setter_list summary
      |> mk_void_func var id class_name m_info c_info

let check_satisfied_c id const_name t_summary init sat_lst =
  (List.fold_left (fun pick (check, smy) ->
       if check then
         if Utils.is_array_init const_name then
           let new_summary = modify_array_summary id t_summary smy in
           (is_from_error true new_summary, const_name, new_summary)
         else
           let new_summary = modify_summary id t_summary smy in
           (is_from_error true new_summary, const_name, new_summary)
       else if pick = (0, "", empty_summary) then (-3, const_name, empty_summary)
       else pick))
    init sat_lst

let satisfied_c_list id t_summary summary method_list =
  if !Cmdline.basic_mode then
    List.fold_left
      (fun list constructor -> (0, constructor, empty_summary) :: list)
      [] method_list
    |> List.rev
  else if !Cmdline.pruning_mode then
    List.fold_left
      (fun list constructor ->
        let c_summaries =
          try SummaryMap.M.find constructor summary |> fst
          with _ -> [ empty_summary ]
        in
        (0, constructor, List.hd c_summaries) :: list)
      [] method_list
    |> List.rev
  else
    List.fold_left
      (fun list constructor ->
        let lst = satisfied_c t_summary id constructor summary in
        let init = (0, "", empty_summary) in
        let pick = check_satisfied_c id constructor t_summary init lst in
        if pick = init then list else pick :: list)
      [] method_list
    |> List.rev

let get_cfunc id constructor m_info c_info =
  let cost, c, s = constructor in
  let t = Utils.get_class_name c in
  let t =
    if Utils.is_array t then AST.get_vinfo id |> fst |> get_array_class_name
    else t
  in
  let func = ASTIR.F { typ = t; method_name = c; import = t; summary = s } in
  let arg_list =
    mk_arg
      ~is_s:(is_static_method c m_info)
      (MethodInfo.M.find c m_info).MethodInfo.formal_params s c_info
  in
  if VarListSet.is_empty arg_list then [ (cost, (func, ASTIR.Arg [])) ]
  else
    VarListSet.fold
      (fun arg cfuncs -> (cost, (func, ASTIR.Arg arg)) :: cfuncs)
      arg_list []

let get_cfuncs id list m_info c_info =
  List.fold_left
    (fun lst (cost, c, s) ->
      List.rev_append (get_cfunc id (cost, c, s) m_info c_info) lst)
    [] list

let get_c ret c_lst summary m_info c_info =
  let class_name = AST.get_vinfo ret |> fst |> get_class_name in
  if class_name = "" then []
  else
    let id = AST.get_vinfo ret |> snd in
    let s_list =
      satisfied_c_list id (AST.get_v ret).summary summary c_lst
      |> List.filter (fun (_, c, _) ->
             is_abstract_class (c |> Utils.get_class_name) c_info |> not)
      |> summary_filtering class_name m_info
      |> prune_dup_summary m_info
    in
    get_cfuncs ret s_list m_info c_info

let is_ret_recv_mem_effect fld_name subtypes summary m_info ret_recv_methods =
  let check_ret_recv fld_name subtypes m_name effect_fld_lst =
    let info = MethodInfo.M.find m_name m_info in
    List.mem info.MethodInfo.return subtypes && List.mem fld_name effect_fld_lst
  in
  List.fold_left
    (fun check m_name ->
      check
      || check_ret_recv fld_name subtypes m_name
           (SummaryMap.M.find m_name summary |> snd))
    false ret_recv_methods

let get_params_symbol m_name m_info { precond = pre_var, pre_mem; _ } =
  let info = MethodInfo.M.find m_name m_info in
  List.fold_left
    (fun lst param ->
      match param with
      | This _ -> lst
      | Var (_, var) ->
          get_field_symbol (mk_var "") (get_id_symbol pre_var var) pre_mem
          :: lst)
    [] info.MethodInfo.formal_params

let is_set_recv_mem_effect fld_name summary m_info set_recv_methods =
  let check_set_recv fld_name m_name summaries =
    let get_fld_symbol { postcond = post_var, post_mem; _ } =
      get_field_symbol (mk_var fld_name)
        (get_id_symbol post_var "this")
        post_mem
    in
    List.fold_left
      (fun check smy ->
        check
        || List.mem (get_fld_symbol smy) (get_params_symbol m_name m_info smy)
           |> not)
      false summaries
  in
  List.fold_left
    (fun check (m_name, fld_set) ->
      check
      || FieldSet.mem { used_in_error = false; name = fld_name } fld_set
         && check_set_recv fld_name m_name
              (SummaryMap.M.find m_name summary |> fst))
    false set_recv_methods

let get_recv_type c_info summary_lst =
  List.fold_left
    (fun need_typ_set (_, c, _) ->
      let recv_type = Utils.get_class_name c in
      let subtypes =
        try IG.succ (snd c_info) recv_type |> List.cons recv_type
        with Invalid_argument _ -> [ recv_type ]
      in
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
          if is_static_method c m_info then []
          else
            try IG.succ (snd c_info) recv_type |> List.cons recv_type
            with Invalid_argument _ -> [ recv_type ]
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
  let class_name = AST.get_vinfo ret |> fst |> get_class_name in
  if class_name = "" then []
  else
    let id = AST.get_vinfo ret |> snd in
    let s_list =
      satisfied_c_list id (AST.get_v ret).summary summary ret_obj_lst
      |> summary_filtering class_name m_info
      |> prune_dup_summary m_info
      |> memory_effect_filtering summary m_info type_info c_info s_map
    in
    get_cfuncs ret s_list m_info c_info

let get_inner_func f arg =
  let fname =
    Str.split Regexp.dollar (AST.get_func f).method_name |> List.rev |> List.hd
  in
  let n_f =
    ASTIR.mk_f (AST.get_func f).typ fname (AST.get_func f).import
      (AST.get_func f).summary
  in
  (* outer class variable *)
  let recv = try AST.get_arg arg |> List.hd with _ -> AST.empty_var in
  let n_recv =
    let escaped_fname =
      Str.global_replace Regexp.open_bk "\\[" fname
      |> Str.global_replace Regexp.end_bk "\\]"
    in
    let var =
      Object
        ((AST.get_func f).method_name
        |> Regexp.first_rm (Str.regexp ("\\$" ^ escaped_fname)))
    in
    ASTIR.mk_var recv.import
      (Var (var, "con_outer"), mk_some !outer)
      FieldSet.empty recv.summary
    |> ASTIR.mk_variable
  in
  (n_recv, n_f, ASTIR.Arg (try AST.get_arg arg |> List.tl with _ -> []))

let cname_condition m_name m_info c_info =
  match MethodInfo.M.find_opt m_name m_info with
  | Some info ->
      info.MethodInfo.return <> ""
      && (is_static_method m_name m_info || is_static_class m_name c_info)
      || Utils.is_init_method m_name
  | _ -> Utils.is_init_method m_name

let get_cname f = ASTIR.ClassName (AST.get_func f).ASTIR.typ

let get_arg_seq (args : ASTIR.id list) =
  let already_arg = ref [] in
  List.fold_left
    (fun s arg ->
      if List.mem arg !already_arg then s
      else (
        already_arg := arg :: !already_arg;
        let x =
          List.fold_left (fun lst x -> AST.mk_const_arg x arg :: lst) [] s
        in
        if is_primitive arg then x
        else
          List.rev_append
            (List.fold_left (fun lst x -> AST.mk_assign_arg x arg :: lst) [] s)
            x))
    [ ASTIR.Skip ] args

let mk_arg_seq arg class_name =
  let modified_x x =
    if is_primitive_from_v x then AST.modify_import class_name x else x
  in
  get_arg_seq
    (List.fold_left
       (fun lst x -> ASTIR.Variable (modified_x x) :: lst)
       [] (AST.get_arg arg))

let loop_id_merge old_ids new_ids =
  LoopIdMap.M.merge
    (fun _ v1 v2 ->
      match (v1, v2) with
      | None, None -> None
      | Some _, _ -> v1
      | None, Some _ -> v2)
    old_ids new_ids

let obj_type_merge old_types new_types =
  ObjTypeMap.M.merge
    (fun _ v1 v2 ->
      match (v1, v2) with
      | None, None -> None
      | Some _, _ -> v1
      | None, Some _ -> v2)
    old_types new_types

(* low priority --> ... --> high priority *)
let sort_const consts =
  List.stable_sort (fun (c1, _) (c2, _) -> compare c1 c2) consts

let is_file_obj x =
  match AST.get_vinfo x |> fst with
  | Object t when t = "java.io.File" -> true
  | _ -> false

let is_instream_obj x =
  match AST.get_vinfo x |> fst with
  | Object t when t = "java.io.InputStream" -> true
  | _ -> false

let is_outstream_obj x =
  match AST.get_vinfo x |> fst with
  | Object t when t = "java.io.OutputStream" -> true
  | _ -> false

let not_null_obj x =
  if is_file_obj x || is_instream_obj x || is_outstream_obj x then true
  else false

let is_comparable x =
  match AST.get_vinfo x |> fst with
  | Object t when t = "java.lang.Comparable" -> true
  | _ -> false

let is_object x =
  match AST.get_vinfo x |> fst with
  | Object t when t = "java.lang.Object" -> true
  | _ -> false

let is_number x =
  match AST.get_vinfo x |> fst with
  | Object t when t = "java.lang.Number" -> true
  | _ -> false

let special_class_list =
  [
    "java.lang.Comparable";
    "java.lang.Object";
    "java.lang.Number";
    "java.lang.Class";
  ]

let const_unroll p { summary; m_info; inst_info; prim_info; _ } =
  let get_r3 x =
    List.fold_left
      (fun lst x1 ->
        match snd x1 with
        | ASTIR.Primitive _ -> lst
        | _ ->
            (fst x1, AST.const_rule3 p, empty_id_map, empty_obj_type_map) :: lst)
      [] (get_value x prim_info)
  in
  let get_r2 x =
    if is_comparable x then
      [
        ( 0,
          AST.const_rule2 p (ASTIR.GlobalConstant "java.math.BigDecimal.ONE"),
          empty_id_map,
          ObjTypeMap.M.add "java.lang.Comparable" "java.math.BigDecimal"
            empty_obj_type_map );
      ]
    else if is_object x then
      let f =
        ASTIR.mk_f "java.lang.Object" "java.lang.Object.<init>()"
          "java.lang.Object" Modeling.obj_summary
      in
      let param = ASTIR.Param [] in
      [
        ( 0,
          AST.const_rule2_2 p f param,
          empty_id_map,
          ObjTypeMap.M.add "java.lang.Object" "java.lang.Object"
            empty_obj_type_map );
      ]
    else if is_number x then
      [
        ( 0,
          AST.const_rule2 p (ASTIR.GlobalConstant "java.math.BigDecimal.ONE"),
          empty_id_map,
          ObjTypeMap.M.add "java.lang.Number" "java.math.BigDecimal"
            empty_obj_type_map );
      ]
    else
      List.fold_left
        (fun lst x1 ->
          (fst x1, AST.const_rule2 p (snd x1), empty_id_map, empty_obj_type_map)
          :: lst)
        []
        (global_var_list
           (AST.get_vinfo x |> fst |> get_class_name)
           (AST.get_v x).summary summary m_info inst_info)
  in
  match p with
  | ASTIR.Const (x, _) ->
      if is_primitive x then
        if !Cmdline.with_loop then
          let prec, exps =
            List.fold_left
              (fun (prec, lst) x1 ->
                let prec = if prec < fst x1 then fst x1 else prec in
                (prec, snd x1 :: lst))
              (min_int, [])
              (get_value x prim_info |> sort_const)
          in
          [
            ( prec,
              AST.const_rule_loop p,
              LoopIdMap.M.add x exps empty_id_map,
              empty_obj_type_map );
          ]
        else
          List.fold_left
            (fun lst x1 ->
              ( fst x1,
                AST.const_rule1 p (snd x1),
                empty_id_map,
                empty_obj_type_map )
              :: lst)
            [] (get_value x prim_info)
      else
        let r2 = get_r2 x in
        if is_receiver (AST.get_vinfo x |> snd) || not_null_obj x then r2
        else List.rev_append (get_r3 x) r2
  | _ -> failwith "Fail: const_unroll"

let fcall_in_assign_unroll p obj_types
    { summary; m_info; t_info; c_info; setter_map; _ } =
  match p with
  | ASTIR.Assign (x0, _, _, _) ->
      let field_set = get_field_set x0 setter_map in
      let class_name = AST.get_vinfo x0 |> fst |> get_class_name in
      let org_c_lst, c_lst, ret_c_lst =
        (* if class is special class, we don't use the methods returning that class type *)
        if List.mem class_name special_class_list then ([], [], [])
        else get_m_lst x0 m_info c_info
      in
      let c_lst = if org_c_lst = [] then c_lst else org_c_lst in
      if c_lst = [] && ret_c_lst = [] then raise Not_found_get_object
      else
        List.rev_append
          (get_c x0 c_lst summary m_info c_info)
          (get_ret_c x0 ret_c_lst summary m_info t_info c_info setter_map)
        |> List.fold_left
             (fun lst (prec, (f, arg)) ->
               let child_name =
                 Utils.get_class_name (AST.get_func f).method_name
               in
               match ObjTypeMap.M.find_opt class_name obj_types with
               | Some child when child = child_name ->
                   ( prec,
                     AST.fcall_in_assign_rule p field_set f arg,
                     empty_id_map,
                     empty_obj_type_map )
                   :: lst
               | Some _ -> lst
               | None ->
                   ( prec,
                     AST.fcall_in_assign_rule p field_set f arg,
                     empty_id_map,
                     ObjTypeMap.M.add class_name child_name obj_types )
                   :: lst)
             []
  | _ -> failwith "Fail: fcall_in_assign_unroll"

let recv_in_assign_unroll (prec, p, loop_ids, obj_types) { m_info; c_info; _ } =
  match p with
  | ASTIR.Assign (_, _, f, arg) when AST.recv_in_assign p ->
      if
        is_nested_class (AST.get_func f).import
        && is_static_class (AST.get_func f).import c_info |> not
        && Utils.is_init_method (AST.get_func f).method_name
      then (
        let recv, f, arg = get_inner_func f arg in
        if (AST.get_v recv).import = "" then
          (* The import of the inner class function being empty means
             that the receiver is an empty variable *)
          []
        else
          let r2 = AST.recv_in_assign_rule2_1 p recv f arg in
          let r3 = AST.recv_in_assign_rule3_1 p recv f arg in
          incr outer;
          (prec, r2, loop_ids, obj_types) :: [ (prec, r3, loop_ids, obj_types) ])
      else if cname_condition (AST.get_func f).method_name m_info c_info then
        [
          (prec, get_cname f |> AST.recv_in_assign_rule1 p, loop_ids, obj_types);
        ]
      else
        let r2 = AST.recv_in_assign_rule2 p "con_recv" !recv in
        let r3 = AST.recv_in_assign_rule3 p "con_recv" !recv in
        incr recv;
        (prec, r2, loop_ids, obj_types) :: [ (prec, r3, loop_ids, obj_types) ]
  | _ -> failwith "Fail: recv_in_assign_unroll"

let rec arg_in_assign_unroll (prec, p, loop_ids, obj_types) =
  match p with
  | ASTIR.Assign (_, _, f, arg) when AST.arg_in_assign p ->
      let class_name = Utils.get_class_name (AST.get_func f).method_name in
      mk_arg_seq arg class_name
      |> List.fold_left
           (fun lst x ->
             ( prec,
               AST.arg_in_assign_rule p x (ASTIR.Param (AST.get_arg arg)),
               loop_ids,
               obj_types )
             :: lst)
           []
  | Seq (s1, s2) when AST.arg_in_assign s2 ->
      arg_in_assign_unroll (prec, s2, loop_ids, obj_types)
      |> List.fold_left
           (fun lst (p', s', loop', type') ->
             ( p',
               ASTIR.Seq (s1, s'),
               loop_id_merge loop_ids loop',
               obj_type_merge obj_types type' )
             :: lst)
           []
  | _ -> failwith "Fail: arg_in_assign_unroll"

let void_unroll p =
  (0, AST.void_rule1 p, empty_id_map, empty_obj_type_map)
  :: List.fold_left
       (fun lst x -> (0, x, empty_id_map, empty_obj_type_map) :: lst)
       [] (AST.void_rule2 p)

let fcall_in_void_unroll p p_data =
  match p with
  | ASTIR.Void (x, _, _) ->
      let lst = get_void_func x p_data in
      if lst = [] then raise Not_found_setter
      else
        List.fold_left
          (fun lst (prec, f, arg) ->
            ( prec,
              AST.fcall_in_void_rule p f (ASTIR.Arg arg),
              empty_id_map,
              empty_obj_type_map )
            :: lst)
          [] lst
  | _ -> failwith "Fail: fcall_in_void_unroll"

let recv_in_void_unroll (prec, p, loop_ids, obj_types) { m_info; c_info; _ } =
  match p with
  | ASTIR.Void (_, f, _) when AST.recv_in_void p ->
      if cname_condition (AST.get_func f).method_name m_info c_info then
        [ (prec, get_cname f |> AST.recv_in_void_rule1 p, loop_ids, obj_types) ]
      else
        let r2 = AST.recv_in_void_rule2 p "con_recv" !recv in
        let r3 = AST.recv_in_void_rule3 p "con_recv" !recv in
        incr recv;
        (prec, r2, loop_ids, obj_types) :: [ (prec, r3, loop_ids, obj_types) ]
  | _ -> failwith "Fail: recv_in_void_unroll"

let rec arg_in_void_unroll (prec, p, loop_ids, obj_types) =
  match p with
  | ASTIR.Void (_, f, arg) when AST.arg_in_void p ->
      let class_name = Utils.get_class_name (AST.get_func f).method_name in
      mk_arg_seq arg class_name
      |> List.fold_left
           (fun lst x ->
             ( prec,
               AST.arg_in_void_rule p x (ASTIR.Param (AST.get_arg arg)),
               loop_ids,
               obj_types )
             :: lst)
           []
  | Seq (s1, s2) when AST.arg_in_void s2 ->
      arg_in_void_unroll (prec, s2, loop_ids, obj_types)
      |> List.fold_left
           (fun lst (p', s', loop', type') ->
             (p', ASTIR.Seq (s1, s'), loop', type') :: lst)
           []
  | _ -> failwith "Fail: arg_in_void_unroll"

let append l1 l2 =
  let rec iter accu ll1 ll2 =
    match (ll1, ll2) with
    | h1 :: t1, h2 :: t2 -> iter (h2 :: h1 :: accu) t1 t2
    | [], ll2 -> List.rev_append accu ll2
    | ll1, [] -> List.rev_append accu ll1
  in
  iter [] l1 l2

let one_unroll p obj_types p_data =
  match p with
  | ASTIR.Seq _ when AST.void p -> void_unroll p
  | Const _ when AST.const p -> const_unroll p p_data
  | Assign _ when AST.fcall_in_assign p -> (
      (* fcall_in_assign --> recv_in_assign --> arg_in_assign *)
      match fcall_in_assign_unroll p obj_types p_data with
      | exception Not_found_get_object ->
          if !Cmdline.mock then
            [ (0, AST.mk_mock_statement p, empty_id_map, empty_obj_type_map) ]
          else raise Not_found_get_object
      | p_lst ->
          let lst =
            List.fold_left
              (fun acc_lst x ->
                recv_in_assign_unroll x p_data |> append acc_lst)
              [] p_lst
            |> List.fold_left
                 (fun acc_lst x -> arg_in_assign_unroll x |> append acc_lst)
                 []
          in
          if
            !Cmdline.mock
            && List.filter
                 (fun (_, x, _, _) ->
                   AST.count_params x < 2 (* at least receiver *))
                 p_lst
               = []
          then
            (0, AST.mk_mock_statement p, empty_id_map, empty_obj_type_map)
            :: lst
          else lst)
  | Void _ when AST.fcall1_in_void p ->
      (* fcall1_in_void --> recv_in_void --> arg_in_void *)
      fcall_in_void_unroll p p_data
      |> List.fold_left
           (fun acc_lst x -> recv_in_void_unroll x p_data |> append acc_lst)
           []
      |> List.fold_left
           (fun acc_lst x -> arg_in_void_unroll x |> append acc_lst)
           []
  | Void _ when AST.fcall2_in_void p ->
      (* fcall2_in_void --> arg_in_void *)
      fcall_in_void_unroll p p_data
      |> List.fold_left
           (fun acc_lst x -> arg_in_void_unroll x |> append acc_lst)
           []
  | Void _ when AST.recv_in_void p ->
      (* unroll error entry *)
      recv_in_void_unroll (0, p, empty_id_map, empty_obj_type_map) p_data
      |> List.fold_left
           (fun acc_lst x -> arg_in_void_unroll x |> append acc_lst)
           []
  | _ -> failwith "Fail: one_unroll"

let rec all_unroll ?(assign_ground = false) p obj_types p_data stmt_map =
  match p with
  | _ when AST.ground p -> stmt_map
  | _ when assign_ground -> all_unroll_void p obj_types p_data stmt_map
  | ASTIR.Seq (s1, s2) when s2 = Stmt ->
      all_unroll ~assign_ground s1 obj_types p_data stmt_map
  | Seq (s1, s2) ->
      all_unroll ~assign_ground s1 obj_types p_data stmt_map
      |> all_unroll ~assign_ground s2 obj_types p_data
  | _ -> StmtMap.M.add p (one_unroll p obj_types p_data) stmt_map

and all_unroll_void p obj_types p_data stmt_map =
  match p with
  | _ when AST.ground p -> stmt_map
  | ASTIR.Seq _ when AST.void p ->
      StmtMap.M.add p (one_unroll p obj_types p_data) stmt_map
  | Seq (s1, s2) -> (
      let new_void s1 (p', s', loop', type') =
        (p', ASTIR.Seq (AST.modify_last_assign s1, s'), loop', type')
      in
      let new_void_list s1 s2 =
        one_unroll (Seq (AST.last_code s1, s2)) obj_types p_data
        |> List.fold_left (fun lst void -> new_void s1 void :: lst) []
        |> List.rev
      in
      match AST.last_code s1 with
      | ASTIR.Assign _ when AST.is_stmt s2 ->
          StmtMap.M.add p (new_void_list s1 s2) stmt_map
      | _ ->
          all_unroll_void s1 obj_types p_data stmt_map
          |> all_unroll_void s2 obj_types p_data)
  | _ -> failwith "Fail: all_unroll_void"

let rec change_stmt p s new_s : ASTIR.t =
  match p with
  | _ when p = s -> new_s
  | ASTIR.Seq (s1, s2) when s1 = s -> Seq (new_s, s2)
  | Seq (s1, s2) when s2 = s -> Seq (s1, new_s)
  | Seq (s1, s2) -> Seq (change_stmt s1 s new_s, change_stmt s2 s new_s)
  | _ -> p

let rec return_stmts p =
  match p with
  | _ when AST.ground p -> [] (* ground check of partial tc is first *)
  | ASTIR.Seq (s1, s2) ->
      p :: List.rev_append (return_stmts s1) (return_stmts s2)
  | _ -> [ p ]

let sort_stmts map stmts =
  List.stable_sort
    (fun s1 s2 ->
      match (StmtMap.M.find_opt s1 map, StmtMap.M.find_opt s2 map) with
      | Some l1, Some l2 -> compare (List.length l1) (List.length l2)
      | Some _, None -> 1
      | None, Some _ -> -1
      | None, None -> 0)
    stmts

let combinate (prec, p, loop_ids, obj_types) stmt_map =
  let combinate_stmt (p', s', loop_ids', obj_types') s new_s_list =
    List.fold_left
      (fun lst (new_p, new_s, new_loop, new_type) ->
        ( p' + new_p,
          change_stmt s' s new_s,
          loop_id_merge loop_ids' new_loop,
          obj_type_merge obj_types' new_type )
        :: lst)
      [] new_s_list
  in
  let combinate_stmts s new_s_lst partial_lst =
    List.fold_left
      (fun l _p -> combinate_stmt _p s new_s_lst |> append l)
      [] partial_lst
  in
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
      [ (prec, p, loop_ids, obj_types) ]
      stmts
  in
  return_stmts p |> sort_stmts stmt_map |> all_combinate |> List.rev

(* find error entry *)
let rec find_ee e_method e_summary p_data =
  let propagation caller_method caller_preconds call_prop =
    let new_value, new_mem, check_match =
      try satisfy e_method e_summary call_prop p_data.m_info
      with _ -> (
        Logger.info
          "Given wrong summary of error method! So, the \"find_ee\" step \
           progresses using a temporary summary";
        match SummaryMap.M.find_opt e_method p_data.summary with
        | Some (s, _) ->
            let tmp_summary = List.hd s in
            (tmp_summary.value, snd tmp_summary.precond, true)
        | None -> (Value.M.empty, Condition.M.empty, false))
    in
    let new_uf = mk_new_uf e_method e_summary call_prop p_data.m_info in
    if !Cmdline.basic_mode then
      ErrorEntrySet.union caller_preconds
        (find_ee caller_method empty_summary p_data)
    else if !Cmdline.pruning_mode then
      ErrorEntrySet.union caller_preconds
        (find_ee caller_method call_prop p_data)
    else if check_match then
      let new_call_prop =
        new_value_summary new_value call_prop
        |> new_mem_summary new_mem |> new_uf_summary new_uf
      in
      ErrorEntrySet.union caller_preconds
        (find_ee caller_method new_call_prop p_data)
    else caller_preconds
  in
  if
    is_public e_method p_data.m_info || is_usable_default e_method p_data.m_info
  then ErrorEntrySet.add (e_method, e_summary) ErrorEntrySet.empty
  else
    let get_caller_list m_name =
      try
        CG.succ p_data.cg m_name
        |> List.filter (fun x -> x <> m_name && x <> e_method)
      with Invalid_argument _ -> []
    in
    let org_caller_list =
      try CG.succ p_data.cg e_method |> List.filter (fun x -> x <> e_method)
      with Invalid_argument _ -> []
    in
    let class_name = Utils.get_class_name e_method in
    let escaped_m_name =
      Str.global_replace Regexp.dot "\\." class_name
      |> Str.global_replace Regexp.dollar "\\$"
    in
    let caller_list =
      if org_caller_list = [] then
        (try IG.pred (snd p_data.c_info) class_name
         with Invalid_argument _ -> [])
        |> List.fold_left
             (fun acc c_name ->
               let new_m_name =
                 Str.replace_first (Str.regexp escaped_m_name) c_name e_method
               in
               List.rev_append (get_caller_list new_m_name) acc)
             org_caller_list
      else org_caller_list
    in
    List.fold_left
      (fun set caller_method ->
        (match
           CallPropMap.M.find_opt (caller_method, e_method) p_data.cp_map
         with
        | None ->
            (* It is possible without any specific conditions *)
            find_ee caller_method empty_summary p_data
        | Some prop_list ->
            List.fold_left
              (fun caller_preconds call_prop ->
                if ExploredMethod.mem caller_method !explored_m then
                  (* if the caller method is included in the error entry set,
                       avoiding duplicate calculation *)
                  caller_preconds
                else (
                  explored_m := ExploredMethod.add caller_method !explored_m;
                  propagation caller_method caller_preconds call_prop))
              ErrorEntrySet.empty prop_list)
        |> ErrorEntrySet.union set)
      ErrorEntrySet.empty caller_list

let pretty_format p =
  let rec imports s set =
    let add_import import set =
      (if is_nested_class import then
         ImportSet.add (Str.replace_first (Str.regexp "\\$.*$") "" import) set
       else set)
      |> ImportSet.add import
    in
    match s with
    | ASTIR.Seq (s1, s2) -> imports s1 set |> imports s2
    | Const (x, _) -> add_import (AST.get_v x).import set
    | Assign (x0, _, f, arg) ->
        List.fold_left
          (fun s (a : ASTIR.var) -> add_import a.import s)
          set (AST.get_param arg)
        |> add_import (AST.get_v x0).import
        |> add_import (AST.get_func f).import
    | Void (_, f, arg) ->
        List.fold_left
          (fun s (a : ASTIR.var) -> add_import a.import s)
          set (AST.get_param arg)
        |> add_import (AST.get_func f).import
    | _ -> set
  in
  (imports p ImportSet.empty, AST.code p)

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
  match queue with
  | p :: tl ->
      if !Cmdline.with_fuzz && AST.ground p.tc && AST.with_withfuzz p.tc then
        [ (Need_Fuzzer, pretty_format p.tc, p.loop_ids, tl) ]
      else if !Cmdline.with_loop && AST.ground p.tc && AST.with_withloop p.tc
      then [ (Need_Loop, pretty_format p.tc, p.loop_ids, tl) ]
      else if AST.ground p.tc then
        [ (Complete, pretty_format p.tc, p.loop_ids, tl) ]
      else
        (match
           all_unroll ~assign_ground:(AST.assign_ground p.tc) p.tc p.obj_types
             p_data StmtMap.M.empty
         with
        | exception Not_found_setter -> tl
        | exception Not_found_get_object -> tl
        | x ->
            combinate (p.prec, p.tc, p.loop_ids, p.obj_types) x
            |> List.fold_left
                 (fun lst (new_p, new_s, new_loop, new_type) ->
                   mk_cost p new_s new_loop new_type new_p :: lst)
                 []
            |> List.rev_append (List.rev tl))
        |> mk_testcase p_data
  | [] -> []

let mk_testcases ~is_start queue (e_method, error_summary) p_data =
  let apply_rule list =
    List.fold_left
      (fun lst (_, f, arg) ->
        AST.fcall_in_void_rule (ASTIR.Void (Id, Func, Arg [])) f (ASTIR.Arg arg)
        :: lst)
      [] list
  in
  let p_info, init =
    if is_start then
      ErrorEntrySet.fold
        (fun (ee, ee_s) (p_info_init, init_list) ->
          ( Constant.expand_string_value ee p_info_init,
            apply_rule (get_void_func ASTIR.Id ~ee ~es:ee_s p_data)
            |> List.fold_left
                 (fun lst new_tc ->
                   mk_cost empty_p new_tc empty_id_map empty_obj_type_map 0
                   :: lst)
                 []
            |> List.rev_append init_list ))
        (find_ee e_method error_summary p_data)
        (p_data.prim_info, [])
    else (p_data.prim_info, queue)
  in
  let result = mk_testcase (update_prim p_data p_info) init in
  if result = [] then (Incomplete, (ImportSet.empty, ""), empty_id_map, [])
  else List.hd result
