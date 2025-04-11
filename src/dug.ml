open Language

module DUGIR = struct
  type num = int [@@deriving compare, equal]

  type var = {
    import : import;
        (* if var is primitive type then import is class of method *)
    variable : variable * int option;
    field : FieldSet.t;
    summary : summary;
  }
  [@@deriving compare, equal]

  type f = {
    typ : string;
    method_name : method_name;
    import : import;
    summary : summary;
  }
  [@@deriving compare, equal]

  type arg = Param of var list | Arg of var list [@@deriving compare, equal]

  type func = F of f | Func [@@deriving compare, equal]

  type id = Variable of var | ClassName of string | Id
  [@@deriving compare, equal]

  type primitive = Z of int | R of float | B of bool | C of char | S of string
  [@@deriving compare, equal]

  type exp =
    | Primitive of primitive
    | GlobalConstant of string
    | Null
    | WithLoop
    | Exp
  [@@deriving compare, equal]

  type t =
    | Const of (num * (variable * int option) * (id * exp))
    | Assign of (num * (variable * int option) * (id * id * func * arg))
    | Void of (num * (variable * int option) * (id * func * arg))
    | Skip of (num * (variable * int option))
    | Stmt of (num * (variable * int option))
  [@@deriving compare, equal]

  let mk_var import variable field summary =
    { import; variable; field; summary }

  let mk_variable var = Variable var

  let mk_f typ method_name import summary =
    F { typ; method_name; import; summary }
end

module Node = struct
  include DUGIR

  let hash = Hashtbl.hash
end

module G = struct
  include Graph.Persistent.Digraph.ConcreteBidirectional (Node)

  let graph_attributes _ = []

  let default_vertex_attributes _ = []

  let vertex_name v = v

  let vertex_attributes _ = []

  let get_subgraph _ = None

  let default_edge_attributes _ = []

  let edge_attributes _ = []
end

module LoopIdMap = struct
  module M = Map.Make (struct
    type t = DUGIR.id

    let compare = compare
  end)

  type t = DUGIR.exp list M.t
end

module DUG = struct
  include G
  module Topological = Graph.Topological.Make_stable (G)
  module PathCheck = Graph.Path.Check (G)
  open DUGIR

  let empty_var =
    {
      import = "";
      variable = (This NonType, None);
      field = FieldSet.empty;
      summary = empty_summary;
    }

  (* id -> var *)
  let rec get_v id =
    match id with Variable v -> v | _ -> failwith "get_v: not supported"

  (* id -> typ * string *)
  and get_vinfo v =
    match (get_v v).variable with
    | Var (typ, id), _ -> (typ, id)
    | This typ, _ -> (typ, "this")

  let get_func func =
    match func with
    | F f -> f
    | _ -> { typ = ""; method_name = ""; import = ""; summary = empty_summary }

  let get_arg arg = match arg with Arg a -> a | _ -> []

  let get_param arg = match arg with Param p -> p | _ -> []

  let is_stmt = function Stmt _ -> true | _ -> false

  and is_arg = function Arg _ -> true | _ -> false

  and is_func = function Func -> true | _ -> false

  and is_id = function Id -> true | _ -> false

  and is_exp = function Exp -> true | _ -> false

  and is_loop = function WithLoop -> true | _ -> false

  let ground_stmt = function
    | Const (_, _, (x, exp)) -> not (is_id x || is_exp exp)
    | Assign (_, _, (x0, x1, func, arg)) ->
        not (is_id x0 || is_id x1 || is_func func || is_arg arg)
    | Void (_, _, (x, func, arg)) -> not (is_id x || is_func func || is_arg arg)
    | Skip _ -> true
    | Stmt _ -> false

  let ground g = G.fold_vertex (fun n check -> check && ground_stmt n) g true

  let assign_ground_stmt = function
    | Const (_, _, (x, exp)) -> not (is_id x || is_exp exp)
    | Assign (_, _, (x0, x1, func, arg)) ->
        not (is_id x0 || is_id x1 || is_func func || is_arg arg)
    | Void (_, _, (x, func, arg)) -> not (is_id x || is_func func || is_arg arg)
    | Skip _ -> true
    | Stmt _ -> true

  let assign_ground g =
    G.fold_vertex (fun n check -> check && assign_ground_stmt n) g true

  let with_withloop_stmt = function
    | Const (_, _, (_, exp)) -> is_loop exp
    | Assign _ -> false
    | Void _ -> false
    | Skip _ -> false
    | Stmt _ -> false

  let with_withloop g =
    G.fold_vertex (fun n check -> check || with_withloop_stmt n) g false

  let rec count_nt_stmt = function
    | Const (_, _, (x, exp)) -> count_id x + count_exp exp
    | Assign (_, _, (x0, x1, func, _)) ->
        count_id x0 + count_id x1 + count_func func
    | Void (_, _, (x, func, _)) -> count_id x + count_func func
    | Skip _ -> 0
    | Stmt _ -> 0

  and count_func = function Func -> 1 | _ -> 0

  and count_id = function Id -> 1 | _ -> 0

  and count_exp = function Exp -> 1 | _ -> 0

  let count_nt g = G.fold_vertex (fun n cnt -> count_nt_stmt n + cnt) g 0

  let rec count_t_stmt = function
    | Const (_, _, (x, exp)) -> count_tid x + count_texp exp
    | Assign (_, _, (x0, x1, f, _)) -> count_tid x0 + count_tid x1 + count_tf f
    | Void (_, _, (x, f, _)) -> count_tid x + count_tf f
    | Skip _ -> 0
    | Stmt _ -> 0

  and count_tf = function Func -> 0 | _ -> 1

  and count_tid = function Id -> 0 | _ -> 1

  and count_texp = function Exp -> 0 | _ -> 1

  let count_t g = G.fold_vertex (fun n cnt -> count_t_stmt n + cnt) g 0

  let rec count_params = function
    | Assign (_, _, (_, _, _, p)) -> count_param p
    | _ -> 0

  and count_param = function Arg a -> List.length a | Param p -> List.length p

  let modify_import import v =
    { import; variable = v.variable; field = v.field; summary = v.summary }

  let is_array_init f = Utils.is_array_init (get_func f).method_name

  let is_array_set f = Utils.is_array_set (get_func f).method_name

  let is_file f =
    let fname = (get_func f).method_name in
    if Str.string_match (Str.regexp "java\\.io\\.File\\.<init>") fname 0 then
      true
    else false

  (* ************************************** *
     Checking for Synthesis Rules
   * ************************************** *)

  (* 1. x := Exp *)
  let const = function
    | Const (_, _, (x, exp)) -> is_id x |> not && is_exp exp
    | _ -> false

  (* 2. x := ID.F(ID) *)
  let fcall_in_assign = function
    | Assign (_, _, (x0, x1, func, arg)) ->
        is_id x0 |> not && is_id x1 && is_func func && is_arg arg
    | _ -> false

  (* 3. x := ID.f(ID) *)
  let recv_in_assign = function
    | Assign (_, _, (x0, x1, func, arg)) ->
        is_id x0 |> not && is_id x1 && is_func func |> not && is_arg arg
    | _ -> false

  (* 4. x0 := x1.f(ID) *)
  let arg_in_assign = function
    | Assign (_, _, (x0, x1, func, arg)) ->
        is_id x0 |> not && is_id x1 |> not && is_func func |> not && is_arg arg
    | _ -> false

  (* 5. x0 := x1.f(arg); Stmt *)
  let check_assign stmt_var = function
    | Assign (_, var, (x0, x1, func, arg)) when stmt_var = var ->
        is_id x0 |> not
        && is_id x1 |> not
        && is_func func |> not
        && is_arg arg |> not
    | _ -> false

  let void g stmt =
    match stmt with
    | Stmt (_, var) ->
        List.fold_left
          (fun check stmt -> check_assign var stmt || check)
          false (G.pred g stmt)
    | _ -> false

  (* 6. ID.F(ID) *)
  let fcall1_in_void = function
    | Void (_, _, (x, func, arg)) -> is_id x && is_func func && is_arg arg
    | _ -> false

  (* 7. x.F(ID) *)
  let fcall2_in_void = function
    | Void (_, _, (x, func, arg)) ->
        is_id x |> not && is_func func && is_arg arg
    | _ -> false

  (* 8. ID.f(ID) *)
  let recv_in_void = function
    | Void (_, _, (x, func, arg)) ->
        is_id x && is_func func |> not && is_arg arg
    | _ -> false

  (* 9. x.f(ID) *)
  let arg_in_void = function
    | Void (_, _, (x, func, arg)) ->
        is_id x |> not && is_func func |> not && is_arg arg
    | _ -> false

  (* ************************************** *
     Basic Operations
   * ************************************** *)

  let add_vertex n g = G.add_vertex g n

  let add_edge n1 n2 g = if n1 = n2 then g else G.add_edge g n1 n2

  let remove_vertex n g = G.remove_vertex g n

  let remove_edge n1 n2 g = G.remove_edge g n1 n2

  let pred n g = G.pred g n

  let succ n g = G.succ g n

  let add n1 n2 g =
    let g' = add_vertex n1 g |> add_vertex n2 in
    let succ = succ n1 g' in
    let g' = List.fold_left (fun g succ' -> remove_edge n1 succ' g) g' succ in
    let g' = List.fold_left (fun g succ' -> add_edge n2 succ' g) g' succ in
    add_edge n1 n2 g'

  let replace n1 n2 g =
    if G.mem_vertex g n1 |> not then failwith "DUG replace: n1 is not in graph"
    else
      let pred = pred n1 g in
      let succ = succ n1 g in
      let g' = List.fold_left (fun g pred' -> remove_edge pred' n1 g) g pred in
      let g' = List.fold_left (fun g succ' -> remove_edge n1 succ' g) g' succ in
      let g' = remove_vertex n1 g' |> add_vertex n2 in
      let g' = List.fold_left (fun g pred' -> add_edge pred' n2 g) g' pred in
      List.fold_left (fun g succ' -> add_edge n2 succ' g) g' succ

  let union g1 g2 =
    let g' =
      G.fold_vertex (fun n g -> add_vertex n g) g2 g1
      |> G.fold_edges (fun n n' g -> add_edge n n' g) g2
    in
    G.fold_vertex
      (fun n g ->
        if G.out_degree g n = 0 && G.in_degree g n = 0 then remove_vertex n g
        else g)
      g' g'

  let get_variable n =
    match n with Variable v -> v.variable | _ -> (This NonType, None)

  let equal_variables v1 v2 =
    if fst v1 <> This NonType && fst v2 <> This NonType && v1 = v2 then true
    else false

  let update n g =
    G.fold_vertex
      (fun n' g ->
        if ground_stmt n && ground_stmt n' then
          match (n, n') with
          | Void (num, v, (_, f, arg)), Void (num', v', (_, f', arg'))
            when equal_variables v v' && num = num' && f = f' && arg = arg' ->
              replace n' n g
          | ( Assign (num, v, (_, x1, f, arg)),
              Assign (num', v', (_, x1', f', arg')) )
            when equal_variables v v' && num = num' && x1 = x1' && f = f'
                 && arg = arg' ->
              replace n' n g
          | _ -> g
        else g)
      g g

  let replace_and_union n1 n2 g1 g2 =
    let g = replace n1 n2 g1 in
    (* update the statements having modified variable *)
    let g =
      G.fold_vertex
        (fun n g -> if G.mem_vertex g n |> not then update n g else g)
        g2 g
    in
    union g g2

  (* connect arguments to method that need the arguments *)
  let connect_and_union n g1 g2 =
    union g1 g2
    |> G.fold_vertex
         (fun n' g -> if G.out_degree g2 n' <> 0 then g else add_edge n' n g)
         g2

  (* if path of n2 ->* n1 exist, then n1 can not be defined before n2 *)
  let gt n1 n2 g =
    let path_checker = PathCheck.create g in
    let check = PathCheck.check_path path_checker n2 n1 in
    if check then false else true

  let get_id n =
    match n with
    | Const (_, _, (id, _)) -> id
    | Assign (_, _, (id, _, _, _)) -> id
    | _ -> Id

  let get_var n =
    match n with
    | Const (_, var, (_, _)) -> var
    | Assign (_, var, (_, _, _, _)) -> var
    | _ -> (This NonType, None)

  let is_similar n1 n2 =
    let v1 = get_var n1 in
    let v2 = get_var n2 in
    if !Cmdline.unknown_bug then
      match (fst v1, fst v2) with
      | This NonType, This NonType -> false
      | This NonType, _ -> false
      | _, This NonType -> false
      | Var (typ1, _), Var (typ2, _) when typ1 = typ2 -> true
      | _, _ -> false
    else if fst v1 = This NonType || fst v2 = This NonType then false
    else if fst v1 = fst v2 then true
    else false

  let get_already_nodes x g =
    G.fold_vertex
      (fun n cands -> if is_similar x n then n :: cands else cands)
      g []

  let is_already_node std_node x g =
    get_already_nodes x g
    |> List.fold_left
         (fun check n -> if gt n std_node g then true else check)
         false

  let find_node std_node x g =
    (* return the node corresponding to variable x in graph g *)
    get_already_nodes x g
    |> List.fold_left
         (fun found n -> if gt n std_node g then n else found)
         (Skip (0, (This NonType, None)))

  let get_edge_of_find_node node node_var graph =
    let succ = succ node graph in
    List.fold_left
      (fun found succ' ->
        match succ' with
        | Stmt (_, var) when var = node_var -> succ'
        | Void (_, var, _) when var = node_var -> succ'
        | _ -> found)
      node succ

  (* ************************************** *
     Synthesis Rules
   * ************************************** *)

  (* 2 *)
  let const_rule1 s n graph =
    match s with
    | Const (num, var, (x, _)) ->
        let s' = Const (num, var, (x, n)) in
        (s', add_vertex s' G.empty)
    | _ -> (s, graph)

  let const_rule2 s g graph =
    match s with
    | Const (num, var, (x, _)) ->
        let s' = Const (num, var, (x, g)) in
        (s', add_vertex s' G.empty)
    | _ -> (s, graph)

  let const_rule2_1 s f arg graph =
    match s with
    | Const (num, var, (x, _)) ->
        let g = ClassName ((get_func f).method_name |> Utils.get_class_name) in
        let s' = Assign (num, var, (x, g, f, arg)) in
        (s', add_vertex s' G.empty)
    | _ -> (s, graph)

  let const_rule3 s graph =
    match s with
    | Const (num, var, (x, _)) ->
        let s' = Const (num, var, (x, Null)) in
        (s', add_vertex s' G.empty)
    | _ -> (s, graph)

  let const_rule_loop s graph =
    match s with
    | Const (num, var, (x, _)) ->
        let s' = Const (num, var, (x, WithLoop)) in
        (s', add_vertex s' G.empty)
    | _ -> (s, graph)

  (* 3 *)
  let fcall_in_assign_rule s field f arg graph =
    match s with
    | Assign (num, var, (x0, x1, _, _)) ->
        let new_x0 =
          Variable
            {
              import = (get_v x0).import;
              variable = (get_v x0).variable;
              field;
              summary = (get_v x0).summary;
            }
        in
        let s' = Assign (num, var, (new_x0, x1, f, arg)) in
        (s', add_vertex s' G.empty)
    | _ -> (s, graph)

  (* TODO: change function name to fcall_in_assign_rule_mock *)
  let mk_mock_statement s graph =
    match s with
    | Assign (num, var, (x0, _, _, _)) ->
        let class_name = get_vinfo x0 |> fst |> get_class_name in
        let f = mk_f "" "mock" "" empty_summary in
        let variable = (Var (NonType, class_name), None) in
        let arg = Param [ mk_var "" variable FieldSet.empty empty_summary ] in
        let s' = Assign (num, var, (x0, ClassName "Mockito", f, arg)) in
        (s', replace s s' graph)
    | _ -> (s, graph)

  (* 4 *)
  let get_field_from_ufmap target var ufmap =
    let symbol =
      Condition.M.fold
        (fun sym id find ->
          match id with Condition.RH_Var i when i = target -> sym | _ -> find)
        var Condition.RH_Any
    in
    match UseFieldMap.M.find_opt symbol ufmap with
    | Some f -> f
    | _ -> FieldSet.empty

  let recv_in_assign_rule1 s c graph =
    match s with
    | Assign (num, var, (x0, _, func, arg)) ->
        let s' = Assign (num, var, (x0, c, func, arg)) in
        (s', replace s s' graph)
    | _ -> (s, graph)

  let recv_in_assign_rule2 s id idx graph =
    match s with
    | Assign (num, var, (x0, _, func, arg)) ->
        let typ = match func with Func -> "" | F f -> f.typ in
        let x1_field =
          match func with
          | Func -> FieldSet.empty
          | F f ->
              get_field_from_ufmap "this" (fst f.summary.precond)
                f.summary.use_field
        in
        let x1_var = (Var (Object typ, id), Some idx) in
        let x1 =
          Variable
            (mk_var
               (match func with Func -> "" | F f -> f.import)
               x1_var x1_field
               (match func with Func -> empty_summary | F f -> f.summary))
        in
        (* edge: const(s'') -> assign(s') *)
        let s' = Assign (num, var, (x0, x1, func, arg)) in
        let s'' = Const (num + 1, x1_var, (x1, Exp)) in
        (s', replace s s' graph |> add s'' s')
    | _ -> (s, graph)

  let recv_in_assign_rule2_1 s x1 f arg graph =
    (* x1: inner receiver *)
    match s with
    | Assign (num, var, (x0, _, _, _)) ->
        (* edge: const(s'') -> assign(s') *)
        let s' = Assign (num, var, (x0, x1, f, arg)) in
        let s'' = Const (num + 1, (get_v x1).variable, (x1, Exp)) in
        (s', replace s s' graph |> add s'' s')
    | _ -> (s, graph)

  let recv_in_assign_rule3 s id idx graph =
    match s with
    | Assign (num, var, (x0, _, func, arg)) ->
        let typ = match func with Func -> "" | F f -> f.typ in
        let x1_field =
          match func with
          | Func -> FieldSet.empty
          | F f ->
              get_field_from_ufmap "this" (fst f.summary.precond)
                f.summary.use_field
        in
        let x1 =
          Variable
            (mk_var
               (match func with Func -> "" | F f -> f.import)
               (Var (Object typ, id), Some idx)
               x1_field
               (match func with Func -> empty_summary | F f -> f.summary))
        in
        (* edge: assign(s'') --> stmt(s''') --> assign(s') *)
        let s' = Assign (num, var, (x0, x1, func, arg)) in
        let s'' = Stmt (num + 2, (get_v x1).variable) in
        let s''' =
          Assign (num + 1, (get_v x1).variable, (x1, Id, Func, Arg []))
        in
        (s', replace s s' graph |> add s'' s' |> add s''' s'')
    | _ -> (s, graph)

  let recv_in_assign_rule3_1 s x1 f arg graph =
    (* x1: inner receiver *)
    match s with
    | Assign (num, var, (x0, _, _, _)) ->
        (* edge: assign(s'') --> stmt(s''') --> assign(s') *)
        let s' = Assign (num, var, (x0, x1, f, arg)) in
        let s'' = Stmt (num + 2, (get_v x1).variable) in
        let s''' =
          Assign (num + 1, (get_v x1).variable, (x1, Id, Func, Arg []))
        in
        (s', replace s s' graph |> add s'' s' |> add s''' s'')
    | _ -> (s, graph)

  let recv_in_assign_rule4 s x1_node graph =
    match s with
    | Assign (num, var, (x0, _, func, arg)) ->
        (* receiver recycle *)
        let e_of_x1_node = get_edge_of_find_node x1_node var graph in
        let new_x1 = get_id x1_node in
        let s' = Assign (num, var, (x0, new_x1, func, arg)) in
        (s', replace s s' graph |> add e_of_x1_node s')
    | _ -> (s, graph)

  (* 5, 9 *)
  let mk_const_arg arg num graph =
    let s' = Const (num, (get_v arg).variable, (arg, Exp)) in
    add_vertex s' graph

  let mk_assign_arg arg num graph =
    let s' = Stmt (num + 1, (get_v arg).variable) in
    let s'' = Assign (num, (get_v arg).variable, (arg, Id, Func, Arg [])) in
    add s'' s' graph

  let mk_already_arg x_node x_var graph arg_graph =
    let e_of_x_node = get_edge_of_find_node x_node x_var graph in
    add_vertex e_of_x_node arg_graph

  let arg_in_assign_rule s arg_seq arg graph =
    match s with
    | Assign (num, var, (x0, x1, func, _)) ->
        let s' = Assign (num, var, (x0, x1, func, arg)) in
        let rep_graph = replace s s' graph in
        (s', connect_and_union s' rep_graph arg_seq)
    | _ -> (s, graph)

  let arg_in_void_rule s arg_seq arg graph =
    match s with
    | Void (num, var, (x, func, _)) ->
        let s' = Void (num, var, (x, func, arg)) in
        let rep_graph = replace s s' graph in
        (s', connect_and_union s' rep_graph arg_seq)
    | _ -> (s, graph)

  (* 6 *)

  let new_id id summary =
    Variable
      {
        import = (get_v id).import;
        variable = (get_v id).variable;
        field = (get_v id).field;
        summary;
      }

  let new_field id field =
    Variable
      {
        import = (get_v id).import;
        variable = (get_v id).variable;
        field;
        summary = (get_v id).summary;
      }

  let void_rule1 s graph =
    match s with
    | Stmt var ->
        let s' = Skip var in
        let succ = succ s graph in
        let g = add_vertex s' G.empty in
        let g = List.fold_left (fun g succ' -> add s' succ' g) g succ in
        (s', g)
    | _ -> (s, graph)

  let rec void_rule2 prev_s s graph =
    match s with
    | Stmt (num_s, var_s) -> (
        match prev_s with
        | Assign (num_a, var_a, (x0, x1, f, arg)) when is_array_init f ->
            void_rule2_array s num_a num_s var_a var_s x0 x1 f arg graph
        | Assign (_, _, (x0, _, _, _)) ->
            void_rule2_normal prev_s s num_s var_s x0 graph
        | _ -> (s, graph))
    | _ -> (s, graph)

  and void_rule2_normal prev_s s ns vs x0 graph =
    let s' = Void (ns, vs, (x0, Func, Arg [])) in
    let s'' = Stmt (ns + 1, vs) in
    let succ = succ s graph in
    let g = add_vertex s' G.empty in
    let g = List.fold_left (fun g succ' -> add s' succ' g) g succ in
    (s', add prev_s s'' g |> add s'' s')

  and void_rule2_array s na ns va vs x0 x1 f arg graph =
    let arr_id = get_vinfo x0 |> snd in
    let new_idx, new_elem = get_array_index arr_id (get_v x0).summary in
    (* remove setter of duplicate index *)
    if FieldSet.mem (snd new_idx |> get_index_value) (get_v x0).field then
      (s, graph)
    else
      let nfield =
        FieldSet.add (snd new_idx |> get_index_value) (get_v x0).field
      in
      let new_next_summary =
        next_summary_in_void (get_v x0).summary
          (remove_array_index arr_id (fst new_idx) (get_v x0).summary)
      in
      let new_current_summary =
        current_summary_in_assign (get_v x0).summary
          (array_field_var (get_v x0).summary (new_idx, new_elem))
          (array_current_mem (get_v x0).summary (new_idx, new_elem))
      in
      let assign =
        Assign
          (na, va, (new_id (new_field x0 nfield) new_next_summary, x1, f, arg))
      in
      let s' = Void (ns, vs, (new_id x0 new_current_summary, Func, Arg [])) in
      let s'' = Stmt (ns + 1, vs) in
      let succ = succ s graph in
      let g = add_vertex assign G.empty in
      let g = List.fold_left (fun g succ' -> add s' succ' g) g succ in
      (s', add_vertex assign g |> add assign s'' |> add s'' s')

  (* 7 *)
  let fcall_in_void_rule s f arg graph =
    match s with
    | Void (num, var, (x0, _, _)) ->
        let s' = Void (num, var, (x0, f, arg)) in
        (s', add_vertex s' G.empty)
    | _ -> (s, graph)

  (* 8 *)
  let recv_in_void_rule1 s c graph =
    match s with
    | Void (num, var, (_, func, arg)) ->
        let s' = Void (num, var, (c, func, arg)) in
        (s', replace s s' graph)
    | _ -> (s, graph)

  let recv_in_void_rule2 s id idx graph =
    match s with
    | Void (num, var, (_, func, arg)) ->
        let typ = match func with Func -> "" | F f -> f.typ in
        let x_field =
          match func with
          | Func -> FieldSet.empty
          | F f ->
              get_field_from_ufmap "this" (fst f.summary.precond)
                f.summary.use_field
        in
        let x =
          Variable
            (mk_var
               (match func with Func -> "" | F f -> f.import)
               (Var (Object typ, id), Some idx)
               x_field
               (match func with Func -> empty_summary | F f -> f.summary))
        in
        let s' = Void (num, var, (x, func, arg)) in
        let s'' = Const (num + 1, (get_v x).variable, (x, Exp)) in
        (s', replace s s' graph |> add s'' s')
    | _ -> (s, graph)

  let recv_in_void_rule3 s id idx graph =
    match s with
    | Void (num, var, (_, func, arg)) ->
        let typ = match func with Func -> "" | F f -> f.typ in
        let x_field =
          match func with
          | Func -> FieldSet.empty
          | F f ->
              get_field_from_ufmap "this" (fst f.summary.precond)
                f.summary.use_field
        in
        let x =
          Variable
            (mk_var
               (match func with Func -> "" | F f -> f.import)
               (Var (Object typ, id), Some idx)
               x_field
               (match func with Func -> empty_summary | F f -> f.summary))
        in
        let s' = Void (num, var, (x, func, arg)) in
        let s'' = Stmt (num + 2, (get_v x).variable) in
        let s''' =
          Assign (num + 1, (get_v x).variable, (x, Id, Func, Arg []))
        in
        (s', replace s s' graph |> add s''' s'' |> add s'' s')
    | _ -> (s, graph)

  (* ************************************** *
     Return Code
   * ************************************** *)

  let get_method_name m =
    Regexp.first_rm (Str.regexp "(.*)") m
    |> Str.split Regexp.dot |> List.rev |> List.hd

  let get_short_class_name c =
    Regexp.first_rm (Str.regexp "\\.<init>(.*)") c
    |> Str.split Regexp.dot |> List.rev |> List.hd

  let array_code dim content =
    let rec code d = if d = 0 then "" else "[" ^ content ^ "]" ^ code (d - 1) in
    code dim

  let arg_code f arg =
    let cc code x idx = code ^ ", " ^ x ^ string_of_int idx in
    match arg with
    | Param p ->
        let param =
          List.fold_left
            (fun pc p ->
              match p.variable with
              | Var (_, id), None ->
                  (id |> get_short_class_name) ^ ".class" (* mock *)
              | Var (_, id), Some idx -> cc pc id idx
              | _ -> pc)
            "" p
          |> Regexp.rm_first_rest
        in
        if is_array_init f then
          array_code
            (Utils.get_array_dim_from_class_name (get_func f).typ)
            param
        else if is_array_set f then
          let lst = Str.split Regexp.bm param in
          array_code
            (Utils.get_array_dim_from_class_name (get_func f).typ)
            (List.hd lst |> Regexp.rm_space)
          ^ " = "
          ^ (List.tl lst |> List.hd |> Regexp.rm_space)
        else "(" ^ param ^ ")"
    | Arg x -> "Arg(" ^ (List.length x |> string_of_int) ^ ")"

  let func_code func =
    match func with
    | F f ->
        if is_array_init func then
          Utils.rm_object_array_import f.typ
          |> Str.split Regexp.dot |> List.rev |> List.hd
          |> Regexp.first_rm (Str.regexp "Array[0-9]*")
          |> Utils.get_array_class_name |> String.cat "new "
        else if is_array_set func then ""
        else if Utils.is_init_method f.method_name then
          get_short_class_name f.method_name
          |> Utils.replace_nested_symbol |> String.cat "new "
        else get_method_name f.method_name |> Utils.replace_nested_symbol
    | _ -> "Func"

  let is_var = function Variable _ -> true | _ -> false

  and is_cn = function ClassName _ -> true | _ -> false

  let var_code v =
    let v =
      match v.variable with
      | Var (typ, id), Some idx -> (typ, id ^ string_of_int idx)
      | _, None -> (NonType, "")
      | This _, _ -> (NonType, "")
    in
    match fst v with
    | Int -> "int " ^ snd v
    | Long -> "long " ^ snd v
    | Short -> "short " ^ snd v
    | Byte -> "byte " ^ snd v
    | Float -> "float " ^ snd v
    | Double -> "double " ^ snd v
    | Bool -> "boolean " ^ snd v
    | Char -> "char " ^ snd v
    | String -> "String " ^ snd v
    | Object name ->
        (get_short_class_name name |> Utils.replace_nested_symbol) ^ " " ^ snd v
    | Array typ -> (
        match get_array_typ typ with
        | Int -> "int" ^ array_code (get_array_dim typ) "" ^ " " ^ snd v
        | Long -> "long" ^ array_code (get_array_dim typ) "" ^ " " ^ snd v
        | Short -> "short" ^ array_code (get_array_dim typ) "" ^ " " ^ snd v
        | Byte -> "byte" ^ array_code (get_array_dim typ) "" ^ " " ^ snd v
        | Float -> "float" ^ array_code (get_array_dim typ) "" ^ " " ^ snd v
        | Double -> "double" ^ array_code (get_array_dim typ) "" ^ " " ^ snd v
        | Char -> "char" ^ array_code (get_array_dim typ) "" ^ " " ^ snd v
        | String -> "String" ^ array_code (get_array_dim typ) "" ^ " " ^ snd v
        | Object name ->
            (get_short_class_name name |> Utils.replace_nested_symbol)
            ^ array_code (get_array_dim typ) ""
            ^ " " ^ snd v
        | _ -> "")
    | _ -> ""

  let recv_name_code recv func =
    match recv with
    | Variable v -> (
        match v.variable with
        | Var (_, id), Some idx when is_array_set func -> id ^ string_of_int idx
        | Var (_, id), Some idx -> id ^ string_of_int idx ^ "."
        | _ -> "")
    | ClassName c when c = "Mockito" -> "" (* mock *)
    | ClassName c ->
        (get_short_class_name c |> Utils.replace_nested_symbol) ^ "."
    | _ -> "ID."

  let id_code = function
    | Variable v -> var_code v
    | ClassName c -> c
    | Id -> "ID"

  let primitive_code p x =
    match p with
    | Z z -> (
        match get_vinfo x |> fst with
        | Bool -> if z = 0 then string_of_bool false else string_of_bool true
        | String -> "\"" ^ string_of_int z ^ "\""
        | _ -> string_of_int z)
    | R r ->
        (* e.g., float --> 0.f, double --> 0. *)
        let type_cast =
          match get_vinfo x |> fst with Float -> "f" | _ -> ""
        in
        string_of_float r ^ type_cast
    | B b -> string_of_bool b
    | C c -> "\'" ^ String.make 1 c ^ "\'"
    | S s ->
        let replace s =
          Str.global_replace (Str.regexp "\\") "\\\\\\\\" s
          |> Str.global_replace (Str.regexp "\"") "\\\""
          |> Str.global_replace (Str.regexp "\'") "\\\'"
        in
        "\"" ^ replace s ^ "\""

  let loop_id_lval_code v =
    match (get_v v).variable with
    | Var (typ, id), Some idx -> (typ, "unitcon_" ^ id ^ string_of_int idx)
    | _, None -> (NonType, "")
    | This _, _ -> (NonType, "")

  let loop_id_lval_for_check v =
    match (get_v v).variable with
    | Var (typ, id), Some idx -> (typ, id ^ string_of_int idx)
    | _, None -> (NonType, "")
    | This _, _ -> (NonType, "")

  let exp_code exp x =
    match exp with
    | Primitive p -> primitive_code p x
    | GlobalConstant g -> Utils.replace_nested_symbol g
    | Null -> (
        (* If type inference from the summaries is fail,
           correct it in the code output step. *)
        match get_vinfo x |> fst with
        | Int | Short | Byte | Char -> "0"
        | Long -> "0l"
        | Float -> "0.f"
        | Double -> "0."
        | Bool -> "false"
        | _ -> "null")
    | WithLoop ->
        if !Cmdline.with_loop then
          let v_type, v_id = loop_id_lval_code x in
          match v_type with
          | Int | Long | Short | Byte | Char | Float | Double | Bool | String
          | Object _ ->
              v_id ^ "_comb[" ^ v_id ^ "_index]"
          | _ -> "Exp"
        else "Exp"
    | Exp -> "Exp"

  let code = function
    | Const (_, _, (x, exp)) -> id_code x ^ " = " ^ exp_code exp x ^ ";\n"
    | Assign (_, _, (x0, x1, func, arg)) ->
        if is_var x1 then
          id_code x0 ^ " = " ^ recv_name_code x1 func ^ func_code func
          ^ arg_code func arg ^ ";\n"
        else if Utils.is_init_method (get_func func).method_name then
          let code =
            id_code x0 ^ " = " ^ func_code func ^ arg_code func arg ^ ";\n"
          in
          if is_file func then
            code ^ recv_name_code x0 func ^ "createNewFile();\n"
          else code
        else
          id_code x0 ^ " = " ^ recv_name_code x1 func ^ func_code func
          ^ arg_code func arg ^ ";\n"
    | Void (_, _, (x, func, arg)) ->
        if Utils.is_init_method (get_func func).method_name then
          func_code func ^ arg_code func arg ^ ";\n"
        else recv_name_code x func ^ func_code func ^ arg_code func arg ^ ";\n"
    | Skip _ -> ""
    | Stmt _ -> "Stmt"

  let loop_id_code loop_id exp_list =
    let v = loop_id_lval_code loop_id in
    let lval =
      match fst v with
      | Int -> "int[] " ^ snd v
      | Long -> "long[] " ^ snd v
      | Short -> "short[] " ^ snd v
      | Byte -> "byte[] " ^ snd v
      | Float -> "float[] " ^ snd v
      | Double -> "double[] " ^ snd v
      | Bool -> "boolean[] " ^ snd v
      | Char -> "char[] " ^ snd v
      | String -> "String[] " ^ snd v
      | Object name ->
          (get_short_class_name name |> Utils.replace_nested_symbol)
          ^ "[] " ^ snd v
      | _ -> ""
    in
    let rec rval id exps =
      match exps with hd :: tl -> ", " ^ exp_code hd id ^ rval id tl | _ -> ""
    in
    let rec string_rval id exps =
      match exps with
      | hd :: tl -> ", \"" ^ exp_code hd id ^ "\"" ^ string_rval id tl
      | _ -> ""
    in
    let comb_func_name = function
      | Int -> "Int"
      | Long -> "Long"
      | Short -> "Short"
      | Byte -> "Byte"
      | Float -> "Float"
      | Double -> "Double"
      | Char -> "Char"
      | Bool -> "Bool"
      | String -> "String"
      | _ -> ""
    in
    if is_primitive (fst v) then
      if !Cmdline.unknown_bug then
        lval ^ "_comb = " ^ "{"
        ^ Regexp.rm_first_rest (rval loop_id exp_list)
        ^ "};\n"
      else
        lval ^ " = " ^ "{"
        ^ Regexp.rm_first_rest (rval loop_id exp_list)
        ^ "};\n" ^ lval ^ "_comb = UnitconCombinator.combine"
        ^ comb_func_name (fst v)
        ^ "(" ^ snd v ^ ");\n"
    else
      lval ^ "_comb = " ^ "{"
      ^ Regexp.rm_first_rest (rval loop_id exp_list)
      ^ "};\n"
      ^ ("String[] " ^ snd v)
      ^ "_string_comb = " ^ "{"
      ^ Regexp.rm_first_rest (string_rval loop_id exp_list)
      ^ "};\n"

  let topological_code g =
    Topological.fold (fun node codes -> codes ^ code node) g ""
end
