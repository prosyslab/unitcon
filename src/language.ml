module Json = Yojson.Safe
module JsonUtil = Yojson.Safe.Util

let compare_string = String.compare

let compare_list = List.compare

type method_name = string [@@deriving compare]

type class_name = string [@@deriving compare]

type file_name = string [@@deriving compare]

type modifier = Public | Private | Protected | Default [@@deriving compare]

type class_type =
  | Abstract
  | Static
  | Private
  | Abstract_and_Static
  | Normal
  | Interface
[@@deriving compare]

type typ =
  | Int
  | Long
  | Float
  | Double
  | Bool
  | Char
  | String
  | Object of class_name
  | Array of typ
  | None
[@@deriving compare]

type id = string (*e.g. i *) [@@deriving compare]

type variable = This of typ | Var of typ * id [@@deriving compare]

type import = string (* package.class *) [@@deriving compare]

type params = (import * variable) list [@@deriving compare]

type symbol = string (*e.g. v1 *) [@@deriving compare]

let get_class_name = function
  | Object n -> n
  | Array typ -> (
      match typ with
      | Int -> "IntArray"
      | Long -> "LongArray"
      | Float -> "FloatArray"
      | Double -> "DoubleArray"
      | Bool -> "BoolArray"
      | Char -> "CharArray"
      | String -> "StringArray"
      | Object _ -> "ObjectArray"
      | _ -> "")
  | None -> ""
  | _ -> failwith "get_class_name: not supported"

let modifier_of_json json =
  JsonUtil.to_string json |> function
  | "Public" -> Public
  | "Private" -> Private
  | "Protected" -> Protected
  | "Default" -> Default
  | s -> failwith ("Unknown modifier " ^ s)

module MethodInfo = struct
  module M = Map.Make (struct
    type t = method_name [@@deriving compare]
  end)

  type info = {
    modifier : modifier;
    is_static : bool;
    formal_params : params;
    return : string;
    filename : file_name;
  }

  type t = info M.t
end

module Relation = struct
  module M = Map.Make (struct
    type t = symbol [@@deriving compare]
  end)

  type t = symbol M.t
end

module Value = struct
  type value =
    | Int of int
    | Long of int
    | Float of float
    | Double of float
    | Bool of bool
    | Char of char
    | String of string
    | PlusInf
    | MinusInf
    | Null
    | None (* Determining whether to use the default value *)

  type op =
    | Eq of value
    | Neq of value
    | Le of value
    | Lt of value
    | Ge of value
    | Gt of value
    | Between of value * value
    | Outside of value * value

  module M = Map.Make (struct
    type t = symbol [@@deriving compare]
  end)

  type t = op M.t

  let is_le str = String.contains str '<' && String.contains str '='

  let is_lt str = String.contains str '<' && String.contains str '=' |> not

  let is_ge str = String.contains str '>' && String.contains str '='

  let is_gt str = String.contains str '>' && String.contains str '=' |> not

  let is_neq str = String.contains str '!' && String.contains str '='

  let is_eq str =
    String.contains str '='
    && String.contains str '!' |> not
    && String.contains str '>' |> not
    && String.contains str '<' |> not

  let is_between str =
    Str.string_match (Str.regexp "in_N") str 0
    || Str.string_match (Str.regexp "in\\[") str 0

  let is_outside str = Str.string_match (Str.regexp "not_in\\[") str 0
end

module Condition = struct
  type rh = RH_Var of id | RH_Symbol of symbol | RH_Index of symbol | RH_Any
  [@@deriving compare]

  module M = Map.Make (struct
    type t = rh [@@deriving compare]
  end)

  type var = rh M.t

  type mem = rh M.t M.t

  type t = var * mem
end

type summary = {
  relation : Relation.t;
  value : Value.t;
  precond : Condition.t;
  postcond : Condition.t;
  args : symbol list;
}

let empty_summary =
  {
    relation = Relation.M.empty;
    value = Value.M.empty;
    precond = (Condition.M.empty, Condition.M.empty);
    postcond = (Condition.M.empty, Condition.M.empty);
    args = [];
  }

module SummaryMap = struct
  module M = Map.Make (struct
    type t = method_name [@@deriving compare]
  end)

  type t = summary list M.t
end

module CallPropMap = struct
  module M = Map.Make (struct
    (* (caller * callee) *)
    type t = method_name * method_name [@@deriving compare]
  end)

  type t = summary list M.t
end

module ClassInfo = struct
  module M = Map.Make (struct
    type t = class_name [@@deriving compare]
  end)

  type info = { class_type : class_type }

  type t = info M.t
end

module FieldSet = struct
  module S = Set.Make (struct
    type t = string [@@deriving compare]
  end)

  type t = S.t
end

module SetterMap = struct
  module M = Map.Make (struct
    type t = class_name [@@deriving compare]
  end)

  type setter = method_name * FieldSet.t

  type t = setter list M.t
end

module EnumInfo = struct
  module M = Map.Make (struct
    type t = string [@@deriving compare]
  end)

  type const = string

  type t = const list M.t (* key: enum name, value: enum const list *)
end

module AST = struct
  type var = {
    import : import;
    variable : variable * int option;
    field : FieldSet.t;
    summary : summary;
  }

  type f = {
    typ : string;
    method_name : method_name;
    import : import;
    summary : summary;
  }

  type func_type = FA | FV

  type arg = Param of var list | Arg of var list

  type func = F of f | Func

  type id = Variable of var | ClassName of string | Id

  type primitive = Z of int | R of float | B of bool | C of char | S of string

  type exp = Primitive of primitive | GlobalConstant of string | Null | Exp

  type t =
    | Const of (id * exp)
    | Assign of (id * id * func * arg)
    | Void of (id * func * arg)
    | Seq of (t * t)
    | Skip
    | Stmt

  let empty_var =
    {
      import = "";
      variable = (This None, None);
      field = FieldSet.S.empty;
      summary = empty_summary;
    }

  (* id -> var*)
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

  let is_stmt = function Stmt -> true | _ -> false

  and is_arg = function Arg _ -> true | _ -> false

  and is_func = function Func -> true | _ -> false

  and is_id = function Id -> true | _ -> false

  and is_exp = function Exp -> true | _ -> false

  let rec ground = function
    | Const (x, exp) -> (is_id x || is_exp exp) |> not
    | Assign (x0, x1, func, arg) ->
        (is_id x0 || is_id x1 || is_func func || is_arg arg) |> not
    | Void (x, func, arg) -> (is_id x || is_func func || is_arg arg) |> not
    | Seq (s1, s2) -> ground s1 && ground s2
    | Skip -> true
    | Stmt -> false

  let rec assign_ground = function
    | Const (x, exp) -> (is_id x || is_exp exp) |> not
    | Assign (x0, x1, func, arg) ->
        (is_id x0 || is_id x1 || is_func func || is_arg arg) |> not
    | Void (x, func, arg) -> (is_id x || is_func func || is_arg arg) |> not
    | Seq (s1, s2) -> assign_ground s1 && assign_ground s2
    | Skip -> true
    | Stmt -> true

  let rec last_code p = match p with Seq (_, s) -> last_code s | _ -> p

  let rec modify_last_assign p =
    match p with
    | Seq (s1, s2) -> Seq (s1, modify_last_assign s2)
    | Assign _ when ground p -> Skip
    | _ -> p

  let rec count_dist_arg arg =
    match arg with
    | hd :: tl ->
        count_dist_arg tl
        + List.fold_left (fun cnt x -> if hd = x then 0 else cnt) 1 tl
    | _ -> 1

  let rec count_nt = function
    | Const (x, exp) -> count_id x + count_exp exp
    | Assign (x0, x1, func, arg) ->
        count_id x0 + count_id x1 + count_func func FA + count_arg arg
    | Void (x, func, arg) -> count_id x + count_func func FV + count_arg arg
    | Seq (s1, s2) -> count_nt s1 + count_nt s2
    | Skip -> 0
    | Stmt -> 1

  and count_arg arg =
    match arg with
    | Arg a ->
        (2 |> float_of_int) ** (count_dist_arg a |> float_of_int)
        |> int_of_float
    | _ -> 0

  and count_func func typ =
    match func with
    | _ when typ = FV -> 100
    | Func -> 1
    | F f when typ = FA ->
        if Str.string_match (Str.regexp ".*\\.<init>") f.method_name 0 then 0
        else 200
    | _ -> 0

  and count_id = function Id -> 1 | _ -> 0

  and count_exp = function Exp -> 1 | _ -> 0

  let is_array f =
    let fname = (get_func f).method_name in
    if Str.string_match (".*Array\\.<init>" |> Str.regexp) fname 0 then true
    else false

  let is_array_set f =
    let fname = (get_func f).method_name in
    if Str.string_match (".*Array\\.set" |> Str.regexp) fname 0 then true
    else false

  let is_file f =
    let fname = (get_func f).method_name in
    if Str.string_match ("File\\.<init>" |> Str.regexp) fname 0 then true
    else false

  (* ************************************** *
     Checking for Synthesis Rules
   * ************************************** *)

  (* 1. x := Exp *)
  let const = function
    | Const (x, exp) -> is_id x |> not && is_exp exp
    | _ -> false

  (* 2. x := ID.F(ID) *)
  let fcall_in_assign = function
    | Assign (x0, x1, func, arg) ->
        is_id x0 |> not && is_id x1 && is_func func && is_arg arg
    | _ -> false

  (* 3. x := ID.f(ID) *)
  let recv_in_assign = function
    | Assign (x0, x1, func, arg) ->
        is_id x0 |> not && is_id x1 && is_func func |> not && is_arg arg
    | _ -> false

  (* 4. x0 := x1.f(ID) *)
  let arg_in_assign = function
    | Assign (x0, x1, func, arg) ->
        is_id x0 |> not && is_id x1 |> not && is_func func |> not && is_arg arg
    | _ -> false

  (* 5. x0 := x1.f(arg); Stmt *)
  let void = function
    | Seq (s1, s2) -> (
        match s1 with
        | Assign (x0, x1, func, arg) ->
            is_id x0 |> not
            && is_id x1 |> not
            && is_func func |> not
            && is_arg arg |> not
            && is_stmt s2
        | _ -> false)
    | _ -> false

  (* 6. ID.F(ID) *)
  let fcall1_in_void = function
    | Void (x, func, arg) -> is_id x && is_func func && is_arg arg
    | _ -> false

  (* 7. ID.F(ID) *)
  let fcall2_in_void = function
    | Void (x, func, arg) -> is_id x |> not && is_func func && is_arg arg
    | _ -> false

  (* 8. ID.f(ID) *)
  let recv_in_void = function
    | Void (x, func, arg) -> is_id x && is_func func |> not && is_arg arg
    | _ -> false

  (* 9. x.f(ID) *)
  let arg_in_void = function
    | Void (x, func, arg) -> is_id x |> not && is_func func |> not && is_arg arg
    | _ -> false

  (* ************************************** *
     Synthesis Rules
   * ************************************** *)

  (* 1 *)
  let const_rule1 s n = match s with Const (x, _) -> Const (x, n) | _ -> s

  let const_rule2 s g = match s with Const (x, _) -> Const (x, g) | _ -> s

  let const_rule3 s = match s with Const (x, _) -> Const (x, Null) | _ -> s

  (* 2 *)
  let fcall_in_assign_rule s field f arg =
    match s with
    | Assign (x0, x1, _, _) ->
        let new_x0 =
          Variable
            {
              import = (x0 |> get_v).import;
              variable = (x0 |> get_v).variable;
              field;
              summary = (x0 |> get_v).summary;
            }
        in
        Assign (new_x0, x1, f, arg)
    | _ -> s

  (* 3 *)
  let recv_in_assign_rule1 s c =
    match s with
    | Assign (x0, _, func, arg) -> Assign (x0, c, func, arg)
    | _ -> s

  let recv_in_assign_rule2 s id idx =
    match s with
    | Assign (x0, _, func, arg) ->
        let typ = match func with Func -> "" | F f -> f.typ in
        let x1 =
          Variable
            {
              import = (match func with Func -> "" | F f -> f.import);
              variable = (Var (Object typ, id), Some idx);
              field = FieldSet.S.empty;
              summary =
                (match func with Func -> empty_summary | F f -> f.summary);
            }
        in
        Seq (Const (x1, Exp), Assign (x0, x1, func, arg))
    | _ -> s

  let recv_in_assign_rule3 s id idx =
    match s with
    | Assign (x0, _, func, arg) ->
        let typ = match func with Func -> "" | F f -> f.typ in
        let x1 =
          Variable
            {
              import = (match func with Func -> "" | F f -> f.import);
              variable = (Var (Object typ, id), Some idx);
              field = FieldSet.S.empty;
              summary =
                (match func with Func -> empty_summary | F f -> f.summary);
            }
        in
        Seq
          (Seq (Assign (x1, Id, Func, Arg []), Stmt), Assign (x0, x1, func, arg))
    | _ -> s

  let recv_in_assign_rule2_1 s recv f arg =
    match s with
    | Assign (x0, _, _, _) -> Seq (Const (recv, Exp), Assign (x0, recv, f, arg))
    | _ -> s

  let recv_in_assign_rule3_1 s recv f arg =
    match s with
    | Assign (x0, _, _, _) ->
        Seq
          ( Seq (Assign (recv, Id, Func, Arg []), Stmt),
            Assign (x0, recv, f, arg) )
    | _ -> s

  (* 4, 9 *)
  let mk_const_arg s arg = Seq (s, Const (arg, Exp))

  let mk_assign_arg s arg = Seq (s, Seq (Assign (arg, Id, Func, Arg []), Stmt))

  let arg_in_assign_rule s arg_seq arg =
    match s with
    | Assign (x0, x1, func, _) -> Seq (arg_seq, Assign (x0, x1, func, arg))
    | _ -> s

  let arg_in_void_rule s arg_seq arg =
    match s with
    | Void (x, func, _) -> Seq (arg_seq, Void (x, func, arg))
    | _ -> s

  (* functions for 5 *)
  let rec get_tail_symbol field_name symbol memory =
    let next_symbol = Condition.M.find_opt symbol memory in
    match next_symbol with
    | Some sym -> (
        match Condition.M.find_opt (Condition.RH_Var field_name) sym with
        | Some s -> get_tail_symbol field_name s memory
        | None -> (
            match Condition.M.find_opt Condition.RH_Any sym with
            | Some any_sym -> get_tail_symbol field_name any_sym memory
            | None -> symbol))
    | None -> symbol

  let get_rh_name rh = match rh with Condition.RH_Symbol s -> s | _ -> ""

  let get_index_value v =
    match v with
    | Value.Eq (Int i) -> i |> string_of_int
    | Value.Ge (Int i) -> i |> string_of_int
    | Value.Gt (Int i) -> i + 1 |> string_of_int
    | _ -> ""

  let org_symbol id summary =
    let variable, memory = summary.precond in
    let id_symbol =
      Condition.M.fold
        (fun symbol symbol_id id_symbol ->
          match symbol_id with
          | Condition.RH_Var v when v = id -> symbol |> get_rh_name
          | _ -> id_symbol)
        variable ""
    in
    Condition.M.fold
      (fun symbol symbol_trace find_variable ->
        let symbol = get_rh_name symbol in
        if symbol = id_symbol then
          Condition.M.fold
            (fun _ tail trace_find_var ->
              match tail with Condition.RH_Symbol s -> s | _ -> trace_find_var)
            symbol_trace find_variable
        else find_variable)
      memory ""

  let get_array_index array summary =
    let _, memory = summary.precond in
    let array_symbol = org_symbol array summary in
    let values = summary.value in
    let find_value s =
      Value.M.fold
        (fun symbol value find_value ->
          if symbol = s then value else find_value)
        values (Value.Eq None)
    in
    match Condition.M.find_opt (Condition.RH_Symbol array_symbol) memory with
    | Some x ->
        Condition.M.fold
          (fun sym v ((idx, idx_value), (elem, elem_value)) ->
            match sym with
            | Condition.RH_Index s when idx = "" ->
                ( (s, find_value s),
                  ( v |> get_rh_name,
                    find_value (get_tail_symbol "" v memory |> get_rh_name) ) )
            | _ -> ((idx, idx_value), (elem, elem_value)))
          x
          (("", Value.Ge (Int 0)), ("", Value.Eq None))
    | None -> (("", Value.Ge (Int 0)), ("", Value.Eq None))

  let remove_array_index array idx summary =
    let _, memory = summary.precond in
    let array_symbol = org_symbol array summary in
    match Condition.M.find_opt (Condition.RH_Symbol array_symbol) memory with
    | Some x ->
        let array_new_mem =
          Condition.M.fold
            (fun sym _ new_mem ->
              match sym with
              | Condition.RH_Index i when idx = i ->
                  Condition.M.remove sym new_mem
              | _ -> new_mem)
            x x
        in
        Condition.M.add (Condition.RH_Symbol array_symbol) array_new_mem memory
    | None -> memory

  let array_field_var org_summary array =
    Condition.M.add
      (Condition.RH_Symbol (array |> fst |> fst))
      (Condition.RH_Var "index")
      (org_summary.precond |> fst)
    |> Condition.M.add
         (Condition.RH_Symbol (array |> snd |> fst))
         (Condition.RH_Var "elem")

  let array_current_mem org_summary array =
    Condition.M.add (Condition.RH_Symbol "v5")
      (Condition.M.add (Condition.RH_Var "index")
         (Condition.RH_Symbol (array |> fst |> fst))
         Condition.M.empty)
      (org_summary.precond |> snd)
    |> Condition.M.add (Condition.RH_Var "elem")
         (Condition.M.add Condition.RH_Any
            (Condition.RH_Symbol (array |> snd |> fst))
            Condition.M.empty)

  let next_summary_in_void org_summary new_mem =
    {
      relation = org_summary.relation;
      value = org_summary.value;
      precond = (org_summary.precond |> fst, new_mem);
      postcond = (org_summary.postcond |> fst, new_mem);
      args = org_summary.args;
    }

  let current_summary_in_assign org_summary new_var new_mem =
    {
      relation = org_summary.relation;
      value = org_summary.value;
      precond = (new_var, new_mem);
      postcond = (new_var, new_mem);
      args = org_summary.args;
    }

  let new_seq assign void = Seq (Seq (assign, Stmt), void)

  let new_id id summary =
    Variable
      {
        import = (id |> get_v).import;
        variable = (id |> get_v).variable;
        field = (id |> get_v).field;
        summary;
      }

  let new_field id field =
    Variable
      {
        import = (id |> get_v).import;
        variable = (id |> get_v).variable;
        field;
        summary = (id |> get_v).summary;
      }

  (* 5 *)
  let void_rule1 s = match s with Seq (s1, _) -> Seq (s1, Skip) | _ -> s

  let void_rule2_array x0 x1 f arg =
    let arr_id = x0 |> get_vinfo |> snd in
    let new_idx, new_elem = get_array_index arr_id (x0 |> get_v).summary in
    (* remove setter of duplicate index *)
    if FieldSet.S.mem (new_idx |> snd |> get_index_value) (x0 |> get_v).field
    then []
    else
      let nfield =
        FieldSet.S.add (new_idx |> snd |> get_index_value) (x0 |> get_v).field
      in
      let new_next_summary =
        next_summary_in_void (x0 |> get_v).summary
          (remove_array_index arr_id (new_idx |> fst) (x0 |> get_v).summary)
      in
      let new_current_summary =
        current_summary_in_assign (x0 |> get_v).summary
          (array_field_var (x0 |> get_v).summary (new_idx, new_elem))
          (array_current_mem (x0 |> get_v).summary (new_idx, new_elem))
      in
      [
        new_seq
          (Assign (new_id (new_field x0 nfield) new_next_summary, x1, f, arg))
          (Void (new_id x0 new_current_summary, Func, Arg []));
      ]

  let void_rule2_normal x0 x1 f arg =
    let remove = FieldSet.S.remove in
    FieldSet.S.fold
      (fun field lst ->
        new_seq
          (Assign (new_field x0 (remove field (x0 |> get_v).field), x1, f, arg))
          (Void (new_field x0 (FieldSet.S.singleton field), Func, Arg []))
        :: lst)
      (x0 |> get_v).field []

  let void_rule2 s =
    match s with
    | Seq (s1, _) -> (
        match s1 with
        | Assign (x0, x1, f, arg) ->
            if is_array f then void_rule2_array x0 x1 f arg
            else void_rule2_normal x0 x1 f arg
        | _ -> [ s ])
    | _ -> [ s ]

  (* 6, 7 *)
  let fcall_in_void_rule s f arg =
    match s with Void (x0, _, _) -> Void (x0, f, arg) | _ -> s

  (* 8 *)
  let recv_in_void_rule1 s c =
    match s with Void (_, func, arg) -> Void (c, func, arg) | _ -> s

  let recv_in_void_rule2 s id idx =
    match s with
    | Void (_, func, arg) ->
        let typ = match func with Func -> "" | F f -> f.typ in
        let x =
          Variable
            {
              import = (match func with Func -> "" | F f -> f.import);
              variable = (Var (Object typ, id), Some idx);
              field = FieldSet.S.empty;
              summary =
                (match func with Func -> empty_summary | F f -> f.summary);
            }
        in
        Seq (Const (x, Exp), Void (x, func, arg))
    | _ -> s

  let recv_in_void_rule3 s id idx =
    match s with
    | Void (_, func, arg) ->
        let typ = match func with Func -> "" | F f -> f.typ in
        let x =
          Variable
            {
              import = (match func with Func -> "" | F f -> f.import);
              variable = (Var (Object typ, id), Some idx);
              field = FieldSet.S.empty;
              summary =
                (match func with Func -> empty_summary | F f -> f.summary);
            }
        in
        Seq (Seq (Assign (x, Id, Func, Arg []), Stmt), Void (x, func, arg))
    | _ -> s

  (* ************************************** *
     Return Code
   * ************************************** *)

  let arg_code f arg =
    let cc code x idx = code ^ ", " ^ x ^ (idx |> string_of_int) in
    match arg with
    | Param p ->
        let param =
          List.fold_left
            (fun pc p ->
              match p.variable with
              | Var (_, id), Some idx -> cc pc id idx
              | _ -> pc)
            "" p
          |> Regexp.rm_first_rest
        in
        if is_array f then "[" ^ param ^ "]"
        else if is_array_set f then
          let lst = param |> Str.split Regexp.bm in
          "["
          ^ (lst |> List.hd |> Regexp.rm_space)
          ^ "] = "
          ^ (lst |> List.tl |> List.hd |> Regexp.rm_space)
        else "(" ^ param ^ ")"
    | Arg x -> "Arg(" ^ (x |> List.length |> string_of_int) ^ ")"

  let func_code func =
    match func with
    | F f ->
        if is_array func then
          Str.split Regexp.dot f.method_name
          |> List.hd
          |> Regexp.first_rm (Str.regexp "Array")
          |> String.cat "new "
        else if is_array_set func then ""
        else if Str.string_match (".*\\.<init>" |> Str.regexp) f.method_name 0
        then
          Str.split Regexp.dot f.method_name
          |> List.hd
          |> Str.global_replace Regexp.dollar "."
          |> String.cat "new "
        else
          Str.split Regexp.dot f.method_name
          |> List.tl |> List.hd
          |> Regexp.global_rm (Str.regexp "(.*)$")
          |> Str.global_replace Regexp.dollar "."
    | _ -> "Func"

  let is_var = function Variable _ -> true | _ -> false

  and is_cn = function ClassName _ -> true | _ -> false

  let var_code v =
    let v =
      match v.variable with
      | Var (typ, id), Some idx -> (typ, id ^ (idx |> string_of_int))
      | _, None -> (None, "")
      | This _, _ -> (None, "")
    in
    match v |> fst with
    | Int -> "int " ^ (v |> snd)
    | Long -> "long " ^ (v |> snd)
    | Float -> "float " ^ (v |> snd)
    | Double -> "double " ^ (v |> snd)
    | Bool -> "boolean " ^ (v |> snd)
    | Char -> "char " ^ (v |> snd)
    | String -> "String " ^ (v |> snd)
    | Object name ->
        (name |> Str.global_replace Regexp.dollar ".") ^ " " ^ (v |> snd)
    | Array typ -> (
        match typ with
        | Int -> "int[] " ^ (v |> snd)
        | Long -> "long[] " ^ (v |> snd)
        | Float -> "float[] " ^ (v |> snd)
        | Double -> "double[] " ^ (v |> snd)
        | Char -> "char[] " ^ (v |> snd)
        | String -> "String[] " ^ (v |> snd)
        | Object _ -> "Object[] " ^ (v |> snd)
        | _ -> "")
    | _ -> ""

  let recv_name_code recv func =
    match recv with
    | Variable v -> (
        match v.variable with
        | Var (_, id), Some idx when is_array_set func ->
            id ^ (idx |> string_of_int)
        | Var (_, id), Some idx -> id ^ (idx |> string_of_int) ^ "."
        | _ -> "")
    | ClassName c -> (c |> Str.global_replace Regexp.dollar ".") ^ "."
    | _ -> "ID."

  let id_code = function
    | Variable v -> var_code v
    | ClassName c -> c
    | Id -> "ID"

  let primitive_code p x =
    match p with
    | Z z -> (
        match get_vinfo x |> fst with
        | Bool ->
            if z = 0 then (false |> string_of_bool) ^ ";\n"
            else (true |> string_of_bool) ^ ";\n"
        | String -> "\"" ^ (z |> string_of_int) ^ "\";\n"
        | _ -> (z |> string_of_int) ^ ";\n")
    | R r -> (r |> string_of_float) ^ ";\n"
    | B b -> (b |> string_of_bool) ^ ";\n"
    | C c -> "\'" ^ String.make 1 c ^ "\';\n"
    | S s -> "\"" ^ s ^ "\";\n"

  let exp_code exp x =
    match exp with
    | Primitive p -> primitive_code p x
    | GlobalConstant g -> (g |> Str.global_replace Regexp.dollar ".") ^ ";\n"
    | Null -> "null;\n"
    | Exp -> "Exp;\n"

  let rec code = function
    | Const (x, exp) -> id_code x ^ " = " ^ exp_code exp x
    | Assign (x0, x1, func, arg) ->
        if is_var x1 then
          id_code x0 ^ " = " ^ recv_name_code x1 func ^ func_code func
          ^ arg_code func arg ^ ";\n"
        else if
          Str.string_match
            (".*\\.<init>" |> Str.regexp)
            (get_func func).method_name 0
        then
          let code =
            id_code x0 ^ " = " ^ func_code func ^ arg_code func arg ^ ";\n"
          in
          if is_file func then
            code ^ recv_name_code x0 func ^ "createNewFile();\n"
          else code
        else
          id_code x0 ^ " = " ^ recv_name_code x1 func ^ func_code func
          ^ arg_code func arg ^ ";\n"
    | Void (x, func, arg) ->
        if
          Str.string_match
            (".*\\.<init>" |> Str.regexp)
            (get_func func).method_name 0
        then func_code func ^ arg_code func arg ^ ";\n"
        else recv_name_code x func ^ func_code func ^ arg_code func arg ^ ";\n"
    | Seq (s1, s2) -> code s1 ^ code s2
    | Skip -> ""
    | Stmt -> "Stmt"
end
