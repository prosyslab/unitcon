module Json = Yojson.Safe
module JsonUtil = Yojson.Safe.Util

let compare_string = String.compare

let compare_bool = Bool.compare

let compare_list = List.compare

type tc_completion = Complete | Need_Fuzzer | Need_Loop | Incomplete

type method_name = string [@@deriving compare]

type class_name = string [@@deriving compare]

type file_name = string [@@deriving compare]

type modifier = Public | Private | Protected | Default [@@deriving compare]

(* class_type is only allowed to be public or default *)
type class_type =
  | Public
  | Private
  | Default (* including protected *)
  | Public_Static
  | Public_Abstract
  | Public_Static_Abstract
  | Private_Static
  | Private_Abstract
  | Private_Static_Abstract
  | Default_Static
  | Default_Abstract
  | Default_Static_Abstract
  | Public_Interface
  | Default_Interface
[@@deriving compare]

type typ =
  | Int
  | Long
  | Short
  | Byte
  | Float
  | Double
  | Bool
  | Char
  | String
  | Object of class_name
  | Array of typ
  | NonType
[@@deriving compare]

type id = string (*e.g. i *) [@@deriving compare]

type variable = This of typ | Var of typ * id [@@deriving compare]

type import = string (* package.class *) [@@deriving compare]

type params = variable list [@@deriving compare]

type symbol = string (*e.g. v1 *) [@@deriving compare]

let rec get_array_typ typ =
  match typ with Array t -> get_array_typ t | _ -> typ

let rec get_array_dim typ =
  match typ with Array t -> get_array_dim t + 1 | _ -> 1

let get_array_class_name = function
  | Array typ -> (
      match get_array_typ typ with
      | Int -> "IntArray" ^ (get_array_dim typ |> string_of_int)
      | Long -> "LongArray" ^ (get_array_dim typ |> string_of_int)
      | Short -> "ShortArray" ^ (get_array_dim typ |> string_of_int)
      | Byte -> "ByteArray" ^ (get_array_dim typ |> string_of_int)
      | Float -> "FloatArray" ^ (get_array_dim typ |> string_of_int)
      | Double -> "DoubleArray" ^ (get_array_dim typ |> string_of_int)
      | Bool -> "BoolArray" ^ (get_array_dim typ |> string_of_int)
      | Char -> "CharArray" ^ (get_array_dim typ |> string_of_int)
      | String -> "StringArray" ^ (get_array_dim typ |> string_of_int)
      | Object class_name ->
          "Object" ^ class_name ^ "Array" ^ (get_array_dim typ |> string_of_int)
      | _ -> "")
  | _ -> ""

let get_class_name = function
  | Object n -> n
  | Array typ -> (
      match get_array_typ typ with
      | Int -> "IntArray"
      | Long -> "LongArray"
      | Short -> "ShortArray"
      | Byte -> "ByteArray"
      | Float -> "FloatArray"
      | Double -> "DoubleArray"
      | Bool -> "BoolArray"
      | Char -> "CharArray"
      | String -> "StringArray"
      | Object _ -> "ObjectArray"
      | _ -> "")
  | NonType -> ""
  | _ -> failwith "get_class_name: not supported"

let get_consume_func t =
  (match t with
  | Int -> "Int()"
  | Long -> "Long()"
  | Short -> "Short()"
  | Byte -> "Byte()"
  | Float -> "Float()"
  | Double -> "Double()"
  | Bool -> "Boolean()"
  | Char -> "Char()"
  | String -> "RemainingAsString()"
  | _ -> failwith "get_consume_func: not supported")
  |> String.cat "data.consume"

let modifier_of_json json : modifier =
  JsonUtil.to_string json |> function
  | "Protected" -> Protected
  | "Public" -> Public
  | "Private" -> Private
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

module ReturnType = struct
  module M = Map.Make (struct
    type t = class_name [@@deriving compare]
  end)

  type t = method_name list M.t
end

module MethodType = struct
  module M = Map.Make (struct
    type t = class_name [@@deriving compare]
  end)

  type t = method_name list M.t
end

module Relation = struct
  module M = Map.Make (struct
    type t = symbol [@@deriving compare]
  end)

  type t = symbol M.t
end

module Value = struct
  type const =
    | Int of int
    | Long of int
    | Short of int
    | Byte of int
    | Float of float
    | Double of float
    | Bool of bool
    | Char of char
    | String of string
    | PlusInf
    | MinusInf
    | Null
    | NonValue (* Determining whether to use the default const *)

  type op =
    | Eq of const
    | Neq of const
    | Le of const
    | Lt of const
    | Ge of const
    | Gt of const
    | Between of const * const
    | Outside of const * const

  module M = Map.Make (struct
    type t = symbol [@@deriving compare]
  end)

  type v = { from_error : bool; value : op }

  type t = v M.t

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

  type var = rh M.t (* symbol -> variable *)

  type mem = rh M.t M.t

  type t = var * mem
end

module Field = struct
  type t = { used_in_error : bool; name : string } [@@deriving compare]
end

module FieldSet = Set.Make (Field)

module UseFieldMap = struct
  module M = Map.Make (struct
    type t = Condition.rh [@@deriving compare]
  end)

  type t = FieldSet.t M.t
end

type summary = {
  relation : Relation.t;
  value : Value.t;
  use_field : UseFieldMap.t;
  precond : Condition.t;
  postcond : Condition.t;
  args : symbol list;
}

let empty_summary =
  {
    relation = Relation.M.empty;
    value = Value.M.empty;
    use_field = UseFieldMap.M.empty;
    precond = (Condition.M.empty, Condition.M.empty);
    postcond = (Condition.M.empty, Condition.M.empty);
    args = [];
  }

module SummaryMap = struct
  module M = Map.Make (struct
    type t = method_name [@@deriving compare]
  end)

  (* list of summaries * list of fields with memory effects *)
  type t = (summary list * string list) M.t
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

module SetterMap = struct
  module M = Map.Make (struct
    type t = class_name [@@deriving compare]
  end)

  type setter = method_name * FieldSet.t

  type t = setter list M.t
end

module InstanceInfo = struct
  module M = Map.Make (struct
    type t = string [@@deriving compare]
  end)

  type const = string

  (* enum name -> enum const list || class name -> pre-created instance list*)
  type t = const list M.t
end

module PrimitiveInfo = struct
  module TypeMap = Map.Make (struct
    type t = typ [@@deriving compare]
  end)

  module ClassMap = Map.Make (struct
    (* default class name: "" *)
    type t = class_name [@@deriving compare]
  end)

  type const = string

  (* type -> class name -> const list*)
  type t = const list ClassMap.t TypeMap.t
end

module AST = struct
  type var = {
    import : import;
        (* if var is primitive type then import is class of method *)
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

  type arg = Param of var list | Arg of var list

  type func = F of f | Func

  type id = Variable of var | ClassName of string | Id

  type primitive = Z of int | R of float | B of bool | C of char | S of string

  type exp =
    | Primitive of primitive
    | GlobalConstant of string
    | Null
    | WithFuzz
    | WithLoop
    | Exp

  type t =
    | Const of (id * exp)
    | Assign of (id * id * func * arg)
    | Void of (id * func * arg)
    | Seq of (t * t)
    | Skip
    | Stmt

  module LoopIdMap = struct
    module M = Map.Make (struct
      type t = id

      let compare = compare
    end)

    type t = exp list M.t
  end

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

  let is_stmt = function Stmt -> true | _ -> false

  and is_arg = function Arg _ -> true | _ -> false

  and is_func = function Func -> true | _ -> false

  and is_id = function Id -> true | _ -> false

  and is_exp = function Exp -> true | _ -> false

  and is_fuzz = function WithFuzz -> true | _ -> false

  and is_loop = function WithLoop -> true | _ -> false

  let rec ground = function
    | Const (x, exp) -> not (is_id x || is_exp exp)
    | Assign (x0, x1, func, arg) ->
        not (is_id x0 || is_id x1 || is_func func || is_arg arg)
    | Void (x, func, arg) -> not (is_id x || is_func func || is_arg arg)
    | Seq (s1, s2) -> ground s1 && ground s2
    | Skip -> true
    | Stmt -> false

  let rec assign_ground = function
    | Const (x, exp) -> not (is_id x || is_exp exp)
    | Assign (x0, x1, func, arg) ->
        not (is_id x0 || is_id x1 || is_func func || is_arg arg)
    | Void (x, func, arg) -> not (is_id x || is_func func || is_arg arg)
    | Seq (s1, s2) -> assign_ground s1 && assign_ground s2
    | Skip -> true
    | Stmt -> true

  let rec with_withfuzz = function
    | Const (_, exp) -> is_fuzz exp
    | Assign _ -> false
    | Void _ -> false
    | Seq (s1, s2) -> with_withfuzz s1 || with_withfuzz s2
    | Skip -> false
    | Stmt -> false

  let rec with_withloop = function
    | Const (_, exp) -> is_loop exp
    | Assign _ -> false
    | Void _ -> false
    | Seq (s1, s2) -> with_withloop s1 || with_withloop s2
    | Skip -> false
    | Stmt -> false

  let modify_import import v =
    { import; variable = v.variable; field = v.field; summary = v.summary }

  let rec last_code p = match p with Seq (_, s) -> last_code s | _ -> p

  let rec modify_last_assign p =
    match p with
    | Seq (s1, s2) -> Seq (s1, modify_last_assign s2)
    | Assign _ when ground p -> Skip
    | _ -> p

  let rec count_nt = function
    | Const (x, exp) -> count_id x + count_exp exp
    | Assign (x0, x1, func, _) -> count_id x0 + count_id x1 + count_func func
    | Void (x, func, _) -> count_id x + count_func func
    | Seq (s1, s2) -> count_nt s1 + count_nt s2
    | Skip -> 0
    | Stmt -> 0

  and count_func = function Func -> 1 | _ -> 0

  and count_id = function Id -> 1 | _ -> 0

  and count_exp = function Exp -> 1 | _ -> 0

  let rec count_t = function
    | Const (x, exp) -> count_tid x + count_texp exp
    | Assign (x0, x1, f, _) -> count_tid x0 + count_tid x1 + count_tf f
    | Void (x, f, _) -> count_tid x + count_tf f
    | Seq (s1, s2) -> count_t s1 + count_t s2
    | Skip -> 0
    | Stmt -> 0

  and count_tf = function Func -> 0 | _ -> 1

  and count_tid = function Id -> 0 | _ -> 1

  and count_texp = function Exp -> 0 | _ -> 1

  let rec count_params = function
    | Assign (_, _, _, p) -> count_param p
    | _ -> 0

  and count_param = function Arg a -> List.length a | Param p -> List.length p

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

  (* 7. x.F(ID) *)
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

  let const_rule2_2 s f arg =
    match s with
    | Const (x, _) ->
        Assign
          ( x,
            ClassName ((get_func f).method_name |> Utils.get_class_name),
            f,
            arg )
    | _ -> s

  let const_rule3 s = match s with Const (x, _) -> Const (x, Null) | _ -> s

  let const_rule_loop s =
    match s with Const (x, _) -> Const (x, WithLoop) | _ -> s

  (* 2 *)
  let fcall_in_assign_rule s field f arg =
    match s with
    | Assign (x0, x1, _, _) ->
        let new_x0 =
          Variable
            {
              import = (get_v x0).import;
              variable = (get_v x0).variable;
              field;
              summary = (get_v x0).summary;
            }
        in
        Assign (new_x0, x1, f, arg)
    | _ -> s

  let mk_mock_statement s =
    match s with
    | Assign (x0, _, _, _) ->
        let class_name = get_vinfo x0 |> fst |> get_class_name in
        let x1 = ClassName "Mockito" in
        let f =
          F
            {
              typ = "";
              method_name = "mock";
              import = "";
              summary = empty_summary;
            }
        in
        let arg =
          Param
            [
              {
                import = "";
                variable = (Var (NonType, class_name), None);
                field = FieldSet.empty;
                summary = empty_summary;
              };
            ]
        in
        Assign (x0, x1, f, arg)
    | _ -> s

  (* 3 *)
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
              field =
                (match func with
                | Func -> FieldSet.empty
                | F f ->
                    get_field_from_ufmap "this" (fst f.summary.precond)
                      f.summary.use_field);
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
              field =
                (match func with
                | Func -> FieldSet.empty
                | F f ->
                    get_field_from_ufmap "this" (fst f.summary.precond)
                      f.summary.use_field);
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

  let get_rh_name ?(is_var = false) rh =
    if is_var then match rh with Condition.RH_Var v -> v | _ -> ""
    else match rh with Condition.RH_Symbol s -> s | _ -> ""

  let get_next_symbol symbol memory =
    match Condition.M.find_opt symbol memory with
    | Some sym -> (
        match Condition.M.find_opt Condition.RH_Any sym with
        | Some s -> s
        | None -> symbol)
    | None -> symbol

  let get_id_symbol vars id =
    Condition.M.fold
      (fun symbol symbol_id find ->
        match symbol_id with
        | Condition.RH_Var v when v = id -> symbol
        | _ -> find)
      vars Condition.RH_Any

  let rec get_tail_symbol field_name symbol memory =
    match Condition.M.find_opt symbol memory with
    | Some sym -> (
        match Condition.M.find_opt (Condition.RH_Var field_name) sym with
        | Some s -> get_tail_symbol field_name s memory
        | None -> (
            match Condition.M.find_opt Condition.RH_Any sym with
            | Some any_sym -> get_tail_symbol field_name any_sym memory
            | None -> symbol))
    | None -> symbol

  let get_index_value (v : Value.v) : Field.t =
    match v.value with
    | Value.Eq (Int i) ->
        { used_in_error = v.from_error; name = string_of_int i }
    | Value.Ge (Int i) ->
        { used_in_error = v.from_error; name = string_of_int i }
    | Value.Gt (Int i) ->
        { used_in_error = v.from_error; name = string_of_int (i + 1) }
    | _ -> { used_in_error = false; name = "" }

  let org_symbol id { precond = pre_var, pre_mem; _ } =
    let id_symbol = get_id_symbol pre_var id |> get_rh_name in
    Condition.M.fold
      (fun symbol symbol_trace find_variable ->
        let symbol = get_rh_name symbol in
        if symbol = id_symbol then
          Condition.M.fold
            (fun _ tail trace_find_var ->
              match tail with Condition.RH_Symbol s -> s | _ -> trace_find_var)
            symbol_trace find_variable
        else find_variable)
      pre_mem ""

  let get_array_index array summary =
    let _, memory = summary.precond in
    let array_symbol = org_symbol array summary in
    let values = summary.value in
    let find_value s =
      Value.M.fold
        (fun symbol value find_value ->
          if symbol = s then value else find_value)
        values
        { from_error = false; value = Value.Eq NonValue }
    in
    match Condition.M.find_opt (Condition.RH_Symbol array_symbol) memory with
    | Some x ->
        Condition.M.fold
          (fun sym v ((idx, idx_value), (elem, elem_value)) ->
            match sym with
            | Condition.RH_Index s when idx = "" ->
                ( (s, find_value s),
                  ( get_rh_name v,
                    find_value (get_tail_symbol "" v memory |> get_rh_name) ) )
            | _ -> ((idx, idx_value), (elem, elem_value)))
          x
          ( ("", { from_error = false; value = Value.Ge (Int 0) }),
            ("", { from_error = false; value = Value.Eq NonValue }) )
    | None ->
        ( ("", { from_error = false; value = Value.Ge (Int 0) }),
          ("", { from_error = false; value = Value.Eq NonValue }) )

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
      (Condition.RH_Symbol (fst array |> fst))
      (Condition.RH_Var "index") (fst org_summary.precond)
    |> Condition.M.add
         (Condition.RH_Symbol (snd array |> fst))
         (Condition.RH_Var "elem")

  let array_current_mem org_summary array =
    Condition.M.add (Condition.RH_Symbol "v5")
      (Condition.M.add (Condition.RH_Var "index")
         (Condition.RH_Symbol (fst array |> fst))
         Condition.M.empty)
      (snd org_summary.precond)
    |> Condition.M.add (Condition.RH_Var "elem")
         (Condition.M.add Condition.RH_Any
            (Condition.RH_Symbol (snd array |> fst))
            Condition.M.empty)

  let next_summary_in_void org_summary new_mem =
    {
      relation = org_summary.relation;
      value = org_summary.value;
      use_field = org_summary.use_field;
      precond = (fst org_summary.precond, new_mem);
      postcond = (fst org_summary.postcond, new_mem);
      args = org_summary.args;
    }

  let current_summary_in_assign org_summary new_var new_mem =
    {
      relation = org_summary.relation;
      value = org_summary.value;
      use_field = org_summary.use_field;
      precond = (new_var, new_mem);
      postcond = (new_var, new_mem);
      args = org_summary.args;
    }

  let new_seq assign void = Seq (Seq (assign, Stmt), void)

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

  (* 5 *)
  let void_rule1 s = match s with Seq (s1, _) -> Seq (s1, Skip) | _ -> s

  let void_rule2_array x0 x1 f arg =
    let arr_id = get_vinfo x0 |> snd in
    let new_idx, new_elem = get_array_index arr_id (get_v x0).summary in
    (* remove setter of duplicate index *)
    if FieldSet.mem (snd new_idx |> get_index_value) (get_v x0).field then []
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
      [
        new_seq
          (Assign (new_id (new_field x0 nfield) new_next_summary, x1, f, arg))
          (Void (new_id x0 new_current_summary, Func, Arg []));
      ]

  (* let void_rule2_normal x0 x1 f arg =
     let remove = FieldSet.remove in
     FieldSet.fold
       (fun field lst ->
         new_seq
           (Assign (new_field x0 (remove field (x0 |> get_v).field), x1, f, arg))
           (Void (new_field x0 (FieldSet.singleton field), Func, Arg []))
         :: lst)
       (x0 |> get_v).field [] *)

  let void_rule2_normal x0 x1 f arg =
    [ new_seq (Assign (x0, x1, f, arg)) (Void (x0, Func, Arg [])) ]

  let void_rule2 s =
    match s with
    | Seq (s1, _) -> (
        match s1 with
        | Assign (x0, x1, f, arg) ->
            if is_array_init f then void_rule2_array x0 x1 f arg
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
              field =
                (match func with
                | Func -> FieldSet.empty
                | F f ->
                    get_field_from_ufmap "this" (fst f.summary.precond)
                      f.summary.use_field);
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
              field =
                (match func with
                | Func -> FieldSet.empty
                | F f ->
                    get_field_from_ufmap "this" (fst f.summary.precond)
                      f.summary.use_field);
              summary =
                (match func with Func -> empty_summary | F f -> f.summary);
            }
        in
        Seq (Seq (Assign (x, Id, Func, Arg []), Stmt), Void (x, func, arg))
    | _ -> s

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
    | WithFuzz ->
        if !Cmdline.with_fuzz then
          match get_vinfo x |> fst with
          | Int | Long | Short | Byte | Char | Float | Double | Bool | String ->
              get_consume_func (get_vinfo x |> fst)
          | _ -> "Exp"
        else "Exp"
    | WithLoop ->
        if !Cmdline.with_loop then
          let v_type, v_id = loop_id_lval_code x in
          match v_type with
          | Int | Long | Short | Byte | Char | Float | Double | Bool | String ->
              v_id ^ "_comb[" ^ v_id ^ "_index]"
          | _ -> "Exp"
        else "Exp"
    | Exp -> "Exp"

  let rec code = function
    | Const (x, exp) -> id_code x ^ " = " ^ exp_code exp x ^ ";\n"
    | Assign (x0, x1, func, arg) ->
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
    | Void (x, func, arg) ->
        if Utils.is_init_method (get_func func).method_name then
          func_code func ^ arg_code func arg ^ ";\n"
        else recv_name_code x func ^ func_code func ^ arg_code func arg ^ ";\n"
    | Seq (s1, s2) -> code s1 ^ code s2
    | Skip -> ""
    | Stmt -> "Stmt"

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
    lval ^ " = " ^ "{"
    ^ Regexp.rm_first_rest (rval loop_id exp_list)
    ^ "};\n" ^ lval ^ "_comb = UnitconCombinator.combine"
    ^ comb_func_name (fst v)
    ^ "(" ^ snd v ^ ");\n"
end
