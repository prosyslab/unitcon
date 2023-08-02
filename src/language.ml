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
      | _ -> failwith "get_class_name: not supported type")
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

module SetterMap = struct
  module M = Map.Make (struct
    type t = class_name [@@deriving compare]
  end)

  type setter = method_name * id list

  type t = setter list M.t
end

module FieldMap = struct
  module M = Map.Make (struct
    type t = string [@@deriving compare]
  end)

  type t = Value.op M.t
end

module AST = struct
  type var = {
    import : import;
    variable : variable * int option;
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

  type exp = Primitive of primitive | GlobalConstant of string | Null | Exp

  type t =
    | Const of (id * exp)
    | Assign of (id * id * func * arg)
    | Void of (id * func * arg)
    | Seq of (t * t)
    | Skip
    | Stmt

  (* id -> var*)
  let rec get_v id =
    match id with Variable v -> v | _ -> failwith "get_v: not supported"

  (* id -> typ * string *)
  and get_vinfo v =
    match (get_v v).variable with
    | Var (typ, id), _ -> (typ, id)
    | This typ, _ -> (typ, "this")

  let get_func func =
    match func with F f -> f | _ -> failwith "get_func: not supported"

  let get_arg arg =
    match arg with Arg a -> a | _ -> failwith "get_arg: not supported"

  let get_param arg =
    match arg with Param p -> p | _ -> failwith "get_param: not supported"

  let rec ground = function
    | Const (x, exp) -> (is_id x || is_exp exp) |> not
    | Assign (x0, x1, func, arg) ->
        (is_id x0 || is_id x1 || is_func func || is_arg arg) |> not
    | Void (x, func, arg) -> (is_id x || is_func func || is_arg arg) |> not
    | Seq (s1, s2) -> ground s1 && ground s2
    | Skip -> true
    | Stmt -> false

  and is_stmt = function Stmt -> true | _ -> false

  and is_arg = function Arg _ -> true | _ -> false

  and is_func = function Func -> true | _ -> false

  and is_id = function Id -> true | _ -> false

  and is_exp = function Exp -> true | _ -> false

  let rec count_nt = function
    | Const (x, exp) -> count_id x + count_exp exp
    | Assign (x0, x1, func, arg) ->
        count_id x0 + count_id x1 + count_func func + count_arg arg
    | Void (x, func, arg) -> count_id x + count_func func + count_arg arg
    | Seq (s1, s2) -> count_nt s1 + count_nt s2
    | Skip -> 0
    | Stmt -> 1

  and count_arg = function
    | Arg a -> if a = [] then 1 else List.length a
    | _ -> 0

  and count_func = function Func -> 1 | _ -> 0

  and count_id = function Id -> 1 | _ -> 0

  and count_exp = function Exp -> 1 | _ -> 0

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
  let fcall_in_assign_rule s f arg =
    match s with Assign (x0, x1, _, _) -> Assign (x0, x1, f, arg) | _ -> s

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

  (* 5 *)
  let void_rule1 s = match s with Seq (s1, _) -> s1 | _ -> s

  let void_rule2 s =
    match s with
    | Seq (s1, _) -> (
        match s1 with
        | Assign (x0, _, _, _) -> Seq (Seq (s1, Stmt), Void (x0, Func, Arg []))
        | _ -> s)
    | _ -> s

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
              summary =
                (match func with Func -> empty_summary | F f -> f.summary);
            }
        in
        Seq (Seq (Assign (x, Id, Func, Arg []), Stmt), Void (x, func, arg))
    | _ -> s

  (* ************************************** *
     Return Code
   * ************************************** *)

  let is_array f =
    let fname = (get_func f).method_name in
    if Str.string_match (".*Array\\.<init>" |> Str.regexp) fname 0 then true
    else false

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
        if is_array f then "[" ^ param ^ "]" else "(" ^ param ^ ")"
    | Arg _ -> failwith "Error: still need unrolling arg"

  let func_code func =
    match func with
    | F f ->
        if is_array func then
          Str.split Regexp.dot f.method_name
          |> List.hd
          |> Regexp.first_rm (Str.regexp "Array")
          |> String.cat "new "
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
    | _ -> failwith "Error: still need unrolling func"

  let is_var = function Variable _ -> true | _ -> false

  and is_cn = function ClassName c -> true | _ -> false

  let var_code v =
    let v =
      match v.variable with
      | Var (typ, id), Some idx -> (typ, id ^ (idx |> string_of_int))
      | _, None -> failwith "Error: idx cannot be none"
      | This typ, _ -> failwith "Error: This is not var"
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
        | _ -> failwith "not supported variable")
    | _ -> failwith "not supported variable"

  let recv_name_code = function
    | Variable v -> (
        match v.variable with
        | Var (_, id), Some idx -> id ^ (idx |> string_of_int) ^ "."
        | _ -> "")
    | ClassName c -> (c |> Str.global_replace Regexp.dollar ".") ^ "."
    | _ -> failwith "Error: still need unrolling id"

  let id_code = function
    | Variable v -> var_code v
    | ClassName c -> c
    | Id -> failwith "Error: still need unrolling id"

  let primitive_code p x =
    match p with
    | Z z -> (
        match get_vinfo x |> fst with
        | Bool ->
            if z = 0 then (false |> string_of_bool) ^ ";\n"
            else (true |> string_of_bool) ^ ";\n"
        | _ -> (z |> string_of_int) ^ ";\n")
    | R r -> (r |> string_of_float) ^ ";\n"
    | B b -> (b |> string_of_bool) ^ ";\n"
    | C c -> "\'" ^ String.make 1 c ^ "\';\n"
    | S s -> "\"" ^ s ^ "\";\n"

  let exp_code exp x =
    match exp with
    | Primitive p -> primitive_code p x
    | GlobalConstant g -> g ^ ";\n"
    | Null -> "null;\n"
    | Exp -> failwith "Error: still need unrolling exp"

  let rec code = function
    | Const (x, exp) -> id_code x ^ " = " ^ exp_code exp x
    | Assign (x0, x1, func, arg) ->
        if is_var x1 then
          id_code x0 ^ " = " ^ recv_name_code x1 ^ func_code func
          ^ arg_code func arg ^ ";\n"
        else if
          Str.string_match
            (".*\\.<init>" |> Str.regexp)
            (get_func func).method_name 0
        then id_code x0 ^ " = " ^ func_code func ^ arg_code func arg ^ ";\n"
        else
          id_code x0 ^ " = " ^ recv_name_code x1 ^ func_code func
          ^ arg_code func arg ^ ";\n"
    | Void (x, func, arg) ->
        if
          Str.string_match
            (".*\\.<init>" |> Str.regexp)
            (get_func func).method_name 0
        then func_code func ^ arg_code func arg ^ ";\n"
        else recv_name_code x ^ func_code func ^ arg_code func arg ^ ";\n"
    | Seq (s1, s2) -> code s1 ^ code s2
    | Skip -> ""
    | Stmt -> failwith "Error: still need unrolling stmt"
end
