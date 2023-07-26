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
  type arg = Param of params | Defined of string list | Arg

  type func = F of { method_name : method_name; args : arg } | Func

  type id = Variable of variable | ClassName of string | Id

  type primitive = Z of int | R of float | B of bool | C of char

  type exp = Primitive of primitive | GlobalConstant of string | Null | Exp

  type t =
    | Const of (id * exp)
    | Assign of (id * id * func * arg)
    | Void of (id * func * arg)
    | Seq of (t * t)
    | Skip
    | Stmt

  let is_stmt = function Stmt -> true | _ -> false

  and is_arg = function Arg -> true | _ -> false

  and is_func = function Func -> true | _ -> false

  and is_id = function Id -> true | _ -> false

  and is_exp = function Exp -> true | _ -> false

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
     Return Code
   * ************************************** *)

  let arg_code =
    let cc code x = code ^ ", " ^ x in
    function
    | Param p ->
        "("
        ^ (List.fold_left
             (fun pc (_, p) -> match p with Var (_, id) -> cc pc id | _ -> pc)
             "" p
          |> Regexp.rm_first_rest)
        ^ ")"
    | Defined c ->
        "("
        ^ (List.fold_left (fun pc c -> cc pc c) "" c |> Regexp.rm_first_rest)
        ^ ")"
    | Arg -> failwith "Error: still need unrolling arg"

  let func_code = function
    | F f -> f.method_name |> Str.global_replace Regexp.dollar "."
    | _ -> failwith "Error: still need unrolling func"

  let is_var = function Variable _ -> true | _ -> false

  and is_string = function ClassName c when c = "String" -> true | _ -> false

  and is_cn = function ClassName c when c <> "String" -> true | _ -> false

  let var_code v =
    let v =
      match v with
      | Var (typ, id) -> (typ, id)
      | This _ -> failwith "Error: This is not var"
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
    | _ -> failwith "not supported variable"

  let recv_name_code = function
    | Variable v -> (
        match v with
        | Var (_, id) -> id
        | This _ -> failwith "Error: This is not var")
    | ClassName c -> c
    | _ -> failwith "Error: still need unrolling id"

  let id_code = function
    | Variable v -> var_code v
    | ClassName c -> c
    | Id -> failwith "Error: still need unrolling id"

  let primitive_code = function
    | Z z -> (z |> string_of_int) ^ ";\n"
    | R r -> (r |> string_of_float) ^ ";\n"
    | B b -> (b |> string_of_bool) ^ ";\n"
    | C c -> "\'" ^ String.make 1 c ^ "\';\n"

  let exp_code = function
    | Primitive p -> primitive_code p
    | GlobalConstant g -> g
    | Null -> "null;\n"
    | Exp -> failwith "Error: still need unrolling exp"

  let rec s_code = function
    | Const (x, exp) -> id_code x ^ " = " ^ exp_code exp
    | Assign (x0, x1, func, arg) ->
        if is_cn x1 then
          id_code x0 ^ " = " ^ "new " ^ func_code func ^ arg_code arg ^ ";\n"
        else if is_var x1 then
          id_code x0 ^ " = " ^ recv_name_code x1 ^ "." ^ func_code func
          ^ arg_code arg ^ ";\n"
        else if is_string x1 then
          id_code x0 ^ " = " ^ "\"" ^ func_code func ^ "\";\n"
        else failwith "Error: not supported id type"
    | Void (x, func, arg) ->
        recv_name_code x ^ "." ^ func_code func ^ arg_code arg ^ ";\n"
    | Seq (s1, s2) -> s_code s1 ^ s_code s2
    | Skip -> ""
    | Stmt -> failwith "Error: still need unrolling stmt"

  let code = function
    | Seq (s1, s2) -> s_code s1 ^ s_code s2
    | _ -> "Error: this s can not be start"
end
