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
  type var = variable

  type args = Param of params | Constant of string list

  type func = { id : id option; method_name : method_name; args : args }

  type primitive =
    | Null
    | Z of int
    | R of float
    | B of bool
    | C of char
    | S of string

  type setter =
    | SETEmpty
    | Setter of (string * func * setter)
    | SETNT (* setter non-terminal *)

  type create =
    | Primitive of primitive
    | GV of string
    | NewCreate of (func * setter)
    | GetCreate of (var * func * setter)

  type stmt =
    | STEmpty
    | Stmt of (var * create)
    | MStmt of (stmt * stmt)
    | STNT (* stmt non-terminal *)

  type t = TestCase of (stmt * func)

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

  let get_id v =
    match v with
    | Var (_, id) -> id
    | This _ -> failwith "Error: This is not contain id"

  let params_code params =
    match params with
    | Param p ->
        let code =
          List.fold_left
            (fun p_code (_, p) ->
              match p with Var (_, id) -> p_code ^ ", " ^ id | _ -> p_code)
            "" p
          |> Regexp.global_rm_exp Regexp.start_bm2
        in
        "(" ^ code ^ ")"
    | Constant c ->
        let code =
          List.fold_left (fun p_code c -> p_code ^ ", " ^ c) "" c
          |> Regexp.global_rm_exp Regexp.start_bm2
        in
        "(" ^ code ^ ")"

  let primitive_code p =
    match p with
    | Null -> "null;\n"
    | Z z -> (z |> string_of_int) ^ ";\n"
    | R r -> (r |> string_of_float) ^ ";\n"
    | B b -> (b |> string_of_bool) ^ ";\n"
    | C c -> "\'" ^ String.make 1 c ^ "\';\n"
    | S s -> "\"" ^ s ^ "\";\n"

  let rec setter_code (s : setter) =
    match s with
    | SETEmpty -> ""
    | Setter (id, func, setter) ->
        (id ^ "."
        ^ (func.method_name |> Str.global_replace Regexp.dollar ".")
        ^ params_code func.args ^ ";\n")
        ^ setter_code setter
    | _ -> failwith "Error: still need unrolling"

  let create_code c =
    match c with
    | Primitive p -> primitive_code p
    | GV g -> g ^ ";"
    | NewCreate (func, s) ->
        "new "
        ^ (func.method_name |> Str.global_replace Regexp.dollar ".")
        ^ params_code func.args ^ ";\n" ^ setter_code s
    | GetCreate (var, func, s) ->
        (var |> get_id) ^ "."
        ^ (func.method_name |> Str.global_replace Regexp.dollar ".")
        ^ params_code func.args ^ ";\n" ^ setter_code s

  let x = ref 0

  let rec stmt_code (s : stmt) =
    match s with
    | STEmpty -> ""
    | Stmt (var, c) -> var_code var ^ " = " ^ create_code c
    | MStmt (s1, s2) -> stmt_code s1 ^ stmt_code s2
    | _ -> failwith "Error: still need unrolling"

  let error_func_code e =
    match e.id with
    | Some id -> id ^ "." ^ e.method_name ^ params_code e.args ^ ";\n"
    | None -> "new " ^ e.method_name ^ params_code e.args ^ ";\n"

  let testcase_code = function
    | TestCase (stmt, e) -> stmt_code stmt ^ error_func_code e

  let get_ee = function TestCase (_, e) -> e

  let get_stmt = function TestCase (stmt, _) -> stmt

  let modify_setnt (t_var : var) stmt = function
    | TestCase (old_stmt, _) ->
        let modify c =
          let rec modify_s s =
            match s with
            | SETNT -> stmt
            | Setter (id, f, s) -> Setter (id, f, modify_s s)
            | _ -> s
          in
          match c with NewCreate (f, s) -> NewCreate (f, modify_s s) | _ -> c
        in
        let rec find_create stmt =
          match stmt with
          | Stmt (var, c) when var = t_var -> Stmt (var, modify c)
          | MStmt (s1, s2) -> MStmt (find_create s1, find_create s2)
          | _ -> stmt
        in
        find_create old_stmt

  let modify_stnt stmt = function
    | TestCase (old_stmt, _) ->
        let rec check_stnt stmt =
          match stmt with
          | STNT -> true
          | MStmt (s1, s2) -> check_stnt s1 || check_stnt s2
          | _ -> false
        in
        let rec modify old =
          match old with
          | STNT -> stmt
          | MStmt (s1, s2) ->
              if check_stnt s2 then MStmt (s1, modify s2)
              else MStmt (modify s1, s2)
          | _ -> old
        in
        modify old_stmt

  let remove_nt = function
    | TestCase (old_stmt, e) ->
        let rec modify old =
          match old with
          | STNT -> STEmpty
          | MStmt (s1, s2) -> MStmt (modify s1, modify s2)
          | _ -> old
        in
        TestCase (modify old_stmt, e)
end

let empty_tc =
  AST.TestCase (STEmpty, { id = None; method_name = ""; args = Constant [] })
