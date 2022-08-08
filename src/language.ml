module Json = Yojson.Safe
module JsonUtil = Yojson.Safe.Util

type var = string

type modifier = Public | Private | Protected [@@deriving compare]

let modifier_of_json json =
  JsonUtil.to_string json |> function
  | "public" -> Public
  | "private" -> Private
  | "protected" -> Protected
  | s -> failwith ("Unknown modifier " ^ s)

let param_of_json json = List.map JsonUtil.to_string json

type args = var list

type exp =
  | Command of string * args
  | String of string
  | Int of int
  | New of string * args

type t = Assignment of var * exp | Statement of var * exp | Sequence of t * t

module Method = struct
  let compare_string = String.compare

  let compare_list = List.compare

  type t = { name : string; modifier : modifier; param : string list }
  [@@deriving compare]

  let hash = Hashtbl.hash

  let equal = ( = )

  let from_json json =
    let name = Yojson.Safe.Util.member "name" json |> JsonUtil.to_string in
    let modifier =
      Yojson.Safe.Util.member "modifier" json |> modifier_of_json
    in
    let param =
      Yojson.Safe.Util.member "param" json
      |> Yojson.Safe.Util.to_list |> param_of_json
    in
    { name; modifier; param }
end

module MethodMap = struct
  module M = Map.Make (struct
    type t = string

    let compare = compare
  end)

  type t = Method.t M.t

  let of_json json =
    Yojson.Safe.Util.to_list json
    |> List.fold_left
         (fun mmap item ->
           let m = Method.from_json item in
           M.add m.Method.name m mmap)
         M.empty
end
