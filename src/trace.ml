module Method = Language.Method
module Json = Yojson.Safe
module JsonUtil = Yojson.Safe.Util
module SummaryMap = Summary.SummaryMap
module FindMethodMap = Summary.FindMethodMap

module TraceMap = struct
  module M = Map.Make (struct
    type t = int

    let compare = compare
  end)

  (* file_name * [visited] *)
  type t = Summary.key M.t
end

let bug_trace assoc mmap =
  let file_name = JsonUtil.member "filename" assoc |> JsonUtil.to_string in
  let level = JsonUtil.member "level" assoc |> JsonUtil.to_int in
  let line = JsonUtil.member "line_number" assoc |> JsonUtil.to_int in
  if TraceMap.M.mem level mmap then
    let key = TraceMap.M.find level mmap in
    let file_name = key.Summary.filename in
    let line_list = key.Summary.visited in
    TraceMap.M.add level
      { Summary.filename = file_name; Summary.visited = line :: line_list }
      mmap
  else
    TraceMap.M.add level
      { Summary.filename = file_name; Summary.visited = [ line ] }
      mmap

let from_json json =
  let json =
    JsonUtil.to_list json |> List.hd
    |> JsonUtil.member "bug_trace"
    |> JsonUtil.to_list
  in
  List.fold_left (fun mmap x -> bug_trace x mmap) TraceMap.M.empty json

let target_method json =
  let json =
    JsonUtil.to_list json |> List.hd
    |> JsonUtil.member "procedure"
    |> JsonUtil.to_string
  in
  let method_sig = String.split_on_char ':' json |> List.hd in
  let method_and_param = String.split_on_char '(' method_sig in
  let class_and_method =
    method_and_param |> List.hd |> String.split_on_char '.' |> List.rev
  in
  let method_name = class_and_method |> List.hd in
  let class_name = class_and_method |> List.tl |> List.hd in
  let param =
    method_and_param |> List.tl |> List.hd |> String.split_on_char ')'
    |> List.hd
  in
  let param_list = param |> String.split_on_char ',' in
  (class_name, method_name, param_list)
