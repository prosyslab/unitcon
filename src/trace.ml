module Method = Language.Method
module Json = Yojson.Safe
module JsonUtil = Yojson.Safe.Util
module SummaryMap = Summary.SummaryMap
module FindMethodMap = Summary.FindMethodMap

module TraceMap = struct
  module M = Map.Make (struct
    type t = string

    let compare = compare
  end)

  (* file_name * [visited] *)
  type t = Summary.key M.t
end

let bug_trace assoc mmap =
  let file_name = JsonUtil.member "filename" assoc |> JsonUtil.to_string in
  let method_name = JsonUtil.member "description" assoc |> JsonUtil.to_string in
  let line = JsonUtil.member "line_number" assoc |> JsonUtil.to_int in
  if TraceMap.M.mem method_name mmap then
    let key = TraceMap.M.find method_name mmap in
    let file_name = key.Summary.filename in
    let line_list = key.Summary.visited in
    TraceMap.M.add method_name
      { Summary.filename = file_name; Summary.visited = line :: line_list }
      mmap
  else
    TraceMap.M.add method_name
      {
        Summary.filename = Summary.Filename file_name;
        Summary.visited = [ line ];
      }
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
  String.split_on_char ':' json |> List.hd
