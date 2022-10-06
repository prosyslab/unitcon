module Method = Language.Method
module Json = Yojson.Safe
module JsonUtil = Yojson.Safe.Util
module SummaryMap = Summary.SummaryMap

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
  let method_name =
    if String.contains method_name ' ' then
      method_name |> String.split_on_char ' ' |> List.tl |> List.hd
    else method_name
  in
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
  let procname_and_param =
    String.split_on_char ':' json |> List.hd |> String.split_on_char '('
  in
  let procname = procname_and_param |> List.hd |> String.split_on_char '.' in
  let procname =
    List.nth procname (List.length procname - 2)
    ^ "."
    ^ List.nth procname (List.length procname - 1)
  in
  let param =
    procname_and_param |> List.tl |> List.hd |> String.split_on_char '.'
  in
  let param = List.nth param (List.length param - 1) in
  procname ^ "(" ^ param
