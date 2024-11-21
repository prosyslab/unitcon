module Json = Yojson.Safe
module JsonUtil = Yojson.Safe.Util
module MethodInfo = Language.MethodInfo
module ExtraCalleeSet = Set.Make (String)

module Node = struct
  include String

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

let split_name name =
  if String.contains name ':' then Str.split Regexp.colon name |> List.hd
  else name

let get_caller_method_name assoc =
  JsonUtil.member "method" assoc
  |> JsonUtil.to_list |> List.hd |> JsonUtil.to_string |> split_name

let get_callee_method_name assoc =
  JsonUtil.member "callee" assoc
  |> JsonUtil.to_list
  |> List.fold_left (fun l m -> (JsonUtil.to_string m |> split_name) :: l) []
  |> List.rev

let add_missing_callee info cg =
  match JsonUtil.member "methods" info with
  | `Null -> cg
  | methods ->
      List.fold_left
        (fun cg caller_name ->
          if Utils.is_lambda_method caller_name then cg
          else
            let m_info = JsonUtil.member caller_name methods in
            let callees = JsonUtil.member "callee" m_info |> JsonUtil.to_list in
            List.fold_left
              (fun g callee ->
                let callee_name = JsonUtil.to_string callee in
                if Utils.is_lambda_method callee_name then g
                else G.add_edge g callee_name caller_name)
              cg callees)
        cg (JsonUtil.keys methods)

let of_json json =
  let json = JsonUtil.to_list json in
  List.fold_left
    (fun g element ->
      let caller = get_caller_method_name element in
      get_callee_method_name element
      |> List.fold_left (fun g callee -> G.add_edge g callee caller) g)
    G.empty json

let of_extra_json cg json =
  List.fold_left
    (fun g class_name ->
      let info = JsonUtil.member class_name json in
      add_missing_callee info g)
    cg (JsonUtil.keys json)

module Graphviz = Graph.Graphviz.Dot (G)
include G
