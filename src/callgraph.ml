module Json = Yojson.Safe
module JsonUtil = Yojson.Safe.Util

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

let get_caller_method_name assoc =
  let split_name name =
    if String.contains name ' ' then
      name |> String.split_on_char ' ' |> List.tl |> List.hd
    else name
  in
  let method_name =
    JsonUtil.member "method" assoc
    |> JsonUtil.to_list |> List.hd |> JsonUtil.to_string |> split_name
  in
  method_name

let get_callee_method_name assoc =
  let split_name name =
    if String.contains name ' ' then
      name |> String.split_on_char ' ' |> List.tl |> List.hd
    else name
  in
  let method_name =
    JsonUtil.member "callee" assoc
    |> JsonUtil.to_list
    |> List.map (fun callee -> callee |> JsonUtil.to_string |> split_name)
  in
  method_name

let of_json json =
  JsonUtil.to_list json
  |> List.fold_left
       (fun g element ->
         let caller = get_caller_method_name element in
         get_callee_method_name element
         |> List.fold_left (fun g callee -> G.add_edge g callee caller) g)
       G.empty

module Graphviz = Graph.Graphviz.Dot (G)
include G
