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

let of_json json =
  JsonUtil.to_assoc json
  |> List.fold_left
       (fun g (caller, callees) ->
         JsonUtil.to_list callees
         |> List.map JsonUtil.to_string
         |> List.fold_left (fun g callee -> G.add_edge g caller callee) g)
       G.empty

module Graphviz = Graph.Graphviz.Dot (G)
include G
