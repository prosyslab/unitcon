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

let get_super_classes_name assoc =
  let class_name =
    JsonUtil.member "super" assoc
    |> JsonUtil.to_list
    |> List.map (fun super -> super |> JsonUtil.to_string)
  in
  class_name

let transitive_closure vertex graph =
  let get_children v = try G.succ graph v with Invalid_argument _ -> [] in
  let rec iter children g =
    match children with
    | hd :: tl ->
        List.fold_left
          (fun g child -> G.add_edge g vertex child)
          g (get_children hd)
        |> iter (get_children hd)
        |> iter tl
    | [] -> g
  in
  iter (get_children vertex) graph

let of_json json =
  let member =
    [ "extends_class"; "implements_interface"; "extends_interface" ]
  in
  let from_hierarchy assoc_name assoc graph =
    JsonUtil.member assoc_name assoc
    |> JsonUtil.to_list
    |> List.fold_left
         (fun g element ->
           let child = JsonUtil.member "child" element |> JsonUtil.to_string in
           get_super_classes_name element
           |> List.fold_left (fun g super -> G.add_edge g super child) g)
         graph
  in
  let graph =
    List.fold_left
      (fun g assoc_name -> from_hierarchy assoc_name json g)
      G.empty member
  in
  G.fold_vertex (fun v g -> transitive_closure v g) graph graph

module Graphviz = Graph.Graphviz.Dot (G)
include G
