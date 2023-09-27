module Json = Yojson.Safe
module JsonUtil = Yojson.Safe.Util
module ClassInfo = Language.ClassInfo

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
    |> List.fold_left (fun lst super -> (super |> JsonUtil.to_string) :: lst) []
    |> List.rev
  in
  class_name

let transitive_closure vertex graph =
  let get_children v = try G.succ graph v with Invalid_argument _ -> [] in
  let rec iter children g =
    match children with
    | hd :: tl ->
        if G.mem_edge g vertex hd then iter tl g
        else G.add_edge g vertex hd |> iter tl |> iter (get_children hd)
    | [] -> g
  in
  iter
    (get_children vertex
    |> List.fold_left (fun lst v -> get_children v :: lst) []
    |> List.rev |> List.flatten)
    graph

let missing_inheritance vertex graph =
  let missing_class_name =
    Str.global_replace (Str.regexp "\\..*\\$") "." vertex
  in
  try
    let missing = G.succ graph missing_class_name in
    List.fold_left
      (fun new_graph name -> G.add_edge new_graph vertex name)
      graph missing
  with Invalid_argument _ -> graph

let from_inheritance_json json =
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
  let graph = G.fold_vertex (fun v g -> transitive_closure v g) graph graph in
  G.fold_vertex (fun v g -> missing_inheritance v g) graph graph

module Graphviz = Graph.Graphviz.Dot (G)
include G

let parse_type type_list =
  let is_static =
    List.fold_left
      (fun result typ -> if typ = "static" then true else result)
      false type_list
  in
  let is_abstract =
    List.fold_left
      (fun result typ -> if typ = "abstract" then true else result)
      false type_list
  in
  let is_private =
    List.fold_left
      (fun result typ -> if typ = "private" then true else result)
      false type_list
  in
  let is_interface =
    List.fold_left
      (fun result typ -> if typ = "interface" then true else result)
      false type_list
  in
  if is_private then Language.Private
  else if is_static && is_abstract then Language.Abstract_and_Static
  else if is_static then Language.Static
  else if is_abstract then Language.Abstract
  else if is_interface then Language.Interface
  else Language.Normal

let mapping_class_info assoc mmap =
  let class_name = JsonUtil.member "name" assoc |> JsonUtil.to_string in
  let typ =
    JsonUtil.member "type" assoc
    |> JsonUtil.to_list
    |> List.fold_left (fun lst x -> JsonUtil.to_string x :: lst) []
    |> List.rev |> parse_type
  in
  ClassInfo.M.add class_name ClassInfo.{ class_type = typ } mmap

let of_json json =
  let class_and_interface_info =
    JsonUtil.member "class_and_interface" json |> JsonUtil.to_list
  in
  let class_type_info =
    List.fold_left
      (fun mmap assoc -> mapping_class_info assoc mmap)
      ClassInfo.M.empty class_and_interface_info
  in
  let inheritance_info = from_inheritance_json json in
  (class_type_info, inheritance_info)
