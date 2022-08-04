open Language

let parse_node n = failwith "not implemented"

let parse_edge n = failwith "not implemented"

(* parse call_graph.json *)
let parse_json filename =
  let json = Yojson.Safe.from_file filename in
  match json with
  | `Assoc l ->
    List.fold_left
      (fun graph (fd, value) ->
        match fd with
        | "node" -> { graph with Callgraph.node = parse_node value }
        | "edge" -> { graph with edge = parse_edge value}
        | _ -> failwith "Invalid input" )
      Callgraph.empty l
  | _ -> failwith "Invalid input"