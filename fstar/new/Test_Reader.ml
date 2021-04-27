open Test_Types

let parse_uint32 (json:Yojson.Safe.t): FStar_UInt32.t =
  match json with
  | `Int x -> (FStar_UInt32.uint_to_t (Z.of_int x))
  | _ -> failwith "parse_uint32: not an int"

let parse_optional_uint32 (json:Yojson.Safe.t): FStar_UInt32.t option =
  match json with
  | `Int x -> Some (FStar_UInt32.uint_to_t (Z.of_int x))
  | `Null -> None
  | _ -> failwith "parse_optional_uint32: not an int or null"

let parse_treemath_test (json:Yojson.Safe.t): treemath_test =
  match json with
  | `Assoc [("n_leaves", `Int n_leaves); ("n_nodes", `Int n_nodes); ("root", `List root); ("left", `List left); ("right", `List right); ("parent", `List parent); ("sibling", `List sibling)] ->
    ({
      n_leaves=FStar_UInt32.uint_to_t (Z.of_int n_leaves);
      n_nodes=FStar_UInt32.uint_to_t (Z.of_int n_nodes);
      root=List.map parse_uint32 root;
      left=List.map parse_optional_uint32 left;
      right=List.map parse_optional_uint32 right;
      parent=List.map parse_optional_uint32 parent;
      sibling=List.map parse_optional_uint32 sibling;
    })
  | _ -> failwith "parse_treemath_test: incorrect test vector format"

let get_filename (typ:test_type): string =
  match typ with
  | TreeMath -> "test_vectors/treemath.json"

let get_testsuite (typ:test_type): testsuite =
  let json = Yojson.Safe.from_channel (open_in (get_filename typ)) in
  match typ with
  | TreeMath -> begin
    match json with
    | `List l ->
      (TreeMath_test (List.map parse_treemath_test l))
    | _ -> failwith "get_testsuite: incorrect test vector format"
  end
