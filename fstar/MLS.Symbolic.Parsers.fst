module MLS.Symbolic.Parsers

open Comparse
open MLS.Tree

#set-options "--fuel 1 --ifuel 1"

noeq type tree_internal_node (bytes:Type0) {|bytes_like bytes|} (leaf_t:Type0) (node_t:Type0) (l:pos) (i:tree_index l) (ps_node_t:parser_serializer_unit bytes node_t) (ps_left:parser_serializer bytes (tree leaf_t node_t (l-1) (left_index i))) (ps_right:parser_serializer bytes (tree leaf_t node_t (l-1) (right_index i))) = {
  [@@@ with_parser #bytes ps_left]
  left: tree leaf_t node_t (l-1) (left_index i);
  [@@@ with_parser #bytes ps_node_t]
  data: node_t;
  [@@@ with_parser #bytes ps_right]
  right: tree leaf_t node_t (l-1) (right_index i);
}

%splice [ps_tree_internal_node] (gen_parser (`tree_internal_node))
%splice [ps_tree_internal_node_is_well_formed] (gen_is_well_formed_lemma (`tree_internal_node))

[@@"opaque_to_smt"]
val ps_tree: #bytes:Type0 -> {|bytes_like bytes|} -> #leaf_t:Type0 -> #node_t:Type0 -> parser_serializer bytes leaf_t -> parser_serializer_unit bytes node_t -> l:nat -> i:tree_index l -> parser_serializer bytes (tree leaf_t node_t l i)
let rec ps_tree #bytes #bl #leaf_t #node_t ps_leaf_t ps_node_t l i =
  if l = 0 then (
    mk_isomorphism
      (tree leaf_t node_t 0 i)
      ps_leaf_t
      (fun x -> TLeaf x)
      (fun (TLeaf x) -> x)
  ) else (
    mk_isomorphism
      (tree leaf_t node_t l i)
      (ps_tree_internal_node #bytes #bl leaf_t node_t l i ps_node_t (ps_tree ps_leaf_t ps_node_t (l-1) (left_index i)) (ps_tree ps_leaf_t ps_node_t (l-1) (right_index i)))
      (fun {left; data; right} -> TNode data left right)
      (fun (TNode data left right) -> {left; data; right})
  )

val ps_tree_is_well_formed: #bytes:Type0 -> {|bytes_like bytes|} -> #leaf_t:Type0 -> #node_t:Type0 -> ps_leaf_t:parser_serializer bytes leaf_t -> ps_node_t:parser_serializer_unit bytes node_t -> l:nat -> i:tree_index l -> pre:bytes_compatible_pre bytes -> x:tree leaf_t node_t l i -> Lemma
  (is_well_formed_partial (ps_tree ps_leaf_t ps_node_t l i) pre x <==> (
    match x with
    | TLeaf y -> is_well_formed_partial ps_leaf_t pre y
    | TNode y left right -> is_well_formed_partial ps_node_t pre y /\ is_well_formed_partial (ps_tree ps_leaf_t ps_node_t (l-1) (left_index i)) pre left /\ is_well_formed_partial (ps_tree ps_leaf_t ps_node_t (l-1) (right_index i)) pre right
  ))
  [SMTPat (is_well_formed_partial (ps_tree ps_leaf_t ps_node_t l i) pre x)]
let ps_tree_is_well_formed #bytes #bl #leaf_t #node_t ps_leaf_t ps_node_t l i pre x =
  // For some reason, reveal_opaque doesn't work here
  normalize_term_spec (ps_tree ps_leaf_t ps_node_t l i)

noeq type path_internal_node (bytes:Type0) {|bytes_like bytes|} (leaf_t:Type0) (node_t:Type0) (l:pos) (i:tree_index l) (li:leaf_index l i) (ps_node_t:parser_serializer_unit bytes node_t) (ps_next:parser_serializer bytes (path leaf_t node_t (l-1) (if is_left_leaf li then left_index i else right_index i) li)) = {
  [@@@ with_parser #bytes ps_node_t]
  data: node_t;
  [@@@ with_parser #bytes ps_next]
  next: path leaf_t node_t (l-1) (if is_left_leaf li then left_index i else right_index i) li;
}

%splice [ps_path_internal_node] (gen_parser (`path_internal_node))
%splice [ps_path_internal_node_is_well_formed] (gen_is_well_formed_lemma (`path_internal_node))

[@@"opaque_to_smt"]
val ps_path: #bytes:Type0 -> {|bytes_like bytes|} -> #leaf_t:Type0 -> #node_t:Type0 -> parser_serializer bytes leaf_t -> parser_serializer_unit bytes node_t -> l:nat -> i:tree_index l -> li:leaf_index l i -> parser_serializer bytes (path leaf_t node_t l i li)
let rec ps_path #bytes #bl #leaf_t #node_t ps_leaf_t ps_node_t l i li =
  if l = 0 then (
    mk_isomorphism
      (path leaf_t node_t 0 i li)
      ps_leaf_t
      (fun x -> PLeaf x)
      (fun (PLeaf x) -> x)
  ) else (
    mk_isomorphism
      (path leaf_t node_t l i li)
      (ps_path_internal_node #bytes #bl leaf_t node_t l i li ps_node_t (ps_path ps_leaf_t ps_node_t (l-1) (if is_left_leaf li then left_index i else right_index i) li))
      (fun {data; next} -> PNode data next)
      (fun (PNode data next) -> {data; next;})
  )

val ps_path_is_well_formed: #bytes:Type0 -> {|bytes_like bytes|} -> #leaf_t:Type0 -> #node_t:Type0 -> ps_leaf_t:parser_serializer bytes leaf_t -> ps_node_t:parser_serializer_unit bytes node_t -> l:nat -> i:tree_index l -> li:leaf_index l i -> pre:bytes_compatible_pre bytes -> x:path leaf_t node_t l i li -> Lemma
  (is_well_formed_partial (ps_path ps_leaf_t ps_node_t l i li) pre x <==> (
    match x with
    | PLeaf y -> is_well_formed_partial ps_leaf_t pre y
    | PNode y next -> is_well_formed_partial ps_node_t pre y /\ is_well_formed_partial (ps_path ps_leaf_t ps_node_t (l-1) (if is_left_leaf li then left_index i else right_index i) li) pre next
  ))
  [SMTPat (is_well_formed_partial (ps_path ps_leaf_t ps_node_t l i li) pre x)]
let ps_path_is_well_formed #bytes #bl #leaf_t #node_t ps_leaf_t ps_node_t l i li pre x =
  // For some reason, reveal_opaque doesn't work here
  normalize_term_spec (ps_path ps_leaf_t ps_node_t l i li)
