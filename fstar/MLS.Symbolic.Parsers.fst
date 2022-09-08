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
%splice [ps_tree_internal_node_is_valid] (gen_is_valid_lemma (`tree_internal_node))

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

val ps_tree_is_valid: #bytes:Type0 -> {|bytes_like bytes|} -> #leaf_t:Type0 -> #node_t:Type0 -> ps_leaf_t:parser_serializer bytes leaf_t -> ps_node_t:parser_serializer_unit bytes node_t -> l:nat -> i:tree_index l -> pre:bytes_compatible_pre bytes -> x:tree leaf_t node_t l i -> Lemma
  ((ps_tree ps_leaf_t ps_node_t l i).is_valid pre x <==> (
    match x with
    | TLeaf y -> ps_leaf_t.is_valid pre y
    | TNode y left right -> ps_node_t.is_valid pre y /\ (ps_tree ps_leaf_t ps_node_t (l-1) (left_index i)).is_valid pre left /\ (ps_tree ps_leaf_t ps_node_t (l-1) (right_index i)).is_valid pre right
  ))
  [SMTPat ((ps_tree ps_leaf_t ps_node_t l i).is_valid pre x)]
let ps_tree_is_valid #bytes #bl #leaf_t #node_t ps_leaf_t ps_node_t l i pre x =
  // For some reason, reveal_opaque doesn't work here
  normalize_term_spec (ps_tree ps_leaf_t ps_node_t l i)
