module MLS.Symbolic.Parsers

open Comparse
open MLS.Tree
open MLS.NetworkTypes
open MLS.TreeSync.NetworkTypes
open MLS.TreeSync.Types
open MLS.TreeSync.Invariants.AuthService
open MLS.TreeSync.Symbolic.IsValid

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

val ps_treesync: #bytes:Type0 -> {|bytes_like bytes|} -> tkt:treekem_types bytes -> l:nat -> i:tree_index l -> parser_serializer bytes (treesync bytes tkt l i)
let ps_treesync #bytes tkt l i =
  ps_tree (ps_option (ps_leaf_node_nt tkt)) (ps_option (ps_parent_node_nt tkt)) l i

val ps_treesync_is_well_formed: #bytes:Type0 -> {|bytes_like bytes|} -> tkt:treekem_types bytes -> l:nat -> i:tree_index l -> pre:bytes_compatible_pre bytes -> x:treesync bytes tkt l i -> Lemma
  (is_well_formed_partial (ps_treesync tkt l i) pre x <==> treesync_has_pre pre x)
let rec ps_treesync_is_well_formed #bytes #bl tkt l i pre x =
  match x with
  | TLeaf _ -> ()
  | TNode data left right ->
    ps_treesync_is_well_formed tkt (l-1) (left_index i) pre left;
    ps_treesync_is_well_formed tkt (l-1) (right_index i) pre right

val ps_as_tokens: #bytes:Type0 -> {|bytes_like bytes|} -> #as_token:Type0 -> parser_serializer bytes as_token -> l:nat -> i:tree_index l -> parser_serializer bytes (as_tokens bytes as_token l i)
let ps_as_tokens #bytes #bl #as_token ps_token l i =
  ps_tree (ps_option ps_token) ps_unit l i
