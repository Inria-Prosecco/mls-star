module MLS.TreeKEM.Parsers

open Comparse
open MLS.Crypto
open MLS.Tree
open MLS.NetworkTypes
open MLS.TreeKEM.Types
open MLS.Symbolic.Parsers

val ps_hpke_private_key:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  parser_serializer_prefix bytes (hpke_private_key bytes)
let ps_hpke_private_key #bytes #cb =
  mk_trivial_isomorphism (ps_lbytes (hpke_private_key_length #bytes))

val ps_treekem_priv:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  l:nat -> i:tree_index l -> li:leaf_index l i ->
  parser_serializer_prefix bytes (treekem_priv bytes l i li)
let ps_treekem_priv #bytes #cb l i li =
  mk_trivial_isomorphism (ps_path ps_hpke_private_key (ps_option ps_hpke_private_key) l i li)

val ps_treekem_leaf:
  #bytes:Type0 -> {|bytes_like bytes|} ->
  parser_serializer_prefix bytes (treekem_leaf bytes)
let ps_treekem_leaf #bytes #bl =
  mk_isomorphism (treekem_leaf bytes)
    ps_bytes
    (fun public_key -> {public_key})
    (fun {public_key} -> public_key)

val ps_treekem_node:
  #bytes:Type0 -> {|bytes_like bytes|} ->
  parser_serializer_prefix bytes (treekem_node bytes)
let ps_treekem_node #bytes #bl =
  mk_isomorphism (treekem_node bytes)
    (bind ps_bytes (fun _ -> ps_list (ps_nat)))
    (fun (|public_key, unmerged_leaves|) -> {public_key; unmerged_leaves})
    (fun {public_key; unmerged_leaves} -> (|public_key, unmerged_leaves|))

val ps_treekem:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  l:nat -> i:tree_index l ->
  parser_serializer_prefix bytes (treekem bytes l i)
let ps_treekem #bytes #cb l i =
  mk_trivial_isomorphism (ps_tree (ps_option ps_treekem_leaf) (ps_option ps_treekem_node) l i)
