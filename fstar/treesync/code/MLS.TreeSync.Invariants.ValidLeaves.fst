module MLS.TreeSync.Invariants.ValidLeaves

open Comparse
open MLS.Crypto
open MLS.NetworkTypes
open MLS.Tree
open MLS.TreeSync.NetworkTypes
open MLS.TreeSync.Types
open MLS.TreeSync.Operations //leaf_is_valid

#set-options "--fuel 1 --ifuel 1"

/// The "valid leaves" invariant:
/// every non-blank leaf has a valid signature.
val valid_leaves_invariant:
  #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes ->
  #l:nat -> #i:tree_index l ->
  mls_bytes bytes -> treesync bytes tkt l i ->
  bool
let rec valid_leaves_invariant #bytes #cb #tkt #l #i group_id t =
  match t with
  | TLeaf None -> true
  | TLeaf (Some ln) -> leaf_is_valid ln group_id i
  | TNode _ left right ->
    valid_leaves_invariant group_id left && valid_leaves_invariant group_id right
