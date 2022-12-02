module MLS.TreeSync.Invariants.Epoch

open Comparse
open MLS.Tree
open MLS.TreeSync.NetworkTypes
open MLS.TreeSync.Types

val leaf_node_epoch:
  #bytes:Type0 -> {|bytes_like bytes|} -> #tkt:treekem_types bytes ->
  leaf_node_nt bytes tkt ->
  nat_lbytes 8
let leaf_node_epoch #bytes #bl #tkt ln =
  match ln.data.source with
  | LNS_key_package -> ln.add_epoch
  | LNS_update -> ln.data.update_epoch
  | LNS_commit -> ln.data.commit_epoch

val epoch_invariant:
  #bytes:Type0 -> {|bytes_like bytes|} -> #tkt:treekem_types bytes ->
  #l:nat -> #i:tree_index l ->
  nat -> treesync bytes tkt l i ->
  bool
let rec epoch_invariant #bytes #bl #tkt #l #i epoch t =
  match t with
  | TLeaf None ->
    true
  | TLeaf (Some ln) ->
    leaf_node_epoch ln <= epoch
  | TNode _ left right ->
    epoch_invariant epoch left && epoch_invariant epoch right
