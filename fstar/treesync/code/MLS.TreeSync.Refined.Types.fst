module MLS.TreeSync.Refined.Types

open MLS.Crypto
open MLS.Tree
open MLS.NetworkTypes
open MLS.TreeSync.NetworkTypes
open MLS.TreeSync.Types
open MLS.TreeSync.Invariants.UnmergedLeaves
open MLS.TreeSync.Invariants.ParentHash
open MLS.TreeSync.Invariants.ValidLeaves

let treesync_valid (bytes:Type0) {|crypto_bytes bytes|} (tkt:treekem_types bytes) (l:nat) (i:tree_index l) (group_id:mls_bytes bytes) =
  t:treesync bytes tkt l i{unmerged_leaves_ok t /\ parent_hash_invariant t /\ valid_leaves_invariant group_id t}
