module MLS.TreeSync.Refined.Types

open MLS.Crypto
open MLS.Tree
open MLS.TreeSync.NetworkTypes
open MLS.TreeSync.Types
open MLS.TreeSync.Invariants.UnmergedLeaves
open MLS.TreeSync.Invariants.ParentHash

let treesync (bytes:Type0) {|crypto_bytes bytes|} (tkt:treekem_types bytes) (l:nat) (i:tree_index l) =
  t:treesync bytes tkt l i{unmerged_leaves_ok t /\ parent_hash_invariant t}

let external_pathsync = external_pathsync
