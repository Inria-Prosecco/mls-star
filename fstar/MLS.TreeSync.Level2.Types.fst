module MLS.TreeSync.Level2.Types

open MLS.Crypto
open MLS.Tree
open MLS.TreeSync.NetworkTypes
open MLS.TreeSync.Level1.Types
open MLS.TreeSync.Level1.Invariants

let treesync (bytes:Type0) {|crypto_bytes bytes|} (tkt:treekem_types bytes) (l:nat) (i:tree_index l) =
  t:treesync bytes tkt l i{parent_hash_invariant t}

let external_pathsync = external_pathsync
