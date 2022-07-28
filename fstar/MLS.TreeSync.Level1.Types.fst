module MLS.TreeSync.Level1.Types

open Comparse
open MLS.Tree
open MLS.TreeSync.NetworkTypes
open MLS.TreeSync.Level0.Types
open MLS.TreeSync.Level0.Invariants

let treesync (bytes:Type0) {|bytes_like bytes|} (tkt:treekem_types bytes) (l:nat) (i:tree_index l) =
  t:treesync bytes tkt l i{unmerged_leaves_ok t}

let external_pathsync = external_pathsync
