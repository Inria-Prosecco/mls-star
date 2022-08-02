module MLS.TreeSync.Types

open Comparse
open MLS.Tree
open MLS.TreeSync.NetworkTypes

let treesync (bytes:Type0) {|bytes_like bytes|} (tkt:treekem_types bytes) =
  tree (option (leaf_node_nt bytes tkt)) (option (parent_node_nt bytes tkt))

let external_pathsync (bytes:Type0) {|bytes_like bytes|} (tkt:treekem_types bytes) =
  path (leaf_node_nt bytes tkt) (option tkt.node_content)
