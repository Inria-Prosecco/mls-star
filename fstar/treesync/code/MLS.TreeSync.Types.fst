module MLS.TreeSync.Types

open Comparse
open MLS.Tree
open MLS.TreeSync.NetworkTypes

/// TreeSync's tree. Blank nodes are represented with `None`.
let treesync (bytes:Type0) {|bytes_like bytes|} (tkt:treekem_types bytes) =
  tree (option (leaf_node_nt bytes tkt)) (option (parent_node_nt bytes tkt))

/// An authenticated path. The leaf contains a parent-hash and a signature.
let pathsync (bytes:Type0) {|bytes_like bytes|} (tkt:treekem_types bytes) =
  path (leaf_node_nt bytes tkt) (option tkt.node_content)

/// An un-authenticated path, outputted by TreeKEM.
/// It lacks signature in the leaf, and the leaf parent hash must be re-computed.
let external_pathsync (bytes:Type0) {|bytes_like bytes|} (tkt:treekem_types bytes) =
  path (leaf_node_data_nt bytes tkt) (option tkt.node_content)
