module MLS.TreeSync.Types

open Comparse.Bytes
open MLS.NetworkTypes
open MLS.TreeSync.NetworkTypes
open MLS.Tree

#set-options "--fuel 1 --ifuel 1"

(** Tree and Paths definitions *)
let treesync (bytes:Type0) {|bytes_like bytes|} (tkt:treekem_types bytes) =
  tree (option (leaf_node_nt bytes tkt)) (option (parent_node_nt bytes tkt))

let external_pathsync (bytes:Type0) {|bytes_like bytes|} (tkt:treekem_types bytes) =
  path (leaf_node_nt bytes tkt) (option tkt.node_content)

(** TreeSync state and accessors *)
noeq type state_t (bytes:Type0) {|bytes_like bytes|} (tkt:treekem_types bytes) = {
  group_id: bytes;
  levels: nat;
  tree: treesync bytes tkt levels 0;
  version: nat;
}

val mk_initial_state: #bytes:Type0 -> {|bytes_like bytes|} -> #tkt:treekem_types bytes -> gid:bytes -> l:nat -> treesync bytes tkt l 0 -> state_t bytes tkt
let mk_initial_state gid l t = {
  group_id = gid;
  levels = l;
  tree = t;
  version = 0;
}

type index_t (#bytes:Type0) {|bytes_like bytes|} (#tkt:treekem_types bytes) (st:state_t bytes tkt) = i:nat{i < pow2 st.levels}
