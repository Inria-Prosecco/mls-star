module MLS.TreeSync.Types

open Comparse.Bytes
open MLS.Tree

(** Identity and Credentials *)
type principal_t = string

type credential_t (bytes:Type0) {|bytes_like bytes|} = {
  version: nat; //For security proofs, should be erasable
  identity: bytes;
  signature_key: bytes;
}

(** Secrets belonging to a Group member  *)
noeq type leaf_secrets_t (bytes:Type0) {|bytes_like bytes|} = {
  identity_sig_key: bytes;
}

type external_content (bytes:Type0) {|bytes_like bytes|} = {
  content: bytes; //Roughly, data sent on the wire
  impl_data: bytes; //Roughly, internal data specific to the implementation details
}

(** Definition of a Leaf package *)
type leaf_package_t (bytes:Type0) {|bytes_like bytes|} = {
  version: nat; //For security proofs, should be erasable
  credential: credential_t bytes;
  endpoint_id: bytes;
  content: external_content bytes;
  extensions: bytes;
  signature: bytes;
}

(** Definition of a Node package *)
type node_package_t (bytes:Type0) {|bytes_like bytes|} = {
  version: nat; //For security proofs, should be erasable
  unmerged_leaves: list nat;
  parent_hash: bytes;
  content: external_content bytes;
}

(** Tree and Paths definitions *)
type level_n = nat

type treesync (bytes:Type0) {|bytes_like bytes|} (l:level_n) (n:tree_size l) = tree l n (option (leaf_package_t bytes)) (option (node_package_t bytes))
type pathsync (bytes:Type0) {|bytes_like bytes|} (l:level_n) (n:tree_size l) (i:leaf_index n) = path l n i (option (leaf_package_t bytes)) (option (node_package_t bytes))

type external_pathsync (bytes:Type0) {|bytes_like bytes|} (l:level_n) (n:tree_size l) (i:leaf_index n) = path l n i (leaf_package_t bytes) (external_content bytes)

type operation_t (bytes:Type0) {|bytes_like bytes|} =
  | Op_Add: lp:leaf_package_t bytes -> operation_t bytes
  | Op_Update: lp:leaf_package_t bytes -> operation_t bytes
  | Op_Remove: ind:nat -> operation_t bytes
  | Op_UpdatePath: l:level_n -> n:tree_size l -> i:leaf_index n -> external_pathsync bytes l n i -> operation_t bytes

(** TreeSync state and accessors *)
type state_t (bytes:Type0) {|bytes_like bytes|} = {
  group_id: bytes;
  levels: level_n;
  treesize: tree_size levels;
  tree: treesync bytes levels treesize;
  version: nat;
  //initial_tree: treesync levels treesize;
  transcript: Seq.seq (operation_t bytes);
}

val mk_initial_state: #bytes:Type0 -> {|bytes_like bytes|} -> gid:bytes -> l:level_n -> n:tree_size l -> treesync bytes l n -> state_t bytes
let mk_initial_state gid l n t = {
  group_id = gid; levels = l;
  treesize = n;
  tree = t; version = 0;
  //initial_tree = t;
  transcript = Seq.empty;}

type index_t (#bytes:Type0) {|bytes_like bytes|} (st:state_t bytes) = i:nat{i < st.treesize}
