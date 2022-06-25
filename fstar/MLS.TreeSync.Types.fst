module MLS.TreeSync.Types

open Comparse.Bytes
open MLS.NetworkTypes
open MLS.Tree

#set-options "--fuel 1 --ifuel 1"

(** Identity and Credentials *)
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
  content: external_content bytes;
  credential: credential_t bytes;
  capabilities: capabilities_nt bytes;
  source: leaf_node_source_nt;
  lifetime: leaf_node_lifetime_nt source;
  parent_hash: leaf_node_parent_hash_nt bytes source;
  extensions: bytes;
  signature: bytes;
}

(** Definition of a Node package *)
type node_package_t (bytes:Type0) {|bytes_like bytes|} = {
  version: nat; //For security proofs, should be erasable
  unmerged_leaves: list nat;
  parent_hash: mls_bytes bytes;
  content: external_content bytes;
}

(** Tree and Paths definitions *)
type treesync (bytes:Type0) {|bytes_like bytes|} (l:nat) (i:tree_index l) = tree l i (option (leaf_package_t bytes)) (option (node_package_t bytes))

type external_pathsync (bytes:Type0) {|bytes_like bytes|} (l:nat) (i:tree_index l) (li:leaf_index l i) = path l i li (leaf_package_t bytes) (option (external_content bytes))

type operation_t (bytes:Type0) {|bytes_like bytes|} =
  | Op_Add: lp:leaf_package_t bytes -> operation_t bytes
  | Op_Update: lp:leaf_package_t bytes -> operation_t bytes
  | Op_Remove: ind:nat -> operation_t bytes
  | Op_UpdatePath: l:nat -> i:tree_index l -> li:leaf_index l i -> external_pathsync bytes l i li -> operation_t bytes

(** TreeSync state and accessors *)
type state_t (bytes:Type0) {|bytes_like bytes|} = {
  group_id: bytes;
  levels: nat;
  tree: treesync bytes levels 0;
  version: nat;
  //initial_tree: treesync levels treesize;
  transcript: Seq.seq (operation_t bytes);
}

val mk_initial_state: #bytes:Type0 -> {|bytes_like bytes|} -> gid:bytes -> l:nat -> treesync bytes l 0 -> state_t bytes
let mk_initial_state gid l t = {
  group_id = gid; levels = l;
  tree = t; version = 0;
  //initial_tree = t;
  transcript = Seq.empty;}

type index_t (#bytes:Type0) {|bytes_like bytes|} (st:state_t bytes) = i:nat{i < pow2 st.levels}
