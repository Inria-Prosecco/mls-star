module MLS.TreeSync.Types

open MLS.Lib.Array
open Lib.ByteSequence
open MLS.Tree

(** Cryptography *)
let sign_key_t = bytes
let verif_key_t = pub_bytes

let enc_key_t = pub_bytes
let dec_key_t = bytes


(** Identity and Credentials *)
type principal_t = string

type credential_t = {
  cred_version: nat;
  cred_identity: pub_bytes;
  cred_signature_key: verif_key_t;
}

assume val validate_credential: credential_t -> bool


(** Secrets belonging to a Group member  *)
noeq type leaf_secrets_t = {
  identity_sig_key: sign_key_t;
}

(** Definition of a Leaf package *)
type leaf_package_t = {
  lp_credential: credential_t;
  lp_version: nat;
  lp_content: pub_bytes;
  lp_extensions: pub_bytes;
  lp_signature: pub_bytes;
}

let mk_initial_leaf_package (c:credential_t) =
  { lp_credential = c;
    lp_version = 0;
    lp_content = Seq.empty;
    lp_extensions = Seq.empty;
    lp_signature = admit();}


(** Definition of a Node package *)
type node_package_t = {
  np_version: nat;
  np_content_dir: direction;
  np_unmerged_leafs: list nat;
  np_parent_hash: pub_bytes;
  np_content: pub_bytes;
}

(** Tree and Paths definitions *)
type level_n = nat

//TODO: clarify the use of credential_t
type treesync (l:level_n) (n:tree_size l) = tree l n (credential_t & option leaf_package_t) (credential_t & option node_package_t)
type pathsync (l:level_n) (n:tree_size l) (i:leaf_index n) = path l n i (option leaf_package_t) (option node_package_t)

//Data coming from TreeKEM
type external_node_package_t = np:node_package_t{np.np_parent_hash == Seq.empty}
type external_pathsync (l:level_n) (n:tree_size l) (i:leaf_index n) = path l n i leaf_package_t external_node_package_t

(** Operations on the state *)
type operation_t = {
  op_levels: level_n;
  op_treesize: tree_size op_levels;
  op_index: leaf_index op_treesize;
  op_actor: credential_t;
  op_path: pathsync op_levels op_treesize op_index;
}

(** TreeSync state and accessors *)
type state_t = {
  st_group_id: nat;
  st_levels: level_n;
  st_treesize: tree_size st_levels;
  st_tree: treesync st_levels st_treesize;
  st_version: nat;
  st_initial_tree: treesync st_levels st_treesize;
  st_transcript: Seq.seq operation_t;
}

val mk_initial_state: gid:nat -> l:level_n -> n:tree_size l -> treesync l n -> Tot state_t
let mk_initial_state gid l n t = {
  st_group_id = gid; st_levels = l;
  st_treesize = n;
  st_tree = t; st_version = 0;
  st_initial_tree = t;
  st_transcript = empty;}

val group_id: state_t -> nat
let group_id st = st.st_group_id

val max_size: state_t -> nat
let max_size st = pow2 st.st_levels

val epoch: state_t -> nat
let epoch st = st.st_version

type index_t (st:state_t) = i:nat{i < st.st_treesize}
