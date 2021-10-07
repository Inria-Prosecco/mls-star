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
  version: nat;
  identity: pub_bytes;
  signature_key: verif_key_t;
}

assume val validate_credential: credential_t -> bool


(** Secrets belonging to a Group member  *)
noeq type leaf_secrets_t = {
  identity_sig_key: sign_key_t;
}

(** Definition of a Leaf package *)
type leaf_package_t = {
  credential: credential_t;
  version: nat;
  content: pub_bytes;
  extensions: pub_bytes;
  signature: pub_bytes;
}

let mk_initial_leaf_package (c:credential_t) =
  { credential = c;
    version = 0;
    content = Seq.empty;
    extensions = Seq.empty;
    signature = admit();}


(** Definition of a Node package *)
type node_package_t = {
  version: nat;
  content_dir: direction;
  unmerged_leafs: list nat;
  parent_hash: pub_bytes;
  content: pub_bytes;
}

(** Tree and Paths definitions *)
type level_n = nat

//TODO: clarify the use of credential_t
type treesync (l:level_n) (n:tree_size l) = tree l n (credential_t & option leaf_package_t) (credential_t & option node_package_t)
type pathsync (l:level_n) (n:tree_size l) (i:leaf_index n) = path l n i (option leaf_package_t) (option node_package_t)

//Data coming from TreeKEM
type external_node_package_t = np:node_package_t{np.parent_hash == Seq.empty}
type external_pathsync (l:level_n) (n:tree_size l) (i:leaf_index n) = path l n i leaf_package_t external_node_package_t

(*
This way to describe operations doesn't work well in practice:
- the number of leaves in the tree is needed for the type of `op_path` (because the number of nodes to update depends on the level, the tree size and the index)
- operations such as Add, Remove change the tree size
- therefore we can't pre-compute a bunch of operations and then apply them to the tree, because some operations will be converted with a wrong tree size
(** Operations on the state *)
type operation_t = {
  op_levels: level_n;
  op_treesize: tree_size op_levels;
  op_index: leaf_index op_treesize;
  op_actor: credential_t;
  op_path: pathsync op_levels op_treesize op_index;
}
*)

type operation_t =
  | Op_Add: actor:credential_t -> lp:leaf_package_t -> operation_t
  | Op_Update: actor:credential_t -> lp:leaf_package_t -> operation_t
  | Op_Remove: actor:credential_t -> ind:nat -> operation_t
  | Op_UpdatePath: actor:credential_t -> l:level_n -> n:tree_size l -> i:leaf_index n -> pathsync l n i -> operation_t

(** TreeSync state and accessors *)
type state_t = {
  group_id: nat;
  levels: level_n;
  treesize: tree_size levels;
  tree: treesync levels treesize;
  version: nat;
  //initial_tree: treesync levels treesize;
  transcript: Seq.seq operation_t;
}

val mk_initial_state: gid:nat -> l:level_n -> n:tree_size l -> treesync l n -> Tot state_t
let mk_initial_state gid l n t = {
  group_id = gid; levels = l;
  treesize = n;
  tree = t; version = 0;
  //initial_tree = t;
  transcript = empty;}

val group_id: state_t -> nat
let group_id st = st.group_id

val max_size: state_t -> nat
let max_size st = pow2 st.levels

val epoch: state_t -> nat
let epoch st = st.version

type index_t (st:state_t) = i:nat{i < st.treesize}
