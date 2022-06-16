module MLS.TreeSyncTreeKEMBinder

open Comparse
open MLS.Crypto
open MLS.NetworkTypes
open MLS.Tree
open MLS.NetworkBinder
open MLS.TreeSync.Types
open MLS.TreeKEM.Types
open MLS.Result

#set-options "--fuel 1 --ifuel 1"

val encrypted_path_secret_nt_to_tk: #bytes:Type0 -> {|crypto_bytes bytes|} -> hpke_ciphertext_nt bytes -> result (path_secret_ciphertext bytes)
let encrypted_path_secret_nt_to_tk #bytes #cb x =
  if not (length (x.kem_output <: bytes) = hpke_kem_output_length #bytes) then
    internal_failure "encrypted_path_secret_nt_to_tk: kem_output has wrong length"
  else
    return ({
      kem_output = x.kem_output;
      ciphertext = x.ciphertext;
    })

val treesync_to_treekem_node_package: #bytes:Type0 -> {|crypto_bytes bytes|} -> nat -> node_package_t bytes -> result (key_package bytes)
let treesync_to_treekem_node_package #bytes #cb nb_left_leaves np =
  content <-- from_option "treesync_to_treekem_node_package: Couldn't parse node content"
    (parse (treekem_content_nt bytes) np.content.content);
  impl_data <-- from_option "treesync_to_treekem_node_package: Couldn't parse node impl data"
    (parse (treekem_impl_data_nt bytes) np.content.impl_data);
  path_secret_ciphertext <-- mapM (encrypted_path_secret_nt_to_tk #bytes) (Seq.seq_to_list impl_data.encrypted_path_secret);
  unmerged_leaves <-- mapM (fun (unmerged_leaf:nat) ->
    if not (nb_left_leaves <= unmerged_leaf) then
      error "treesync_to_treekem_node_package: unmerged_leaf index too small"
    else
      return ((unmerged_leaf - nb_left_leaves) <: nat)
  ) np.unmerged_leaves;
  if not (length (content.public_key <: bytes) = hpke_public_key_length #bytes) then
    error "treesync_to_treekem_node_package: public key has wrong length"
  else (
    return ({
      public_key = content.public_key;
      version = np.version;
      last_group_context = impl_data.last_group_context;
      unmerged_leaves = unmerged_leaves;
      path_secret_from = impl_data.content_dir;
      path_secret_ciphertext = path_secret_ciphertext;
    })
  )

val treesync_to_treekem_aux: #bytes:Type0 -> {|crypto_bytes bytes|} -> #l:nat -> #n:tree_size l -> nat -> treesync bytes l n -> result (treekem bytes l n)
let rec treesync_to_treekem_aux #bytes #cb #l #n nb_left_leaves t =
  match t with
  | TLeaf None ->
    return (TLeaf None)
  | TLeaf (Some lp) ->
    lpc <-- from_option "treesync_to_treekem: Couldn't parse leaf content"
      (parse (treekem_content_nt bytes) lp.content.content);
    if length (lpc.public_key <: bytes) = hpke_public_key_length #bytes then
      return (TLeaf (Some ({public_key = lpc.public_key; version = lp.version} <: member_info bytes)))
    else
      error "treesync_to_treekem: public key has wrong length"
  | TSkip _ t' ->
    result <-- treesync_to_treekem_aux nb_left_leaves t';
    return (TSkip _ result)
  | TNode onp left right -> begin
    tk_left <-- treesync_to_treekem_aux nb_left_leaves left;
    tk_right <-- treesync_to_treekem_aux (nb_left_leaves + pow2 (l-1)) right;
    match onp with
    | None ->
      return (TNode None tk_left tk_right)
    | Some np ->
      kp <-- treesync_to_treekem_node_package nb_left_leaves np;
      return (TNode (Some kp) tk_left tk_right)
  end

val treesync_to_treekem: #bytes:Type0 -> {|crypto_bytes bytes|} -> #l:nat -> #n:tree_size l -> treesync bytes l n -> result (treekem bytes l n)
let treesync_to_treekem #bytes #cb #l #n t =
  treesync_to_treekem_aux 0 t

val encrypted_path_secret_tk_to_nt: #bytes:Type0 -> {|crypto_bytes bytes|} -> path_secret_ciphertext bytes -> result (hpke_ciphertext_nt bytes)
let encrypted_path_secret_tk_to_nt #bytes #cb x =
  if not (length (x.kem_output <: bytes) < pow2 16) then
    internal_failure "encrypted_path_secret_tk_to_nt: kem_output too long"
  else if not (length (x.ciphertext <: bytes) < pow2 16) then
    internal_failure "encrypted_path_secret_tk_to_nt: ciphertext too long"
  else
    return ({
      kem_output = x.kem_output;
      ciphertext = x.ciphertext;
    } <: hpke_ciphertext_nt bytes)

val treekem_to_treesync_node_package: #bytes:Type0 -> {|crypto_bytes bytes|} -> key_package bytes -> result (external_content bytes)
let treekem_to_treesync_node_package #bytes #cb kp =
  ciphertexts <-- mapM encrypted_path_secret_tk_to_nt kp.path_secret_ciphertext;
  if not (bytes_length ps_hpke_ciphertext_nt ciphertexts < pow2 16) then
    internal_failure "treekem_to_treesync: ciphertexts too long"
  else if not (length kp.last_group_context < pow2 64) then
    internal_failure "treekem_to_treesync: last group context too long (internal error)"
  else begin
    Seq.lemma_list_seq_bij ciphertexts;
    return ({
      content = serialize (treekem_content_nt bytes) ({
        public_key = kp.public_key;
      });
      impl_data = serialize (treekem_impl_data_nt bytes) ({
        content_dir = kp.path_secret_from;
        encrypted_path_secret = Seq.seq_of_list ciphertexts;
        last_group_context = kp.last_group_context;
      });
    } <: external_content bytes)
  end

// Some remarks about the `new_leaf_package` argument
// This function is used in two cases:
// - By processing an update path coming from the network. In that case, the update path provided a new leaf package to use, which will go in this `new_leaf_package` argument.
//   Why change its public key in that case? Well it doesn't really change, because the public key in `PLeaf` and the public key of `new_leaf_package` will be the same.
//   This is because the `PLeaf` content is equal to `key_package_to_treekem kp` and `new_leaf_package` is equal to `key_package_to_treesync kp` for the same kp
//   The parent hash extension and the signature will be checked when converting the external_pathsync to a pathsync
// - When we generate an updatepath, and convert it to treesync before converting it to an update_path_nt.
//   In that case, `new_leaf_package` need to be equal to our previous leaf package. The HPKE public key will be updated here.
//   The parent hash and signature need to be updated, but this will be done in the external_pathsync -> pathsync conversion.
val treekem_to_treesync: #bytes:Type0 -> {|crypto_bytes bytes|} -> #l:nat -> #n:tree_size l -> #i:leaf_index n -> leaf_package_t bytes -> pathkem bytes l n i -> result (external_pathsync bytes l n i)
let rec treekem_to_treesync #bytes #cb #l #n #i new_leaf_package pk =
  match pk with
  | PLeaf mi ->
    return (PLeaf ({
      new_leaf_package with
      version = (mi <: member_info bytes).version;
      content = {
        content = serialize (treekem_content_nt bytes) ({
          public_key = (mi <: member_info bytes).public_key;
        });
        impl_data = empty;
      };
    } <: leaf_package_t bytes))
  | PSkip _ pk' ->
    result <-- treekem_to_treesync new_leaf_package pk';
    return (PSkip _ result)
  | PNode kp pk_next ->
    next <-- treekem_to_treesync new_leaf_package pk_next;
    np <-- treekem_to_treesync_node_package kp;
    return (PNode np next)
