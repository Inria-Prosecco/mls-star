module MLS.TreeKEM.API

open Comparse
open MLS.Result
open MLS.Crypto
open MLS.NetworkTypes
open MLS.Tree
open MLS.TreeCommon
open MLS.TreeCommon.Lemmas
open MLS.TreeKEM.Types
open MLS.TreeKEM.Operations
open MLS.TreeKEM.API.Types

(*** Create ***)

val create:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  hpke_private_key bytes -> bytes ->
  treekem_state bytes 0
let create #bytes #cb dec_key enc_key =
  {
    levels = 0;
    tree = TLeaf (Some ({public_key = enc_key} <: treekem_leaf bytes));
    priv = PLeaf dec_key
  }

(*** Welcome ***)

val welcome:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  #l:nat ->
  treekem bytes l 0 -> hpke_private_key bytes -> option (bytes & nat) -> leaf_ind:nat ->
  result (treekem_state bytes leaf_ind)
let welcome #bytes #cb #l t leaf_decryption_key opt_path_secret_and_inviter_ind leaf_ind =
  if not (leaf_ind < pow2 l) then
    error "welcome: leaf_index too big"
  else (
    let priv = create_empty_priv leaf_decryption_key in
    let? priv =
      match opt_path_secret_and_inviter_ind with
      | None -> return priv
      | Some (path_secret, inviter_ind) ->
        if not (leaf_ind <> inviter_ind) then
          error "welcome: leaf_index and inviter index are the same"
        else if not (inviter_ind < pow2 l) then
          error "welcome: inviter_index too big"
        else
          let path_secret_level = compute_least_common_ancestor_level priv inviter_ind in
          let? (priv, _) = path_apply_path t priv path_secret path_secret_level in
          return priv
    in
    assume(treekem_invariant t);
    assume(treekem_state_invariant t priv);
    return {
      levels = l;
      tree = t;
      priv;
    }
  )

(*** Add ***)

val add:
  #bytes:Type0 -> {|crypto_bytes bytes|} -> #leaf_ind:nat ->
  treekem_state bytes leaf_ind -> treekem_leaf bytes ->
  treekem_state bytes leaf_ind & nat
let add #bytes #cb #leaf_ind st kp =
  match find_empty_leaf st.tree with
  | Some i -> (
    assume(treekem_invariant (tree_add st.tree i kp));
    assume(treekem_state_invariant (tree_add st.tree i kp) st.priv);
    ({ st with
      tree = tree_add st.tree i kp;
    }, (i <: nat))
  )
  | None -> (
    find_empty_leaf_tree_extend st.tree;
    let extended_tree = tree_extend st.tree in
    let i = Some?.v (find_empty_leaf extended_tree) in
    assume(treekem_invariant (tree_add extended_tree i kp));
    assume(treekem_state_invariant (tree_add extended_tree i kp) (path_extend st.priv));
    ({ st with
      levels = st.levels+1;
      tree = tree_add extended_tree i kp;
      priv = path_extend st.priv;
    }, (i <: nat))
  )

(*** Update ***)

val update:
  #bytes:Type0 -> {|crypto_bytes bytes|} -> #leaf_ind:nat ->
  st:treekem_state bytes leaf_ind -> treekem_leaf bytes -> treekem_index st ->
  treekem_state bytes leaf_ind
let update #bytes #cb #leaf_ind st lp i =
  assume(treekem_invariant (tree_update st.tree i lp));
  assume(treekem_state_invariant (tree_update st.tree i lp) st.priv);
  { st with tree = tree_update st.tree i lp; }

(*** Remove ***)

val remove:
  #bytes:Type0 -> {|crypto_bytes bytes|} -> #leaf_ind:nat ->
  st:treekem_state bytes leaf_ind -> i:treekem_index st{i <> leaf_ind} ->
  treekem_state bytes leaf_ind
let remove #bytes #cb #leaf_ind st i =
  let blanked_tree = (tree_remove st.tree i) in
  if TNode? blanked_tree && is_tree_empty (TNode?.right blanked_tree) then (
    assume(leaf_ind < pow2 (st.levels-1));
    assume(treekem_invariant (tree_truncate blanked_tree));
    assume(treekem_state_invariant (tree_truncate blanked_tree) (path_truncate st.priv));
    { st with
      levels = st.levels-1;
      tree = tree_truncate blanked_tree;
      priv = path_truncate st.priv;
    }
  ) else (
    assume(treekem_invariant blanked_tree);
    assume(treekem_state_invariant blanked_tree st.priv);
    { st with
      tree = blanked_tree;
    }
  )

(*** Process Commit ***)

val commit:
  #bytes:Type0 -> {|crypto_bytes bytes|} -> #leaf_ind:nat ->
  st:treekem_state bytes leaf_ind -> #li:treekem_index st{li <> leaf_ind} -> p:pathkem bytes st.levels 0 li{pathkem_filtering_ok st.tree p} -> list nat -> group_context_nt bytes ->
  result (treekem_state bytes leaf_ind & bytes)
let commit #bytes #cb #leaf_ind st #li p excluded_leaves group_context =
  let un_added_tree = un_add st.tree excluded_leaves in
  assume(treekem_invariant un_added_tree);
  if not (check_update_path_ciphertexts_lengthes un_added_tree p) then (
    error "TreeKEM.commit: bad UpdatePath ciphertext lengths"
  ) else (
    assume(treekem_state_invariant un_added_tree st.priv);
    assume(pathkem_filtering_ok un_added_tree p);
    let? (path_secret, least_common_ancestor_level) = get_path_secret un_added_tree st.priv p group_context in
    let new_tree = tree_apply_path st.tree p in
    let? (new_priv, root_secret) = path_apply_path new_tree st.priv path_secret least_common_ancestor_level in
    assume(treekem_invariant new_tree);
    assume(treekem_state_invariant new_tree new_priv);
    return ({ st with
      tree = new_tree;
      priv = new_priv;
    }, root_secret)
  )

(*** Create Commit ***)

val prepare_create_commit_entropy_lengths:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  list nat
let prepare_create_commit_entropy_lengths #bytes #cb =
  [hpke_private_key_length #bytes; kdf_length #bytes]

type pending_commit (#bytes:Type0) {|crypto_bytes bytes|} (#leaf_ind:nat) (st:treekem_state bytes leaf_ind) = {
  path_secrets: path_secrets:path_secrets bytes st.levels 0 leaf_ind{forget_path_secrets path_secrets == generate_forgotten_path_secrets st.tree leaf_ind};
  commit_secret: bytes;
}

val prepare_create_commit:
  #bytes:Type0 -> {|crypto_bytes bytes|} -> #leaf_ind:nat ->
  st:treekem_state bytes leaf_ind ->
  randomness bytes (prepare_create_commit_entropy_lengths #bytes) ->
  result (pending_commit st & pre_pathkem bytes st.levels 0 leaf_ind)
let prepare_create_commit #bytes #cb #leaf_ind st rand =
  let leaf_sk, rand = dest_randomness rand in
  let path_secret_0, rand = dest_randomness rand in
  let? (path_secrets, commit_secret) = generate_path_secrets st.tree leaf_sk path_secret_0 leaf_ind in
  let? pre_upd_path = path_secrets_to_pre_pathkem path_secrets in
  return ({
    path_secrets;
    commit_secret;
  }, pre_upd_path)

val finalize_create_commit_entropy_lengths:
  #bytes:Type0 -> {|crypto_bytes bytes|} -> #leaf_ind:nat ->
  st:treekem_state bytes leaf_ind -> list nat ->
  list nat
let finalize_create_commit_entropy_lengths #bytes #cb #leaf_ind st added_leaves =
  assume(treekem_invariant (un_add st.tree added_leaves));
  let path_secrets = generate_forgotten_path_secrets st.tree leaf_ind in
  encrypt_path_secrets_entropy_lengths (un_add st.tree added_leaves) path_secrets

type create_commit_result (#bytes:Type0) {|crypto_bytes bytes|} (#leaf_ind:nat) (st:treekem_state bytes leaf_ind) = {
  new_state: treekem_state bytes leaf_ind;
  update_path: update_path:pathkem bytes st.levels 0 leaf_ind{pathkem_filtering_ok st.tree update_path};
  commit_secret: bytes;
  added_leaves_path_secrets: list bytes;
}

val finalize_create_commit:
  #bytes:Type0 -> {|crypto_bytes bytes|} -> #leaf_ind:nat ->
  #st:treekem_state bytes leaf_ind ->
  pending_commit st ->
  added_leaves:list nat -> group_context_nt bytes ->
  randomness bytes (finalize_create_commit_entropy_lengths st added_leaves) ->
  result (create_commit_result st)
let finalize_create_commit #bytes #cb #leaf_ind #st pending added_leaves group_context randomness =
  assume(treekem_invariant (un_add st.tree added_leaves));
  let? (update_path, new_priv) = encrypt_path_secrets (un_add st.tree added_leaves) pending.path_secrets group_context randomness in
  let? added_leaves_path_secrets = get_path_secret_of_added_leaves pending.path_secrets added_leaves in
  let new_tree = tree_apply_path st.tree update_path in
  assume(pathkem_filtering_ok st.tree update_path);
  assume(treekem_invariant new_tree);
  assume(treekem_state_invariant new_tree new_priv);
  return ({
    new_state = { st with
      tree = new_tree;
      priv = new_priv;
    };
    update_path;
    commit_secret = pending.commit_secret;
    added_leaves_path_secrets;
  })
