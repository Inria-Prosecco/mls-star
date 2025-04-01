module MLS.TreeKEM.API.Tree

open Comparse
open MLS.Result
open MLS.Crypto
open MLS.NetworkTypes
open MLS.Tree
open MLS.TreeCommon
open MLS.TreeCommon.Lemmas
open MLS.TreeKEM.Types
open MLS.TreeKEM.Operations
open MLS.TreeKEM.Invariants
open MLS.TreeKEM.Invariants.Proofs
open MLS.NetworkBinder.Properties
open MLS.TreeKEM.API.Tree.Types

(*** Create ***)

[@"opaque_to_smt"]
val create:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  hpke_private_key bytes -> bytes ->
  treekem_tree_state bytes 0
let create #bytes #cb dec_key enc_key =
  {
    levels = 0;
    tree = tree_create ({public_key = enc_key} <: treekem_leaf bytes);
    priv = PLeaf dec_key
  }

(*** Welcome ***)

[@"opaque_to_smt"]
val welcome:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  #l:nat ->
  t:treekem bytes l 0{treekem_invariant t} -> hpke_private_key bytes -> option (bytes & nat) -> leaf_ind:nat{leaf_ind < pow2 l /\ Some? (leaf_at t leaf_ind)} ->
  result (treekem_tree_state bytes leaf_ind)
let welcome #bytes #cb #l t leaf_decryption_key opt_path_secret_and_inviter_ind leaf_ind =
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
  return {
    levels = l;
    tree = t;
    priv;
  }

(*** Add ***)

[@"opaque_to_smt"]
val add:
  #bytes:Type0 -> {|crypto_bytes bytes|} -> #leaf_ind:nat ->
  treekem_tree_state bytes leaf_ind -> treekem_leaf bytes ->
  treekem_tree_state bytes leaf_ind & nat
let add #bytes #cb #leaf_ind st kp =
  match find_empty_leaf st.tree with
  | Some i -> (
    treekem_invariant_add st.tree i kp;
    treekem_priv_invariant_add st.tree st.priv i kp;
    ({ st with
      tree = tree_add st.tree i kp;
    }, (i <: nat))
  )
  | None -> (
    find_empty_leaf_tree_extend st.tree;
    let extended_tree = tree_extend st.tree in
    let i = Some?.v (find_empty_leaf extended_tree) in
    treekem_invariant_extend st.tree;
    treekem_priv_invariant_extend st.tree st.priv;
    treekem_invariant_add extended_tree i kp;
    treekem_priv_invariant_add extended_tree (path_extend st.priv) i kp;
    ({ st with
      levels = st.levels+1;
      tree = tree_add extended_tree i kp;
      priv = path_extend st.priv;
    }, (i <: nat))
  )

(*** Update ***)

[@"opaque_to_smt"]
val update_myself:
  #bytes:Type0 -> {|crypto_bytes bytes|} -> #leaf_ind:nat ->
  st:treekem_tree_state bytes leaf_ind -> treekem_leaf bytes -> hpke_private_key bytes ->
  treekem_tree_state bytes leaf_ind
let update_myself #bytes #cb #leaf_ind st lp leaf_decryption_key =
  treekem_invariant_update st.tree leaf_ind lp;
  treekem_priv_invariant_update st.tree st.priv leaf_ind lp;
  { st with
    tree = tree_update st.tree leaf_ind lp;
    priv = create_empty_priv leaf_decryption_key;
  }

[@"opaque_to_smt"]
val update_other:
  #bytes:Type0 -> {|crypto_bytes bytes|} -> #leaf_ind:nat ->
  st:treekem_tree_state bytes leaf_ind -> treekem_leaf bytes -> i:treekem_index st{i <> leaf_ind} ->
  treekem_tree_state bytes leaf_ind
let update_other #bytes #cb #leaf_ind st lp i =
  treekem_invariant_update st.tree i lp;
  treekem_priv_invariant_update st.tree st.priv i lp;
  { st with
    tree = tree_update st.tree i lp;
    priv = path_blank st.priv i;
  }

(*** Remove ***)

val truncate_one:
  #bytes:Type0 -> {|crypto_bytes bytes|} -> #leaf_ind:nat ->
  st:treekem_tree_state bytes leaf_ind{1 <= st.levels && is_tree_empty (TNode?.right st.tree)} ->
  res:treekem_tree_state bytes leaf_ind{res.levels == st.levels-1}
let truncate_one #bytes #cb #leaf_ind st =
  if leaf_ind >= pow2 (st.levels-1) then (
    MLS.TreeCommon.Lemmas.is_tree_empty_leaf_at (TNode?.right st.tree) leaf_ind;
    false_elim ()
  ) else (
    treekem_invariant_truncate st.tree;
    treekem_priv_invariant_truncate st.tree st.priv;
    {
      levels = st.levels-1;
      tree = tree_truncate st.tree;
      priv = path_truncate st.priv;
    }
  )

val fully_truncate:
  #bytes:Type0 -> {|crypto_bytes bytes|} -> #leaf_ind:nat ->
  st:treekem_tree_state bytes leaf_ind ->
  Tot (treekem_tree_state bytes leaf_ind)
  (decreases st.levels)
let rec fully_truncate #bytes #cb #leaf_ind st =
  if 1 <= st.levels && is_tree_empty (TNode?.right st.tree) then (
    fully_truncate (truncate_one st)
  ) else (
    st
  )

val remove_aux:
  #bytes:Type0 -> {|crypto_bytes bytes|} -> #leaf_ind:nat ->
  st:treekem_tree_state bytes leaf_ind -> i:treekem_index st{i <> leaf_ind} ->
  treekem_tree_state bytes leaf_ind
let remove_aux #bytes #cb #leaf_ind st i =
  treekem_invariant_remove st.tree i;
  treekem_priv_invariant_remove st.tree st.priv i;
  { st with
    tree = tree_remove st.tree i;
    priv = path_blank st.priv i;
  }

[@"opaque_to_smt"]
val remove:
  #bytes:Type0 -> {|crypto_bytes bytes|} -> #leaf_ind:nat ->
  st:treekem_tree_state bytes leaf_ind -> i:treekem_index st{i <> leaf_ind} ->
  treekem_tree_state bytes leaf_ind
let remove #bytes #cb #leaf_ind st i =
  fully_truncate (remove_aux st i)

(*** Process Commit ***)

[@"opaque_to_smt"]
val commit:
  #bytes:Type0 -> {|crypto_bytes bytes|} -> #leaf_ind:nat ->
  st:treekem_tree_state bytes leaf_ind -> #li:treekem_index st{li <> leaf_ind} -> p:pathkem bytes st.levels 0 li{path_filtering_ok st.tree p} -> excluded_leaves:list nat{~(List.Tot.memP leaf_ind excluded_leaves)} -> group_context_nt bytes ->
  result (treekem_tree_state bytes leaf_ind & bytes)
let commit #bytes #cb #leaf_ind st #li p excluded_leaves group_context =
  let un_added_tree = un_add st.tree excluded_leaves in
  treekem_invariant_un_add st.tree excluded_leaves;
  treekem_priv_invariant_un_add st.tree st.priv excluded_leaves;
  if not (check_update_path_ciphertexts_lengthes un_added_tree p) then (
    error "TreeKEM.commit: bad UpdatePath ciphertext lengths"
  ) else (
    weaken_path_filtering_ok st.tree p;
    path_filtering_weak_ok_un_add st.tree p excluded_leaves;
    let? (path_secret, least_common_ancestor_level) = get_path_secret un_added_tree st.priv p group_context in
    let new_tree = tree_apply_path st.tree p in
    let? (new_priv, root_secret) = path_apply_path new_tree st.priv path_secret least_common_ancestor_level in
    treekem_invariant_apply_path st.tree p;
    treekem_priv_invariant_apply_path st.tree st.priv p path_secret least_common_ancestor_level;
    return ({ st with
      tree = new_tree;
      priv = new_priv;
    }, root_secret)
  )

(*** Create Commit ***)

val prepare_create_commit_entropy_lengths:
  bytes:Type0 -> {|crypto_bytes bytes|} ->
  list nat
let prepare_create_commit_entropy_lengths bytes #cb =
  [hpke_private_key_length #bytes; kdf_length #bytes]

type pending_commit (#bytes:Type0) {|crypto_bytes bytes|} (#leaf_ind:nat) (st:treekem_tree_state bytes leaf_ind) = {
  path_secrets: path_secrets:path_secrets bytes st.levels 0 leaf_ind{path_filtering_ok st.tree path_secrets /\ forget_path_secrets path_secrets == generate_forgotten_path_secrets st.tree leaf_ind};
  commit_secret: bytes;
}

[@"opaque_to_smt"]
val prepare_create_commit:
  #bytes:Type0 -> {|crypto_bytes bytes|} -> #leaf_ind:nat ->
  st:treekem_tree_state bytes leaf_ind ->
  randomness bytes (prepare_create_commit_entropy_lengths bytes) ->
  result (pending_commit st & pre_pathkem bytes st.levels 0 leaf_ind)
let prepare_create_commit #bytes #cb #leaf_ind st rand =
  let leaf_sk, rand = dest_randomness rand in
  let path_secret_0, rand = dest_randomness rand in
  let? (path_secrets, commit_secret) = generate_path_secrets st.tree leaf_sk path_secret_0 leaf_ind in
  let? pre_upd_path = path_secrets_to_pre_pathkem path_secrets in
  path_filtering_ok_generate_path_secrets st.tree leaf_sk path_secret_0 leaf_ind;
  return ({
    path_secrets;
    commit_secret;
  }, pre_upd_path)

val finalize_create_commit_entropy_lengths:
  #bytes:Type0 -> {|crypto_bytes bytes|} -> #leaf_ind:nat ->
  st:treekem_tree_state bytes leaf_ind -> list nat ->
  list nat
let finalize_create_commit_entropy_lengths #bytes #cb #leaf_ind st added_leaves =
  treekem_invariant_un_add st.tree added_leaves;
  let path_secrets = generate_forgotten_path_secrets st.tree leaf_ind in
  encrypt_path_secrets_entropy_lengths (un_add st.tree added_leaves) path_secrets

type create_commit_result (#bytes:Type0) {|crypto_bytes bytes|} (#leaf_ind:nat) (st:treekem_tree_state bytes leaf_ind) = {
  new_state: treekem_tree_state bytes leaf_ind;
  update_path: update_path:pathkem bytes st.levels 0 leaf_ind{path_filtering_ok st.tree update_path};
  commit_secret: bytes;
  added_leaves_path_secrets: list bytes;
}

[@"opaque_to_smt"]
val finalize_create_commit:
  #bytes:Type0 -> {|crypto_bytes bytes|} -> #leaf_ind:nat ->
  #st:treekem_tree_state bytes leaf_ind ->
  pending_commit st ->
  added_leaves:list nat -> group_context_nt bytes ->
  randomness bytes (finalize_create_commit_entropy_lengths st added_leaves) ->
  result (create_commit_result st)
let finalize_create_commit #bytes #cb #leaf_ind #st pending added_leaves group_context randomness =
  treekem_invariant_un_add st.tree added_leaves;
  let? (update_path, new_priv) = encrypt_path_secrets (un_add st.tree added_leaves) pending.path_secrets group_context randomness in
  let? added_leaves_path_secrets = get_path_secret_of_added_leaves pending.path_secrets added_leaves in
  let new_tree = tree_apply_path st.tree update_path in
  path_filtering_ok_encrypt_path_secrets st.tree (un_add st.tree added_leaves) pending.path_secrets group_context randomness;
  treekem_invariant_apply_path st.tree update_path;
  treekem_priv_invariant_encrypt_path_secrets st.tree (un_add st.tree added_leaves) pending.path_secrets group_context randomness;
  return ({
    new_state = { st with
      tree = new_tree;
      priv = new_priv;
    };
    update_path;
    commit_secret = pending.commit_secret;
    added_leaves_path_secrets;
  })
