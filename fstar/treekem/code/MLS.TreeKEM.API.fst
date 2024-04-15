module MLS.TreeKEM.API

open Comparse
open MLS.Crypto
open MLS.NetworkTypes
open MLS.Tree
open MLS.NetworkBinder.Properties
open MLS.TreeKEM.Types
open MLS.TreeKEM.Invariants
open MLS.TreeKEM.API.KeySchedule.Types
//open MLS.TreeKEM.API.KeySchedule
open MLS.TreeKEM.API.Tree.Types
//open MLS.TreeKEM.API.Tree
open MLS.TreeKEM.API.Types
open MLS.Result

module T = MLS.TreeKEM.API.Tree
module KS = MLS.TreeKEM.API.KeySchedule

#set-options "--fuel 0 --ifuel 0"

(*** Create ***)

// TODO: enforce epoch_secret to be of size KDF.Nh?
val create:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  hpke_private_key bytes -> bytes ->
  bytes ->
  result (treekem_state bytes 0 & bytes)
let create #bytes #cb dec_key enc_key epoch_secret =
  let tree_state = T.create dec_key enc_key in
  let? (keyschedule_state, encryption_secret) = KS.create epoch_secret in
  return ({
    tree_state;
    keyschedule_state;
  }, encryption_secret)

(*** Welcome ***)

val welcome:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  #l:nat ->
  t:treekem bytes l 0{treekem_invariant t} -> hpke_private_key bytes -> option (bytes & nat) -> leaf_ind:nat{leaf_ind < pow2 l /\ Some? (leaf_at t leaf_ind)} ->
  bytes ->
  result (treekem_state bytes leaf_ind & bytes)
let welcome #bytes #cb #l t leaf_decryption_key opt_path_secret_and_inviter_ind leaf_ind epoch_secret =
  let? tree_state = T.welcome t leaf_decryption_key opt_path_secret_and_inviter_ind leaf_ind in
  let? (keyschedule_state, encryption_secret) = KS.create epoch_secret in
  return ({
    tree_state;
    keyschedule_state;
  }, encryption_secret)

(*** Add ***)

val add:
  #bytes:Type0 -> {|crypto_bytes bytes|} -> #leaf_ind:nat ->
  treekem_state bytes leaf_ind -> treekem_leaf bytes ->
  treekem_state bytes leaf_ind & nat
let add #bytes #cb #leaf_ind st kp =
  let (tree_state, i) = T.add st.tree_state kp in
  ({ st with tree_state }, i)

(*** Update ***)

val update:
  #bytes:Type0 -> {|crypto_bytes bytes|} -> #leaf_ind:nat ->
  st:treekem_state bytes leaf_ind -> treekem_leaf bytes -> treekem_index st ->
  treekem_state bytes leaf_ind
let update #bytes #cb #leaf_ind st lp i =
  { st with tree_state = T.update st.tree_state lp i }

(*** Remove ***)

val remove:
  #bytes:Type0 -> {|crypto_bytes bytes|} -> #leaf_ind:nat ->
  st:treekem_state bytes leaf_ind -> i:treekem_index st{i <> leaf_ind} ->
  treekem_state bytes leaf_ind
let remove #bytes #cb #leaf_ind st i =
  { st with tree_state = T.remove st.tree_state i }

(*** Process Commit ***)

type full_commit_args (#bytes:Type0) {|crypto_bytes bytes|} (#leaf_ind:nat) (st:treekem_tree_state bytes leaf_ind) = {
  commit_leaf_ind: commit_leaf_ind:MLS.TreeKEM.API.Tree.Types.treekem_index st{commit_leaf_ind <> leaf_ind};
  path: path:pathkem bytes st.levels 0 commit_leaf_ind{path_filtering_ok st.tree path};
  excluded_leaves: excluded_leaves:list nat{~(List.Tot.memP leaf_ind excluded_leaves)};
}

val commit:
  #bytes:Type0 -> {|crypto_bytes bytes|} -> #leaf_ind:nat ->
  st:treekem_state bytes leaf_ind -> option (full_commit_args st.tree_state) -> option bytes -> group_context_nt bytes -> group_context_nt bytes ->
  result (treekem_state bytes leaf_ind & bytes)
let commit #bytes #cb #leaf_ind st opt_full_commit_args opt_psk provisional_group_context new_group_context =
  let? (tree_state, opt_commit_secret) =
    match opt_full_commit_args with
    | None -> return (st.tree_state, None)
    | Some args ->
      let? (new_tree_state, commit_secret) = T.commit st.tree_state args.path args.excluded_leaves provisional_group_context in
      return (new_tree_state, Some commit_secret)
  in
  let? (keyschedule_state, encryption_secret, _) = KS.commit st.keyschedule_state opt_commit_secret opt_psk new_group_context in
  return ({
    tree_state;
    keyschedule_state;
  }, encryption_secret)

(*** Create Commit ***)

val prepare_create_commit_entropy_lengths:
  bytes:Type0 -> {|crypto_bytes bytes|} ->
  list nat
let prepare_create_commit_entropy_lengths bytes #cb =
  T.prepare_create_commit_entropy_lengths bytes

type pending_commit (#bytes:Type0) {|crypto_bytes bytes|} (#leaf_ind:nat) (st:treekem_state bytes leaf_ind) = {
  pend: MLS.TreeKEM.API.Tree.pending_commit st.tree_state;
}

val prepare_create_commit:
  #bytes:Type0 -> {|crypto_bytes bytes|} -> #leaf_ind:nat ->
  st:treekem_state bytes leaf_ind ->
  randomness bytes (prepare_create_commit_entropy_lengths bytes) ->
  result (pending_commit st & pre_pathkem bytes st.tree_state.levels 0 leaf_ind)
let prepare_create_commit #bytes #cb #leaf_ind st rand =
  let? (pend, path) = T.prepare_create_commit st.tree_state rand in
  return ({pend}, path)

val continue_create_commit_entropy_lengths:
  #bytes:Type0 -> {|crypto_bytes bytes|} -> #leaf_ind:nat ->
  st:treekem_state bytes leaf_ind -> list nat ->
  list nat
let continue_create_commit_entropy_lengths #bytes #cb #leaf_ind st added_leaves =
  T.finalize_create_commit_entropy_lengths st.tree_state added_leaves

type pending_commit_2 (bytes:Type0) {|crypto_bytes bytes|} (leaf_ind:nat) = {
  new_state: treekem_state bytes leaf_ind;
  commit_secret: bytes;
}

type continue_create_commit_result (#bytes:Type0) {|crypto_bytes bytes|} (#leaf_ind:nat) (st:treekem_state bytes leaf_ind) = {
  update_path: update_path:pathkem bytes st.tree_state.levels 0 leaf_ind{path_filtering_ok st.tree_state.tree update_path};
  added_leaves_path_secrets: list bytes;
}

val continue_create_commit:
  #bytes:Type0 -> {|crypto_bytes bytes|} -> #leaf_ind:nat ->
  #st:treekem_state bytes leaf_ind ->
  pending_commit st ->
  added_leaves:list nat -> group_context_nt bytes ->
  randomness bytes (continue_create_commit_entropy_lengths st added_leaves) ->
  result (pending_commit_2 bytes leaf_ind & continue_create_commit_result st)
let continue_create_commit #bytes #cb #leaf_ind #st pending added_leaves provisional_group_context randomness =
  let? tree_commit_result = T.finalize_create_commit #bytes pending.pend added_leaves provisional_group_context randomness in
  let new_state = { st with
    tree_state = tree_commit_result.new_state;
  } in
  return ({
    new_state;
    commit_secret = tree_commit_result.commit_secret;
  }, {
    update_path = tree_commit_result.update_path;
    added_leaves_path_secrets = tree_commit_result.added_leaves_path_secrets;
  })

type create_commit_result (bytes:Type0) {|crypto_bytes bytes|} (leaf_ind: nat) = {
  new_state: treekem_state bytes leaf_ind;
  encryption_secret: bytes;
  // secrets needed to generate welcomes
  welcome_secret: bytes;
  joiner_secret: bytes;
}

val finalize_create_commit:
  #bytes:Type0 -> {|crypto_bytes bytes|} -> #leaf_ind:nat ->
  pending_commit_2 bytes leaf_ind  ->
  group_context_nt bytes -> option bytes ->
  result (create_commit_result bytes leaf_ind)
let finalize_create_commit #bytes #cb #leaf_ind pending new_group_context opt_psk =
  let? (keyschedule_state, encryption_secret, additional_secrets) = KS.commit pending.new_state.keyschedule_state (Some pending.commit_secret) opt_psk new_group_context in
  return {
    new_state = {
      pending.new_state with
      keyschedule_state;
    };
    encryption_secret;
    welcome_secret = additional_secrets.welcome_secret;
    joiner_secret = additional_secrets.joiner_secret;
  }
