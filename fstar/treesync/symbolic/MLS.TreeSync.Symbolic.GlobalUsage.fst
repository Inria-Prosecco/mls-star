module MLS.TreeSync.Symbolic.GlobalUsage

open FStar.Tactics
open LabeledCryptoAPI
open LabeledRuntimeAPI
open MLS.Crypto
open MLS.TreeSync.NetworkTypes
open MLS.Symbolic
open MLS.Symbolic.Session
open MLS.Symbolic.MapSession
open MLS.TreeSync.Symbolic.LeafNodeSignature
open MLS.TreeSync.Symbolic.AuthServiceCache
open MLS.TreeSync.Symbolic.API.Sessions
open MLS.TreeSync.Symbolic.API.GroupManager
open MLS.TreeSync.Symbolic.API.KeyPackageManager

#set-options "--fuel 0 --ifuel 0"

(*** Predicate definition ***)

val treesync_key_usages: key_usages
let treesync_key_usages = {
  dh_shared_secret_usage = (fun _ _ _ -> None);
  dh_unknown_peer_usage = (fun _ _ -> None);
  dh_usage_commutes_lemma = (fun () -> ());
  dh_unknown_peer_usage_lemma = (fun () -> ());
  kdf_extend_label = (fun _ _ _ _ _ -> None);
  kdf_extract_usage = (fun _ _ _ -> None);
  kdf_expand_usage = (fun _ _ _ -> None);
}

val can_sign_list: treekem_types dy_bytes -> list (valid_label & sign_pred)
let can_sign_list tkt = [
  (leaf_node_label, leaf_node_spred treesync_key_usages tkt);
]

val treesync_usage_preds: treekem_types dy_bytes -> usage_preds
let treesync_usage_preds tkt = {
  can_pke_encrypt = (fun _ _ _ _ -> False);
  can_aead_encrypt = (fun _ _ _ _ _ -> False);
  can_sign = mk_can_sign (can_sign_list tkt);
  can_mac = (fun _ _ _ _ -> False);
}

val treesync_global_usage: treekem_types dy_bytes -> global_usage
let treesync_global_usage tkt = {
  usage_preds = treesync_usage_preds tkt;
  key_usages = treesync_key_usages;
}

val session_pred_list: tkt:treekem_types dy_bytes -> list (string & session_pred)
let session_pred_list tkt = [
  (as_cache_label, map_session_invariant as_cache_types as_cache_pred);
  (group_manager_label, map_session_invariant group_manager_types group_manager_pred);
  (key_package_manager_label, map_session_invariant (key_package_manager_types tkt) (key_package_manager_pred tkt));
  (treesync_public_state_label, treesync_public_state_pred tkt);
  (treesync_private_state_label, treesync_private_state_pred);
]

val treesync_trace_preds: tkt:treekem_types dy_bytes -> trace_preds (treesync_global_usage tkt)
let treesync_trace_preds tkt = {
  can_trigger_event = (fun time prin e -> True);
  session_st_inv = mk_global_session_pred (session_pred_list tkt) (treesync_global_usage tkt);
  session_st_inv_lemma = (fun time prin si vi st -> (
    FStar.Classical.move_requires (mk_global_session_pred_is_msg (session_pred_list tkt) (treesync_global_usage tkt) time prin si vi) st
  ));
  session_st_inv_later = (fun time0 time1 prin si vi st ->
    FStar.Classical.move_requires (mk_global_session_pred_later (session_pred_list tkt) (treesync_global_usage tkt) time0 time1 prin si vi) st
  );
}

val treesync_preds: treekem_types dy_bytes -> preds
let treesync_preds tkt = {
  global_usage = treesync_global_usage tkt;
  trace_preds = treesync_trace_preds tkt;
}

(*** Proofs ***)

// This tactic is useful because `assert_norm` gets completely lost and eat all the RAM
inline_for_extraction noextract
val sign_memP_tactic: unit -> Tac unit
let sign_memP_tactic () =
  norm [delta_only [`%List.Tot.Base.memP; `%can_sign_list]; iota; zeta]

val treesync_global_usage_has_leaf_node_tbs_invariant: tkt:treekem_types dy_bytes -> Lemma
  (has_leaf_node_tbs_invariant tkt (treesync_global_usage tkt))
  [SMTPat (has_leaf_node_tbs_invariant tkt (treesync_global_usage tkt))]
let treesync_global_usage_has_leaf_node_tbs_invariant tkt =
  assert_norm(List.Tot.no_repeats_p (List.Tot.map fst (can_sign_list tkt)));
  assert(List.Tot.memP (leaf_node_label, (leaf_node_spred treesync_key_usages tkt)) (can_sign_list tkt)) by (sign_memP_tactic());
  mk_can_sign_correct (treesync_global_usage tkt) (can_sign_list tkt) leaf_node_label (leaf_node_spred treesync_key_usages tkt)

inline_for_extraction noextract
val session_memP_tactic: unit -> Tac unit
let session_memP_tactic () =
  norm [delta_only [`%List.Tot.Base.memP; `%session_pred_list]; iota; zeta]

val treesync_preds_has_as_cache_invariant: tkt:treekem_types dy_bytes -> Lemma
  (has_as_cache_invariant (treesync_preds tkt))
  [SMTPat (has_as_cache_invariant (treesync_preds tkt))]
let treesync_preds_has_as_cache_invariant tkt =
  let lab = as_cache_label in
  let spred = (map_session_invariant as_cache_types as_cache_pred) in
  assert_norm(List.Tot.no_repeats_p (List.Tot.map fst (session_pred_list tkt)));
  assert(List.Tot.memP (lab, spred) (session_pred_list tkt)) by (session_memP_tactic());
  mk_global_session_pred_correct (treesync_preds tkt) (session_pred_list tkt) lab spred

val treesync_preds_has_group_manager_invariant: tkt:treekem_types dy_bytes -> Lemma
  (has_group_manager_invariant (treesync_preds tkt))
  [SMTPat (has_group_manager_invariant (treesync_preds tkt))]
let treesync_preds_has_group_manager_invariant tkt =
  let lab = group_manager_label in
  let spred = (map_session_invariant group_manager_types group_manager_pred) in
  assert_norm(List.Tot.no_repeats_p (List.Tot.map fst (session_pred_list tkt)));
  assert(List.Tot.memP (lab, spred) (session_pred_list tkt)) by (session_memP_tactic());
  mk_global_session_pred_correct (treesync_preds tkt) (session_pred_list tkt) lab spred

val treesync_preds_has_key_package_manager_invariant: tkt:treekem_types dy_bytes -> Lemma
  (has_key_package_manager_invariant tkt (treesync_preds tkt))
  [SMTPat (has_key_package_manager_invariant tkt (treesync_preds tkt))]
let treesync_preds_has_key_package_manager_invariant tkt =
  let lab = key_package_manager_label in
  let spred = (map_session_invariant (key_package_manager_types tkt) (key_package_manager_pred tkt)) in
  assert_norm(List.Tot.no_repeats_p (List.Tot.map fst (session_pred_list tkt)));
  assert(List.Tot.memP (lab, spred) (session_pred_list tkt)) by (session_memP_tactic());
  mk_global_session_pred_correct (treesync_preds tkt) (session_pred_list tkt) lab spred

val treesync_preds_has_treesync_public_state_invariant: tkt:treekem_types dy_bytes -> Lemma
  (has_treesync_public_state_invariant tkt (treesync_preds tkt))
  [SMTPat (has_treesync_public_state_invariant tkt (treesync_preds tkt))]
let treesync_preds_has_treesync_public_state_invariant tkt =
  let lab = treesync_public_state_label in
  let spred = treesync_public_state_pred tkt in
  assert_norm(List.Tot.no_repeats_p (List.Tot.map fst (session_pred_list tkt)));
  assert(List.Tot.memP (lab, spred) (session_pred_list tkt)) by (session_memP_tactic());
  mk_global_session_pred_correct (treesync_preds tkt) (session_pred_list tkt) lab spred

val treesync_preds_has_treesync_private_state_invariant: tkt:treekem_types dy_bytes -> Lemma
  (has_treesync_private_state_invariant (treesync_preds tkt))
  [SMTPat (has_treesync_private_state_invariant (treesync_preds tkt))]
let treesync_preds_has_treesync_private_state_invariant tkt =
  let lab = treesync_private_state_label in
  let spred = treesync_private_state_pred in
  assert_norm(List.Tot.no_repeats_p (List.Tot.map fst (session_pred_list tkt)));
  assert(List.Tot.memP (lab, spred) (session_pred_list tkt)) by (session_memP_tactic());
  mk_global_session_pred_correct (treesync_preds tkt) (session_pred_list tkt) lab spred
