module MLS.TreeSync.Symbolic.GlobalUsage

open Comparse
open DY.Core
open DY.Lib
open MLS.Crypto
open MLS.TreeSync.NetworkTypes
open MLS.Symbolic
open MLS.TreeSync.Symbolic.LeafNodeSignature
open MLS.TreeSync.Symbolic.AuthServiceCache
open MLS.TreeSync.Symbolic.API.Sessions
open MLS.TreeSync.Symbolic.API.GroupManager
open MLS.TreeSync.Symbolic.API.KeyPackageManager

#set-options "--fuel 0 --ifuel 0"

(*** Predicate definition ***)

instance treesync_crypto_usages: crypto_usages =
  default_crypto_usages

val all_sign_preds: treekem_types dy_bytes -> list (valid_label & mls_sign_pred)
let all_sign_preds tkt = [
  leaf_node_tbs_tag_and_invariant tkt;
]

val treesync_crypto_predicates: treekem_types dy_bytes -> crypto_predicates treesync_crypto_usages
let treesync_crypto_predicates tkt = {
  default_crypto_predicates treesync_crypto_usages with
  sign_pred = {
    pred = mk_sign_pred (all_sign_preds tkt);
    pred_later = (fun tr1 tr2 vk msg ->
      mk_sign_pred_later (all_sign_preds tkt) tr1 tr2 vk msg
    );
  }
}

instance treesync_crypto_invariants (tkt:treekem_types dy_bytes): crypto_invariants = {
  usages = treesync_crypto_usages;
  preds = treesync_crypto_predicates tkt;
}

val all_state_predicates: tkt:treekem_types dy_bytes -> list (string & local_bytes_state_predicate)
let all_state_predicates tkt = [
  as_cache_tag_and_invariant;
  group_manager_tag_and_invariant;
  key_package_manager_tag_and_invariant tkt;
  treesync_public_state_tag_and_invariant tkt;
  treesync_private_state_tag_and_invariant;
]

val treesync_trace_invariants: tkt:treekem_types dy_bytes -> trace_invariants (treesync_crypto_invariants tkt)
let treesync_trace_invariants tkt = {
  state_pred = mk_state_pred (treesync_crypto_invariants tkt) (all_state_predicates tkt);
  event_pred = mk_event_pred [];
}

val treesync_protocol_invariants: treekem_types dy_bytes -> protocol_invariants
let treesync_protocol_invariants tkt = {
  crypto_invs = treesync_crypto_invariants tkt;
  trace_invs = treesync_trace_invariants tkt;
}

(*** Proofs ***)

val all_sign_preds_has_all_sign_preds: tkt:treekem_types dy_bytes -> Lemma (norm [delta_only [`%all_sign_preds; `%for_allP]; iota; zeta] (for_allP (has_sign_pred (treesync_crypto_invariants tkt)) (all_sign_preds tkt)))
let all_sign_preds_has_all_sign_preds tkt =
  assert_norm(List.Tot.no_repeats_p (List.Tot.map fst (all_sign_preds tkt)));
  mk_sign_pred_correct (treesync_crypto_invariants tkt) (all_sign_preds tkt);
  norm_spec [delta_only [`%all_sign_preds; `%for_allP]; iota; zeta] (for_allP (has_sign_pred (treesync_crypto_invariants tkt)) (all_sign_preds tkt));
  let dumb_lemma (x:prop) (y:prop): Lemma (requires x /\ x == y) (ensures y) = () in
  dumb_lemma (for_allP (has_sign_pred (treesync_crypto_invariants tkt)) (all_sign_preds tkt)) (norm [delta_only [`%all_sign_preds; `%for_allP]; iota; zeta] (for_allP (has_sign_pred (treesync_crypto_invariants tkt)) (all_sign_preds tkt)))

val treesync_global_usage_has_leaf_node_tbs_invariant: tkt:treekem_types dy_bytes -> Lemma
  (has_leaf_node_tbs_invariant tkt (treesync_crypto_invariants tkt))
  [SMTPat (has_leaf_node_tbs_invariant tkt (treesync_crypto_invariants tkt))]
let treesync_global_usage_has_leaf_node_tbs_invariant tkt =
  all_sign_preds_has_all_sign_preds tkt

val all_state_predicates_has_all_state_predicates: tkt:treekem_types dy_bytes -> Lemma (norm [delta_only [`%all_state_predicates; `%for_allP]; iota; zeta] (for_allP (has_local_bytes_state_predicate (treesync_protocol_invariants tkt)) (all_state_predicates tkt)))
let all_state_predicates_has_all_state_predicates tkt =
  assert_norm(List.Tot.no_repeats_p (List.Tot.map fst (all_state_predicates tkt)));
  mk_state_pred_correct (treesync_protocol_invariants tkt) (all_state_predicates tkt);
  norm_spec [delta_only [`%all_state_predicates; `%for_allP]; iota; zeta] (for_allP (has_local_bytes_state_predicate (treesync_protocol_invariants tkt)) (all_state_predicates tkt))

val treesync_protocol_invariants_has_as_cache_invariant: tkt:treekem_types dy_bytes -> Lemma
  (has_as_cache_invariant (treesync_protocol_invariants tkt))
  [SMTPat (has_as_cache_invariant (treesync_protocol_invariants tkt))]
let treesync_protocol_invariants_has_as_cache_invariant tkt =
  all_state_predicates_has_all_state_predicates tkt

val treesync_protocol_invariants_has_group_manager_invariant: tkt:treekem_types dy_bytes -> Lemma
  (has_group_manager_invariant (treesync_protocol_invariants tkt))
  [SMTPat (has_group_manager_invariant (treesync_protocol_invariants tkt))]
let treesync_protocol_invariants_has_group_manager_invariant tkt =
  all_state_predicates_has_all_state_predicates tkt

val treesync_protocol_invariants_has_key_package_manager_invariant: tkt:treekem_types dy_bytes -> Lemma
  (has_key_package_manager_invariant tkt (treesync_protocol_invariants tkt))
  [SMTPat (has_key_package_manager_invariant tkt (treesync_protocol_invariants tkt))]
let treesync_protocol_invariants_has_key_package_manager_invariant tkt =
  all_state_predicates_has_all_state_predicates tkt

val treesync_protocol_invariants_has_treesync_public_state_invariant: tkt:treekem_types dy_bytes -> Lemma
  (has_treesync_public_state_invariant tkt (treesync_protocol_invariants tkt))
  [SMTPat (has_treesync_public_state_invariant tkt (treesync_protocol_invariants tkt))]
let treesync_protocol_invariants_has_treesync_public_state_invariant tkt =
  all_state_predicates_has_all_state_predicates tkt

val treesync_protocol_invariants_has_treesync_private_state_invariant: tkt:treekem_types dy_bytes -> Lemma
  (has_treesync_private_state_invariant (treesync_protocol_invariants tkt))
  [SMTPat (has_treesync_private_state_invariant (treesync_protocol_invariants tkt))]
let treesync_protocol_invariants_has_treesync_private_state_invariant tkt =
  all_state_predicates_has_all_state_predicates tkt
