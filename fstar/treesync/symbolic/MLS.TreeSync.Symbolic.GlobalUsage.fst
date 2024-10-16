module MLS.TreeSync.Symbolic.GlobalUsage

open Comparse
open DY.Core
open DY.Lib
open MLS.Crypto
open MLS.TreeSync.NetworkTypes
open MLS.Symbolic
open MLS.Crypto.Derived.Symbolic.SignWithLabel
open MLS.TreeSync.Symbolic.LeafNodeSignature
open MLS.TreeSync.Symbolic.AuthServiceCache
open MLS.TreeSync.Symbolic.API.Sessions
open MLS.TreeSync.Symbolic.API.GroupManager
open MLS.TreeSync.Symbolic.API.KeyPackageManager
open MLS.TreeSync.Symbolic.API

#set-options "--fuel 0 --ifuel 0"

(*** Predicate definition ***)

instance treesync_crypto_usages: crypto_usages =
  default_crypto_usages

val all_signwithlabel_preds: treekem_types dy_bytes -> list (valid_label & signwithlabel_crypto_pred)
let all_signwithlabel_preds tkt = [
  leaf_node_tbs_tag_and_invariant tkt;
]

val mls_sign_pred: treekem_types dy_bytes -> sign_crypto_predicate
let mls_sign_pred tkt =
  mk_mls_sign_pred (all_signwithlabel_preds tkt)

val all_sign_preds: treekem_types dy_bytes -> list (string & sign_crypto_predicate)
let all_sign_preds tkt = [
  ("MLS.LeafSignKey", mls_sign_pred tkt)
]

val treesync_crypto_predicates: treekem_types dy_bytes -> crypto_predicates
let treesync_crypto_predicates tkt = {
  default_crypto_predicates with
  sign_pred = mk_sign_predicate (all_sign_preds tkt);
}

instance treesync_crypto_invariants (tkt:treekem_types dy_bytes): crypto_invariants = {
  usages = treesync_crypto_usages;
  preds = treesync_crypto_predicates tkt;
}

val all_state_predicates: tkt:treekem_types dy_bytes -> list (dtuple2 string local_bytes_state_predicate)
let all_state_predicates tkt = [
  as_cache_tag_and_invariant;
  group_manager_tag_and_invariant;
  key_package_manager_tag_and_invariant tkt;
  treesync_public_state_tag_and_invariant tkt;
  treesync_private_state_tag_and_invariant;
]

val treesync_trace_invariants: tkt:treekem_types dy_bytes -> trace_invariants
let treesync_trace_invariants tkt = {
  state_pred = mk_state_pred (all_state_predicates tkt);
  event_pred = mk_event_pred [];
}

instance treesync_protocol_invariants (tkt:treekem_types dy_bytes): protocol_invariants = {
  crypto_invs = treesync_crypto_invariants tkt;
  trace_invs = treesync_trace_invariants tkt;
}

(*** Proofs ***)

#push-options "--ifuel 1 --fuel 1"
val all_signwithlabel_preds_has_all_signwithlabel_preds: tkt:treekem_types dy_bytes -> Lemma (norm [delta_only [`%all_signwithlabel_preds; `%for_allP]; iota; zeta] (for_allP (has_signwithlabel_pred (mls_sign_pred tkt)) (all_signwithlabel_preds tkt)))
let all_signwithlabel_preds_has_all_signwithlabel_preds tkt =
  assert_norm(List.Tot.no_repeats_p (List.Tot.map fst (all_signwithlabel_preds tkt)));
  mk_mls_sign_pred_correct (mls_sign_pred tkt) (all_signwithlabel_preds tkt);
  norm_spec [delta_only [`%all_signwithlabel_preds; `%for_allP]; iota; zeta] (for_allP (has_signwithlabel_pred (mls_sign_pred tkt)) (all_signwithlabel_preds tkt))
#pop-options

#push-options "--ifuel 1 --fuel 1"
val all_sign_preds_has_all_sign_preds: tkt:treekem_types dy_bytes -> Lemma (norm [delta_only [`%all_sign_preds; `%for_allP]; iota; zeta] (for_allP has_sign_predicate (all_sign_preds tkt)))
let all_sign_preds_has_all_sign_preds tkt =
  assert_norm(List.Tot.no_repeats_p (List.Tot.map fst (all_sign_preds tkt)));
  mk_sign_predicate_correct (all_sign_preds tkt);
  norm_spec [delta_only [`%all_sign_preds; `%for_allP]; iota; zeta] (for_allP has_sign_predicate (all_sign_preds tkt))
#pop-options

val all_state_predicates_has_all_state_predicates: tkt:treekem_types dy_bytes -> Lemma (norm [delta_only [`%all_state_predicates; `%for_allP]; iota; zeta] (for_allP has_local_bytes_state_predicate (all_state_predicates tkt)))
let all_state_predicates_has_all_state_predicates tkt =
  assert_norm(List.Tot.no_repeats_p (List.Tot.map dfst (all_state_predicates tkt)));
  mk_state_pred_correct (all_state_predicates tkt);
  norm_spec [delta_only [`%all_state_predicates; `%for_allP]; iota; zeta] (for_allP has_local_bytes_state_predicate (all_state_predicates tkt))

val treesync_protocol_invariants_has_has_treesync_invariants: tkt:treekem_types dy_bytes -> Lemma
  (has_treesync_invariants tkt)
  [SMTPat (has_treesync_invariants tkt)]
let treesync_protocol_invariants_has_has_treesync_invariants tkt =
  all_signwithlabel_preds_has_all_signwithlabel_preds tkt;
  all_sign_preds_has_all_sign_preds tkt;
  all_state_predicates_has_all_state_predicates tkt
