module MLS.TreeKEM.Symbolic.Traceful.ProtocolInvariants

open Comparse
open DY.Core
open DY.Lib
open MLS.TreeKEM.NetworkTypes
open MLS.TreeSync.Symbolic.API
open MLS.Crypto
open MLS.Crypto.Derived.Symbolic.EncryptWithLabel
open MLS.Crypto.Derived.Symbolic.ExpandWithLabel
open MLS.Crypto.Derived.Symbolic.SignWithLabel
open MLS.Bootstrap.Symbolic.State.InitKey
open MLS.Bootstrap.Symbolic.KeyPackage
open MLS.Bootstrap.Symbolic.GroupInfo
open MLS.Bootstrap.Symbolic.State.KeyPackageStore
open MLS.Bootstrap.Symbolic.Welcome
open MLS.TreeSync.Symbolic.LeafNodeSignature
open MLS.TreeSync.Symbolic.Event.LeafNodeHasBeenVerified
open MLS.TreeSync.Symbolic.State.Tree
open MLS.TreeSync.Symbolic.State.SignatureKey
open MLS.TreeSync.Symbolic.State.GroupManager
open MLS.TreeSync.Symbolic.State.KeyPackageManager
open MLS.TreeSync.Symbolic.State.AuthServiceCache
open MLS.TreeKEM.Symbolic.State.EpochSecrets
open MLS.TreeKEM.Symbolic.State.NodeKey
open MLS.TreeKEM.Symbolic.State.ProposalCache
open MLS.TreeKEM.Symbolic.State.UpdateCache
open MLS.TreeKEM.Symbolic.State.API
open MLS.TreeKEM.Symbolic.Tree.Labels
open MLS.TreeKEM.Symbolic.Tree.Operations
open MLS.TreeKEM.Symbolic.EpochEvent
open MLS.TreeKEM.Symbolic.KeySchedule
open MLS.TreeKEM.Symbolic.PSK
open MLS.TreeKEM.Symbolic.State.PSKStore
open MLS.TreeKEM.Symbolic.State.OnePSKStore
open MLS.TreeKEM.Symbolic.Traceful.AllInvariants

#set-options "--fuel 0 --ifuel 0"

let all_extractedkey_kdf_expand_usage: list (valid_label & expandwithlabel_crypto_usage) = [
    ("derived psk", expand_usage_extractedkey_derivedpsk);
    ("epoch", expand_usage_extractedkey_epoch);
    ("joiner", expand_usage_extractedkey_joiner);
    ("welcome", expand_usage_extractedkey_welcome);
]

let all_welcome_kdf_expand_usage: list (valid_label & expandwithlabel_crypto_usage) = [
  ("key", expand_usage_welcome_key);
  ("nonce", expand_usage_welcome_nonce);
]

let all_path_kdf_expand_usage: list (valid_label & expandwithlabel_crypto_usage) = [
  ("node", expand_usage_path_secret_node);
  ("path", expand_usage_path_secret_path);
]

let all_epoch_kdf_expand_usage: list (valid_label & expandwithlabel_crypto_usage) = [
  ("authentication", expand_usage_epoch_authentication);
  ("confirm", expand_usage_epoch_confirmation);
  ("encryption", expand_usage_epoch_encryption);
  ("exporter", expand_usage_epoch_exporter);
  ("external", expand_usage_epoch_external);
  ("init", expand_usage_epoch_init);
  ("membership", expand_usage_epoch_membership);
  ("resumption", expand_usage_epoch_resumption);
  ("sender data", expand_usage_epoch_senderdata);
]

let extractedkey_kdf_expand_usage = mk_kdf_expand_mls_usage all_extractedkey_kdf_expand_usage
let welcome_kdf_expand_usage = mk_kdf_expand_mls_usage all_welcome_kdf_expand_usage
let path_kdf_expand_usage = mk_kdf_expand_mls_usage all_path_kdf_expand_usage
let epoch_kdf_expand_usage = mk_kdf_expand_mls_usage all_epoch_kdf_expand_usage

let all_kdf_expand_usage: list (string & kdf_expand_crypto_usage) = [
  hpke_kdf_expand_tag_and_usage;
  ("MLS.TreeKEM.ConfirmationKey", expand_usage_confirmation_tag);
  ("KDF.ExtractedKey", extractedkey_kdf_expand_usage);
  ("MLS.Bootstrap.WelcomeSecret", welcome_kdf_expand_usage);
  ("MLS.PathSecret", path_kdf_expand_usage);
  ("MLS.TreeKEM.EpochSecret", epoch_kdf_expand_usage);
]

instance treesync_treekem_crypto_usages: crypto_usages = {
  default_crypto_usages with
  kdf_expand_usage = mk_kdf_expand_usage all_kdf_expand_usage;
}

let all_init_hpke_pred: list (valid_label & encryptwithlabel_crypto_pred) = [
  ("Welcome", mls_hpke_welcome_pred)
]

let all_node_hpke_pred : list (valid_label & encryptwithlabel_crypto_pred) = [
  ("UpdatePathNode", mls_hpke_updatepathnode_pred)
]

let init_hpke_pred = mk_hpke_mls_pred all_init_hpke_pred
let node_hpke_pred = mk_hpke_mls_pred all_node_hpke_pred

let all_hpke_pred: list (string & hpke_crypto_predicate) = [
  ("MLS.InitHpkeKey", init_hpke_pred);
  ("MLS.NodeHpkeKey", node_hpke_pred);
]

instance hpke_pred = { hpke_pred = mk_hpke_predicate all_hpke_pred }

let all_aead_pred: list (string & aead_crypto_predicate) = [
  hpke_aead_tag_and_pred;
  ("MLS.Bootstrap.WelcomeKey", aead_group_info_pred);
]

let all_leafnode_signature_pred: list (valid_label & signwithlabel_crypto_pred) = [
  group_info_tbs_tag_and_invariant;
  key_package_tbs_tag_and_invariant;
  leaf_node_tbs_tag_and_invariant tkt;
]

let leafnode_signature_pred = mk_mls_sign_pred all_leafnode_signature_pred

let all_sign_pred: list (string & sign_crypto_predicate) = [
  ("MLS.LeafSignKey", leafnode_signature_pred);
]

let all_mac_pred: list (string & mac_crypto_predicate) = [
  ("MLS.TreeKEM.ConfirmationKey", confirmation_mac_pred);
]

let treesync_treekem_crypto_predicates = {
  default_crypto_predicates with
  aead_pred = mk_aead_predicate all_aead_pred;
  sign_pred = mk_sign_predicate all_sign_pred;
  mac_pred = mk_mac_predicate all_mac_pred;
}

instance treesync_treekem_crypto_invariants = {
  usages = treesync_treekem_crypto_usages;
  preds = treesync_treekem_crypto_predicates;
}

let all_local_state_pred: list (dtuple2 string local_bytes_state_predicate) = [
  treesync_public_state_tag_and_invariant tkt;
  bootstrap_init_key_state_tag_and_invariant;
  bootstrap_key_package_store_state_tag_and_invariant;
  treekem_epoch_secret_state_tag_and_invariant;
  treekem_node_keys_state_tag_and_invariant;
  treesync_signature_key_state_tag_and_invariant;
  treesync_treekem_state_tag_and_invariant;
  key_package_manager_tag_and_invariant tkt;
  as_cache_tag_and_invariant;
  group_manager_tag_and_invariant;
  proposal_cache_tag_and_invariant;
  update_cache_tag_and_invariant;
  one_psk_state_tag_and_invariant;
  psk_store_tag_and_invariant;
]

let all_event_pred: list (string & compiled_event_predicate) = [
  leaf_node_has_been_verified_tag_and_invariant tkt;
  group_has_tree_event_tag_and_invariant;
  i_am_in_group_tag_and_invariant;
  key_package_has_been_verified_tag_and_invariant;
  leaf_node_signed_event_tag_and_invariant;
]

let treesync_treekem_trace_invariants = {
  state_pred = mk_state_pred all_local_state_pred;
  event_pred = mk_event_pred all_event_pred;
}

instance treesync_treekem_protocol_invariants: protocol_invariants = {
  crypto_invs = treesync_treekem_crypto_invariants;
  trace_invs = treesync_treekem_trace_invariants;
}

val extractedkey_kdf_expand_usage_correct: unit -> Lemma (norm [delta_only [`%all_extractedkey_kdf_expand_usage; `%for_allP]; iota; zeta] (for_allP (has_expandwithlabel_usage extractedkey_kdf_expand_usage) all_extractedkey_kdf_expand_usage))
let extractedkey_kdf_expand_usage_correct () =
  assert_norm(List.Tot.no_repeats_p (List.Tot.map fst (all_extractedkey_kdf_expand_usage)));
  mk_kdf_expand_mls_usage_correct extractedkey_kdf_expand_usage all_extractedkey_kdf_expand_usage;
  norm_spec [delta_only [`%all_extractedkey_kdf_expand_usage; `%for_allP]; iota; zeta] (for_allP (has_expandwithlabel_usage extractedkey_kdf_expand_usage) all_extractedkey_kdf_expand_usage)

val welcome_kdf_expand_usage_correct: unit -> Lemma (norm [delta_only [`%all_welcome_kdf_expand_usage; `%for_allP]; iota; zeta] (for_allP (has_expandwithlabel_usage welcome_kdf_expand_usage) all_welcome_kdf_expand_usage))
let welcome_kdf_expand_usage_correct () =
  assert_norm(List.Tot.no_repeats_p (List.Tot.map fst (all_welcome_kdf_expand_usage)));
  mk_kdf_expand_mls_usage_correct welcome_kdf_expand_usage all_welcome_kdf_expand_usage;
  norm_spec [delta_only [`%all_welcome_kdf_expand_usage; `%for_allP]; iota; zeta] (for_allP (has_expandwithlabel_usage welcome_kdf_expand_usage) all_welcome_kdf_expand_usage)

val path_kdf_expand_usage_correct: unit -> Lemma (norm [delta_only [`%all_path_kdf_expand_usage; `%for_allP]; iota; zeta] (for_allP (has_expandwithlabel_usage path_kdf_expand_usage) all_path_kdf_expand_usage))
let path_kdf_expand_usage_correct () =
  assert_norm(List.Tot.no_repeats_p (List.Tot.map fst (all_path_kdf_expand_usage)));
  mk_kdf_expand_mls_usage_correct path_kdf_expand_usage all_path_kdf_expand_usage;
  norm_spec [delta_only [`%all_path_kdf_expand_usage; `%for_allP]; iota; zeta] (for_allP (has_expandwithlabel_usage path_kdf_expand_usage) all_path_kdf_expand_usage)

val epoch_kdf_expand_usage_correct: unit -> Lemma (norm [delta_only [`%all_epoch_kdf_expand_usage; `%for_allP]; iota; zeta] (for_allP (has_expandwithlabel_usage epoch_kdf_expand_usage) all_epoch_kdf_expand_usage))
let epoch_kdf_expand_usage_correct () =
  assert_norm(List.Tot.no_repeats_p (List.Tot.map fst (all_epoch_kdf_expand_usage)));
  mk_kdf_expand_mls_usage_correct epoch_kdf_expand_usage all_epoch_kdf_expand_usage;
  norm_spec [delta_only [`%all_epoch_kdf_expand_usage; `%for_allP]; iota; zeta] (for_allP (has_expandwithlabel_usage epoch_kdf_expand_usage) all_epoch_kdf_expand_usage)

val treesync_treekem_kdf_expand_usage_correct: unit -> Lemma (norm [delta_only [`%all_kdf_expand_usage; `%for_allP]; iota; zeta] (for_allP has_kdf_expand_usage all_kdf_expand_usage))
let treesync_treekem_kdf_expand_usage_correct () =
  assert_norm(List.Tot.no_repeats_p (List.Tot.map fst (all_kdf_expand_usage)));
  mk_kdf_expand_usage_correct all_kdf_expand_usage;
  norm_spec [delta_only [`%all_kdf_expand_usage; `%for_allP]; iota; zeta] (for_allP has_kdf_expand_usage all_kdf_expand_usage)

#push-options "--fuel 1 --ifuel 1"
val init_hpke_pred_correct: unit -> Lemma (norm [delta_only [`%all_init_hpke_pred; `%for_allP]; iota; zeta] (for_allP (has_encryptwithlabel_pred init_hpke_pred) all_init_hpke_pred))
let init_hpke_pred_correct () =
  assert_norm(List.Tot.no_repeats_p (List.Tot.map fst (all_init_hpke_pred)));
  mk_hpke_mls_pred_correct init_hpke_pred all_init_hpke_pred;
  norm_spec [delta_only [`%all_init_hpke_pred; `%for_allP]; iota; zeta] (for_allP (has_encryptwithlabel_pred init_hpke_pred) all_init_hpke_pred)
#pop-options

#push-options "--fuel 1 --ifuel 1"
val node_hpke_pred_correct: unit -> Lemma (norm [delta_only [`%all_node_hpke_pred; `%for_allP]; iota; zeta] (for_allP (has_encryptwithlabel_pred node_hpke_pred) all_node_hpke_pred))
let node_hpke_pred_correct () =
  assert_norm(List.Tot.no_repeats_p (List.Tot.map fst (all_node_hpke_pred)));
  mk_hpke_mls_pred_correct node_hpke_pred all_node_hpke_pred;
  norm_spec [delta_only [`%all_node_hpke_pred; `%for_allP]; iota; zeta] (for_allP (has_encryptwithlabel_pred node_hpke_pred) all_node_hpke_pred)
#pop-options

val hpke_pred_correct: unit -> Lemma (norm [delta_only [`%all_hpke_pred; `%for_allP]; iota; zeta] (for_allP has_hpke_predicate all_hpke_pred))
let hpke_pred_correct () =
  assert_norm(List.Tot.no_repeats_p (List.Tot.map fst (all_hpke_pred)));
  mk_hpke_predicate_correct all_hpke_pred;
  norm_spec [delta_only [`%all_hpke_pred; `%for_allP]; iota; zeta] (for_allP has_hpke_predicate all_hpke_pred)

val leafnode_signature_pred_correct: unit -> Lemma (norm [delta_only [`%all_leafnode_signature_pred; `%for_allP]; iota; zeta] (for_allP (has_signwithlabel_pred leafnode_signature_pred) all_leafnode_signature_pred))
let leafnode_signature_pred_correct () =
  assert_norm(List.Tot.no_repeats_p (List.Tot.map fst (all_leafnode_signature_pred)));
  mk_mls_sign_pred_correct leafnode_signature_pred all_leafnode_signature_pred;
  norm_spec [delta_only [`%all_leafnode_signature_pred; `%for_allP]; iota; zeta] (for_allP (has_signwithlabel_pred leafnode_signature_pred) all_leafnode_signature_pred)

val treesync_treekem_aead_pred_correct: unit -> Lemma (norm [delta_only [`%all_aead_pred; `%for_allP]; iota; zeta] (for_allP has_aead_predicate all_aead_pred))
let treesync_treekem_aead_pred_correct () =
  assert_norm(List.Tot.no_repeats_p (List.Tot.map fst (all_aead_pred)));
  mk_aead_predicate_correct all_aead_pred;
  norm_spec [delta_only [`%all_aead_pred; `%for_allP]; iota; zeta] (for_allP has_aead_predicate all_aead_pred)

#push-options "--fuel 1 --ifuel 1"
val treesync_treekem_sign_pred_correct: unit -> Lemma (norm [delta_only [`%all_sign_pred; `%for_allP]; iota; zeta] (for_allP has_sign_predicate all_sign_pred))
let treesync_treekem_sign_pred_correct () =
  assert_norm(List.Tot.no_repeats_p (List.Tot.map fst (all_sign_pred)));
  mk_sign_predicate_correct all_sign_pred;
  norm_spec [delta_only [`%all_sign_pred; `%for_allP]; iota; zeta] (for_allP has_sign_predicate all_sign_pred)
#pop-options

#push-options "--fuel 1 --ifuel 1"
val treesync_treekem_mac_pred_correct: unit -> Lemma (norm [delta_only [`%all_mac_pred; `%for_allP]; iota; zeta] (for_allP has_mac_predicate all_mac_pred))
let treesync_treekem_mac_pred_correct () =
  assert_norm(List.Tot.no_repeats_p (List.Tot.map fst (all_mac_pred)));
  mk_mac_predicate_correct all_mac_pred;
  norm_spec [delta_only [`%all_mac_pred; `%for_allP]; iota; zeta] (for_allP has_mac_predicate all_mac_pred)
#pop-options

val treesync_treekem_state_pred_correct: unit -> Lemma (norm [delta_only [`%all_local_state_pred; `%for_allP]; iota; zeta] (for_allP (has_local_bytes_state_predicate) all_local_state_pred))
let treesync_treekem_state_pred_correct () =
  assert_norm(List.Tot.no_repeats_p (List.Tot.map dfst (all_local_state_pred)));
  mk_state_pred_correct all_local_state_pred;
  norm_spec [delta_only [`%all_local_state_pred; `%for_allP]; iota; zeta] (for_allP (has_local_bytes_state_predicate) all_local_state_pred)

val treesync_treekem_event_pred_correct: unit -> Lemma (norm [delta_only [`%all_event_pred; `%for_allP]; iota; zeta] (for_allP (has_compiled_event_pred) all_event_pred))
let treesync_treekem_event_pred_correct () =
  assert_norm(List.Tot.no_repeats_p (List.Tot.map fst (all_event_pred)));
  mk_event_pred_correct all_event_pred;
  norm_spec [delta_only [`%all_event_pred; `%for_allP]; iota; zeta] (for_allP (has_compiled_event_pred) all_event_pred)

val treesync_treekem_protocol_invariants_correct: unit -> Lemma (has_treesync_and_treekem_invariants)
let treesync_treekem_protocol_invariants_correct () =
  extractedkey_kdf_expand_usage_correct ();
  welcome_kdf_expand_usage_correct ();
  path_kdf_expand_usage_correct ();
  epoch_kdf_expand_usage_correct ();
  treesync_treekem_kdf_expand_usage_correct ();
  init_hpke_pred_correct ();
  node_hpke_pred_correct ();
  hpke_pred_correct ();
  leafnode_signature_pred_correct ();
  treesync_treekem_aead_pred_correct ();
  treesync_treekem_sign_pred_correct ();
  treesync_treekem_mac_pred_correct ();
  treesync_treekem_state_pred_correct ();
  treesync_treekem_event_pred_correct ()
