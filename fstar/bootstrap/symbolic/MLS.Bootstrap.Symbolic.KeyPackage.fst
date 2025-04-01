module MLS.Bootstrap.Symbolic.KeyPackage

open Comparse
open DY.Core
open DY.Lib
open MLS.Symbolic
open MLS.Symbolic.Lemmas
open MLS.Symbolic.Labels.Big
open MLS.Symbolic.Labels.Event
open MLS.Symbolic.Labels.Guard
open MLS.Symbolic.Labels.Prop
open MLS.Crypto
open MLS.Bootstrap.Symbolic.State.InitKey
open MLS.Crypto.Derived.Symbolic.SignWithLabel
open MLS.TreeSync.NetworkTypes
open MLS.TreeSync.Symbolic.AuthService
open MLS.TreeSync.Symbolic.AuthService.CredentialInterpretation
open MLS.TreeSync.Symbolic.State.SignatureKey
open MLS.TreeKEM.NetworkTypes
open MLS.Bootstrap.NetworkTypes

#set-options "--fuel 0 --ifuel 0"

(*** KeyPackage signature ***)

val key_package_label: string
let key_package_label = "KeyPackageTBS"

#push-options "--ifuel 1"
val key_package_sign_pred:
  {|crypto_usages|} ->
  signwithlabel_crypto_pred
let key_package_sign_pred #cu = {
  pred = (fun tr sk_usg vk kp_tbs_bytes ->
    match (parse (key_package_tbs_nt bytes tkt) kp_tbs_bytes) with
    | None -> False
    | Some kp_tbs -> (
      exists prin.
        sk_usg == mk_mls_sigkey_usage prin /\
        bytes_well_formed tr kp_tbs.init_key /\
        get_hpke_sk_label tr kp_tbs.init_key == init_key_label prin kp_tbs.init_key /\
        kp_tbs.init_key `has_hpke_sk_usage tr` init_key_usage prin kp_tbs.leaf_node.data.content
    )
  );
  pred_later = (fun tr1 tr2 sk_usg vk kp_tbs_bytes ->
    parse_wf_lemma (key_package_tbs_nt bytes tkt) (bytes_well_formed tr1) kp_tbs_bytes
  );
}
#pop-options

val key_package_tbs_tag_and_invariant: {|crypto_usages|} -> (valid_label & signwithlabel_crypto_pred)
let key_package_tbs_tag_and_invariant #cu = (key_package_label, key_package_sign_pred)

val has_key_package_tbs_invariant:
  {|crypto_invariants|} ->
  prop
let has_key_package_tbs_invariant #ci =
  has_mls_signwithlabel_pred (key_package_tbs_tag_and_invariant)

(*** KeyPackage signature verification event ***)

[@@ with_bytes bytes]
type key_package_has_been_verified = {
  key_package: key_package_nt bytes tkt;
}

%splice [ps_key_package_has_been_verified] (gen_parser (`key_package_has_been_verified))

instance event_key_package_has_been_verified: event key_package_has_been_verified = {
  tag = "MLS.Bootstrap.KeyPackageHasBeenVerified";
  format = mk_parseable_serializeable ps_key_package_has_been_verified;
}

val key_package_has_been_verified_pred: {|crypto_invariants|} -> event_predicate key_package_has_been_verified
let key_package_has_been_verified_pred #cinvs =
  fun tr prin {key_package} ->
    key_package.tbs.leaf_node.data.source == LNS_key_package /\
    // preconditions of `bytes_invariant_verify_with_label`
    is_well_formed _ (bytes_invariant tr) key_package /\
    (exists as_token. (dy_asp tr).credential_ok (key_package.tbs.leaf_node.data.signature_key, key_package.tbs.leaf_node.data.credential) as_token) /\
    // verification succeeded
    verify_with_label #bytes key_package.tbs.leaf_node.data.signature_key key_package_label (serialize _ key_package.tbs) key_package.signature

val has_key_package_has_been_verified_invariant:
  {|protocol_invariants|} ->
  prop
let has_key_package_has_been_verified_invariant #invs =
  has_event_pred key_package_has_been_verified_pred

val key_package_has_been_verified_tag_and_invariant: {|crypto_invariants|} -> (string & compiled_event_predicate)
let key_package_has_been_verified_tag_and_invariant #cinvs =
  (event_key_package_has_been_verified.tag, compile_event_pred key_package_has_been_verified_pred)

val i_have_verified_key_package:
  trace -> principal -> key_package_nt bytes tkt ->
  prop
let i_have_verified_key_package tr me key_package =
  event_triggered tr me {key_package}

val i_have_verified_every_key_package:
  trace -> principal -> list (key_package_nt bytes tkt) ->
  prop
let i_have_verified_every_key_package tr me joiners =
  for_allP (i_have_verified_key_package tr me) joiners

val i_have_verified_every_key_package_later:
  tr1:trace -> tr2:trace -> me:principal -> joiners:list (key_package_nt bytes tkt) ->
  Lemma
  (requires
    i_have_verified_every_key_package tr1 me joiners /\
    tr1 <$ tr2
  )
  (ensures i_have_verified_every_key_package tr2 me joiners)
  [SMTPat (i_have_verified_every_key_package tr1 me joiners); SMTPat (tr1 <$ tr2)]
let i_have_verified_every_key_package_later tr1 tr2 me joiners =
  for_allP_eq (i_have_verified_key_package tr1 me) joiners;
  for_allP_eq (i_have_verified_key_package tr2 me) joiners

(*** All invariants ***)

val has_key_package_invariant:
  {|protocol_invariants|} ->
  prop
let has_key_package_invariant #invs =
  has_key_package_tbs_invariant /\
  has_key_package_has_been_verified_invariant


(*** KeyPackage label ***)

val principal_key_package_has_been_verified_label:
  key_package_nt bytes tkt -> principal ->
  label
let principal_key_package_has_been_verified_label key_package prin =
  event_triggered_label prin {key_package}

val key_package_has_been_verified_label:
  key_package_nt bytes tkt ->
  label
let key_package_has_been_verified_label key_package =
  big_join (principal_key_package_has_been_verified_label key_package)

val key_package_to_principal:
  key_package_nt bytes tkt ->
  option principal
let key_package_to_principal kp =
  credential_to_principal kp.tbs.leaf_node.data.credential

val key_package_to_init_label:
  key_package_nt bytes tkt ->
  label
let key_package_to_init_label kp =
  match key_package_to_principal kp with
  | None ->
    public
  | Some prin ->
    (guard (signature_key_label prin kp.tbs.leaf_node.data.signature_key) (key_package_has_been_verified_label kp))
    `join`
    (init_key_label prin kp.tbs.init_key)

val key_package_to_init_label_lemma:
  {|protocol_invariants|} ->
  tr:trace ->
  me:principal ->
  key_package:key_package_nt bytes tkt ->
  Lemma
  (requires
    i_have_verified_key_package tr me key_package /\
    trace_invariant tr /\
    has_key_package_invariant
  )
  (ensures
    key_package_to_init_label key_package `can_flow tr` (get_hpke_sk_label tr key_package.tbs.init_key) /\ (
      key_package.tbs.init_key `has_hpke_sk_usage tr` init_key_usage (Some?.v (key_package_to_principal key_package)) (key_package.tbs.leaf_node.data.content)
      \/
      key_package_to_init_label key_package `can_flow tr` public
    )
  )
let key_package_to_init_label_lemma #invs tr me key_package =
  let Some prin = key_package_to_principal key_package in
  is_corrupt_event_triggered_label tr me {key_package};
  big_join_flow_to_component tr (principal_key_package_has_been_verified_label key_package) me;
  guard_authentication_lemma tr (signature_key_label prin key_package.tbs.leaf_node.data.signature_key) (key_package_has_been_verified_label key_package)
    (fun tr_ev -> exists p. key_package_has_been_verified_pred tr_ev p {key_package})
    (fun tr_ev ->
      trace_invariant_before tr_ev tr
    )
    (fun tr_before_ev ->
      bytes_well_formed tr_before_ev key_package.tbs.init_key /\
      get_hpke_sk_label tr_before_ev key_package.tbs.init_key == init_key_label prin key_package.tbs.init_key /\
      key_package.tbs.init_key `has_hpke_sk_usage tr` init_key_usage (Some?.v (key_package_to_principal key_package)) (key_package.tbs.leaf_node.data.content)
    )
    (fun tr_before_ev ->
      serialize_wf_lemma _ (bytes_invariant tr_before_ev) key_package.tbs;
      bytes_invariant_verify_with_label key_package_sign_pred tr_before_ev prin key_package.tbs.leaf_node.data.signature_key key_package_label (serialize #bytes _ key_package.tbs) key_package.signature
    )

val key_package_to_init_label_is_corrupt:
  tr:trace ->
  me:principal ->
  key_package:key_package_nt bytes tkt ->
  Lemma
  (requires
    is_corrupt tr (key_package_to_init_label key_package) /\
    Some? (key_package_to_principal key_package) /\
    i_have_verified_key_package tr me key_package
  )
  (ensures (
    let Some prin = key_package_to_principal key_package in
    is_corrupt (prefix tr (find_event_triggered_at_timestamp tr me {key_package})) (signature_key_label prin key_package.tbs.leaf_node.data.signature_key)
    \/
    is_corrupt tr (init_key_label prin key_package.tbs.init_key)
  ))
let key_package_to_init_label_is_corrupt tr me key_package =
  let Some prin = key_package_to_principal key_package in
  introduce forall tr. (key_package_has_been_verified_label key_package) `can_flow tr` (principal_key_package_has_been_verified_label key_package me) with (
    big_join_flow_to_component tr (principal_key_package_has_been_verified_label key_package) me
  );
  guard_can_flow tr (signature_key_label prin key_package.tbs.leaf_node.data.signature_key) (signature_key_label prin key_package.tbs.leaf_node.data.signature_key) (principal_key_package_has_been_verified_label key_package me) (key_package_has_been_verified_label key_package);
  is_corrupt_guard_event tr (signature_key_label prin key_package.tbs.leaf_node.data.signature_key) me {key_package}

(*** Init key associated to leaf node ***)

val key_package_has_leaf_node:
  key_package_nt bytes tkt -> leaf_node_nt bytes tkt ->
  prop
let key_package_has_leaf_node kp ln =
  kp.tbs.leaf_node == ln

val init_key_associated_with_aux:
  leaf_node_nt bytes tkt -> key_package_nt bytes tkt ->
  label
let init_key_associated_with_aux ln kp =
  meet
    (meet
      (prop_to_label (key_package_has_leaf_node kp ln))
      (key_package_has_been_verified_label kp)
    )
    (key_package_to_init_label kp)

val init_key_associated_with:
  leaf_node_nt bytes tkt ->
  label
let init_key_associated_with ln =
  big_join (init_key_associated_with_aux ln)

val init_key_associated_with_lemma:
  {|protocol_invariants|} ->
  tr:trace ->
  me:principal ->
  key_package:key_package_nt bytes tkt ->
  Lemma
  (requires
    i_have_verified_key_package tr me key_package /\
    trace_invariant tr /\
    has_key_package_invariant
  )
  (ensures
    init_key_associated_with key_package.tbs.leaf_node `can_flow tr` (get_hpke_sk_label tr key_package.tbs.init_key) /\ (
      key_package.tbs.init_key `has_hpke_sk_usage tr` init_key_usage (Some?.v (key_package_to_principal key_package)) (key_package.tbs.leaf_node.data.content)
      \/
      init_key_associated_with key_package.tbs.leaf_node `can_flow tr` public
    )
  )
let init_key_associated_with_lemma #invs tr me key_package =
  big_join_flow_to_component tr (principal_key_package_has_been_verified_label key_package) me;
  big_join_flow_to_component tr (init_key_associated_with_aux key_package.tbs.leaf_node) key_package;
  prop_to_label_true (key_package_has_leaf_node key_package key_package.tbs.leaf_node);
  is_corrupt_event_triggered_label tr me {key_package};
  key_package_to_init_label_lemma tr me key_package

val init_key_associated_with_is_corrupt:
  tr:trace ->
  leaf_node:leaf_node_nt bytes tkt ->
  Lemma
  (requires
    is_corrupt tr (init_key_associated_with leaf_node)
  )
  (ensures
    exists (key_package:key_package_nt bytes tkt) prin.
      i_have_verified_key_package tr prin key_package /\
      key_package.tbs.leaf_node == leaf_node /\
      is_corrupt tr (key_package_to_init_label key_package)
  )
let init_key_associated_with_is_corrupt tr leaf_node =
  assert(exists (key_package:key_package_nt bytes tkt).
    is_corrupt tr ((prop_to_label (key_package_has_leaf_node key_package leaf_node))) /\
    is_corrupt tr ((key_package_has_been_verified_label key_package)) /\
    is_corrupt tr (key_package_to_init_label key_package)
  );
  assert(exists (key_package:key_package_nt bytes tkt).
    key_package.tbs.leaf_node == leaf_node /\
    (exists prin. i_have_verified_key_package tr prin key_package) /\
    is_corrupt tr (key_package_to_init_label key_package)
  );
  ()
