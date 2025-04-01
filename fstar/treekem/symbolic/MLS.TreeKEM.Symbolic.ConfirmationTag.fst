module MLS.TreeKEM.Symbolic.ConfirmationTag

open Comparse
open DY.Core
open MLS.Result
open MLS.Crypto
open MLS.NetworkTypes
open MLS.TreeKEM.NetworkTypes
open MLS.TreeKEM.KeySchedule
open MLS.TreeKEM.API.KeySchedule.Types
open MLS.TreeKEM.API.KeySchedule
open MLS.Symbolic
open MLS.TreeKEM.PSK
open MLS.TreeKEM.Symbolic.PSK

#set-options "--fuel 0 --ifuel 0"

(*** Strong version, from joiner secret to confirmation tag ***)

val compute_confirmation_tag_from_joiner_secret:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  bytes -> list (pre_shared_key_id_nt bytes & bytes) -> group_context_nt bytes ->
  result bytes
let compute_confirmation_tag_from_joiner_secret #bytes #cb joiner_secret psks group_context =
  let? epoch_secret = secret_joiner_to_epoch joiner_secret psks group_context in
  let? confirmation_key = secret_epoch_to_confirmation (epoch_secret <: bytes) in
  let? confirmation_tag = compute_confirmation_tag (confirmation_key <: bytes) group_context.confirmed_transcript_hash in
  return (confirmation_tag <: bytes)

val compute_confirmation_tag_from_joiner_secret_inj:
  joiner_secret1:bytes -> psks1:list (pre_shared_key_id_nt bytes & bytes) -> group_context1:group_context_nt bytes ->
  joiner_secret2:bytes -> psks2:list (pre_shared_key_id_nt bytes & bytes) -> group_context2:group_context_nt bytes ->
  Lemma (
    match compute_confirmation_tag_from_joiner_secret joiner_secret1 psks1 group_context1, compute_confirmation_tag_from_joiner_secret joiner_secret2 psks2 group_context2 with
    | Success confirmation_tag1, Success confirmation_tag2 -> (
      confirmation_tag1 == confirmation_tag2 ==> (
        joiner_secret1 == joiner_secret2 /\
        psks1 == psks2 /\
        group_context1 == group_context2
      )
    )
    | _, _ -> True
  )
let compute_confirmation_tag_from_joiner_secret_inj joiner_secret1 psks1 group_context1 joiner_secret2 psks2 group_context2 =
  match compute_confirmation_tag_from_joiner_secret joiner_secret1 psks1 group_context1, compute_confirmation_tag_from_joiner_secret joiner_secret2 psks2 group_context2 with
  | Success confirmation_tag1, Success confirmation_tag2 -> (
    if confirmation_tag1 <> confirmation_tag2 then ()
    else (
      // Not sure why F* needs the following
      let kdf_label1: kdf_label_nt bytes = {
        length = (kdf_length #bytes);
        label = get_mls_label "epoch";
        context = (serialize #bytes (group_context_nt bytes) group_context1);
      } in

      let Success psk_secret1 = compute_psk_secret psks1 in
      let Success epoch_secret1 = secret_joiner_to_epoch_internal joiner_secret1 psk_secret1 group_context1 in
      let Success confirmation_key1 = secret_epoch_to_confirmation (epoch_secret1 <: bytes) in
      let Success ct1 = compute_confirmation_tag (confirmation_key1 <: bytes) group_context1.confirmed_transcript_hash in
      let Success psk_secret2 = compute_psk_secret psks2 in
      let Success epoch_secret2 = secret_joiner_to_epoch_internal joiner_secret2 psk_secret2 group_context2 in
      let Success confirmation_key2 = secret_epoch_to_confirmation (epoch_secret2 <: bytes) in
      let Success ct2 = compute_confirmation_tag (confirmation_key2 <: bytes) group_context2.confirmed_transcript_hash in
      assert(ct1 == ct2);
      normalize_term_spec (hmac_hmac #bytes);
      assert(confirmation_key1 == confirmation_key2);
      normalize_term_spec (DY.Core.kdf_expand);
      normalize_term_spec (DY.Core.kdf_extract);
      assert(epoch_secret1 == epoch_secret2);
      assert(psk_secret1 == psk_secret2);
      compute_psk_secret_inj psks1 psks2;
      assert(psks1 == psks2);
      assert(joiner_secret1 == joiner_secret2);
      assert(group_context1 == group_context2);
      ()
    )
  )
  | _, _ -> ()

val treekem_keyschedule_state_auth_strong:
  treekem_keyschedule_state bytes ->
  bytes -> list (pre_shared_key_id_nt bytes & bytes) -> group_context_nt bytes ->
  prop
let treekem_keyschedule_state_auth_strong st joiner_secret psks group_context =
  Success st == (
    let? epoch_secret: bytes = secret_joiner_to_epoch joiner_secret psks group_context in
    let? (new_st, encryption_secret) = create_from_epoch_secret epoch_secret group_context in
    return new_st
  )

#push-options "--z3cliopt 'smt.qi.eager_threshold=100'"
val treekem_keyschedule_state_auth_strong_inj:
  st1:treekem_keyschedule_state bytes ->
  joiner_secret1:bytes -> psks1:list (pre_shared_key_id_nt bytes & bytes) -> group_context1:group_context_nt bytes ->
  st2:treekem_keyschedule_state bytes ->
  joiner_secret2:bytes -> psks2:list (pre_shared_key_id_nt bytes & bytes) -> group_context2:group_context_nt bytes ->
  Lemma
  (requires
    treekem_keyschedule_state_auth_strong st1 joiner_secret1 psks1 group_context1 /\
    treekem_keyschedule_state_auth_strong st2 joiner_secret2 psks2 group_context2 /\
    st1.epoch_keys.confirmation_tag == st2.epoch_keys.confirmation_tag
  )
  (ensures
    st1 == st2 /\
    psks1 == psks2
  )
let treekem_keyschedule_state_auth_strong_inj st1 joiner_secret1 psks1 group_context1 st2 joiner_secret2 psks2 group_context2 =
  reveal_opaque (`%create_from_epoch_secret) (create_from_epoch_secret #bytes);
  compute_confirmation_tag_from_joiner_secret_inj joiner_secret1 psks1 group_context1 joiner_secret2 psks2 group_context2
#pop-options

val treekem_keyschedule_state_auth_strong_exists:
  treekem_keyschedule_state bytes ->
  prop
let treekem_keyschedule_state_auth_strong_exists st =
  exists joiner_secret psks group_context.
    treekem_keyschedule_state_auth_strong st joiner_secret psks group_context

val treekem_keyschedule_state_auth_strong_exists_inj:
  st1:treekem_keyschedule_state bytes -> st2:treekem_keyschedule_state bytes ->
  Lemma
  (requires
    treekem_keyschedule_state_auth_strong_exists st1 /\
    treekem_keyschedule_state_auth_strong_exists st2 /\
    st1.epoch_keys.confirmation_tag == st2.epoch_keys.confirmation_tag
  )
  (ensures st1 == st2)
let treekem_keyschedule_state_auth_strong_exists_inj st1 st2 =
  eliminate exists joiner_secret1 psks1 group_context1 joiner_secret2 psks2 group_context2.
    treekem_keyschedule_state_auth_strong st1 joiner_secret1 psks1 group_context1 /\
    treekem_keyschedule_state_auth_strong st2 joiner_secret2 psks2 group_context2
  returns st1 == st2
  with _. (
    treekem_keyschedule_state_auth_strong_inj st1 joiner_secret1 psks1 group_context1 st2 joiner_secret2 psks2 group_context2
  )

(*** Weak version, from epoc secret ***)

val compute_confirmation_tag_from_epoch_secret:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  bytes -> group_context_nt bytes ->
  result bytes
let compute_confirmation_tag_from_epoch_secret #bytes #cb epoch_secret group_context =
  let? confirmation_key = secret_epoch_to_confirmation (epoch_secret <: bytes) in
  let? confirmation_tag = compute_confirmation_tag (confirmation_key <: bytes) group_context.confirmed_transcript_hash in
  return (confirmation_tag <: bytes)

val compute_confirmation_tag_from_epoch_secret_inj:
  epoch_secret1:bytes -> group_context1:group_context_nt bytes ->
  epoch_secret2:bytes -> group_context2:group_context_nt bytes ->
  Lemma (
    match compute_confirmation_tag_from_epoch_secret epoch_secret1 group_context1, compute_confirmation_tag_from_epoch_secret epoch_secret2 group_context2 with
    | Success confirmation_tag1, Success confirmation_tag2 -> (
      confirmation_tag1 == confirmation_tag2 ==> (
        epoch_secret1 == epoch_secret2
      )
    )
    | _, _ -> True
  )
let compute_confirmation_tag_from_epoch_secret_inj epoch_secret1 group_context1 epoch_secret2 group_context2 =
  match compute_confirmation_tag_from_epoch_secret epoch_secret1 group_context1, compute_confirmation_tag_from_epoch_secret epoch_secret2 group_context2 with
  | Success confirmation_tag1, Success confirmation_tag2 -> (
    if confirmation_tag1 <> confirmation_tag2 then ()
    else (
      let Success confirmation_key1 = secret_epoch_to_confirmation (epoch_secret1 <: bytes) in
      let Success ct1 = compute_confirmation_tag (confirmation_key1 <: bytes) group_context1.confirmed_transcript_hash in
      let Success confirmation_key2 = secret_epoch_to_confirmation (epoch_secret2 <: bytes) in
      let Success ct2 = compute_confirmation_tag (confirmation_key2 <: bytes) group_context2.confirmed_transcript_hash in
      assert(ct1 == ct2);
      normalize_term_spec (hmac_hmac #bytes);
      assert(confirmation_key1 == confirmation_key2);
      normalize_term_spec (DY.Core.kdf_expand)
    )
  )
  | _, _ -> ()

val treekem_keyschedule_state_auth_weak:
  treekem_keyschedule_state bytes ->
  bytes -> group_context_nt bytes ->
  prop
let treekem_keyschedule_state_auth_weak st epoch_secret group_context =
  Success st == (
    let? (new_st, encryption_secret) = create_from_epoch_secret epoch_secret group_context in
    return new_st
  )

#push-options "--z3cliopt 'smt.qi.eager_threshold=100'"
val treekem_keyschedule_state_auth_weak_inj:
  st1:treekem_keyschedule_state bytes ->
  epoch_secret1:bytes -> group_context1:group_context_nt bytes ->
  st2:treekem_keyschedule_state bytes ->
  epoch_secret2:bytes -> group_context2:group_context_nt bytes ->
  Lemma
  (requires
    treekem_keyschedule_state_auth_weak st1 epoch_secret1 group_context1 /\
    treekem_keyschedule_state_auth_weak st2 epoch_secret2 group_context2 /\
    st1.epoch_keys.confirmation_tag == st2.epoch_keys.confirmation_tag
  )
  (ensures
    st1 == st2
  )
let treekem_keyschedule_state_auth_weak_inj st1 epoch_secret1 group_context1 st2 epoch_secret2 group_context2 =
  reveal_opaque (`%create_from_epoch_secret) (create_from_epoch_secret #bytes);
  compute_confirmation_tag_from_epoch_secret_inj epoch_secret1 group_context1 epoch_secret2 group_context2
#pop-options

val treekem_keyschedule_state_auth_weak_exists:
  treekem_keyschedule_state bytes ->
  prop
let treekem_keyschedule_state_auth_weak_exists st =
  exists epoch_secret group_context.
    treekem_keyschedule_state_auth_weak st epoch_secret group_context

val treekem_keyschedule_state_auth_weak_exists_inj:
  st1:treekem_keyschedule_state bytes -> st2:treekem_keyschedule_state bytes ->
  Lemma
  (requires
    treekem_keyschedule_state_auth_weak_exists st1 /\
    treekem_keyschedule_state_auth_weak_exists st2 /\
    st1.epoch_keys.confirmation_tag == st2.epoch_keys.confirmation_tag
  )
  (ensures st1 == st2)
let treekem_keyschedule_state_auth_weak_exists_inj st1 st2 =
  eliminate exists epoch_secret1 group_context1 epoch_secret2 group_context2.
    treekem_keyschedule_state_auth_weak st1 epoch_secret1 group_context1 /\
    treekem_keyschedule_state_auth_weak st2 epoch_secret2 group_context2
  returns st1 == st2
  with _. (
    treekem_keyschedule_state_auth_weak_inj st1 epoch_secret1 group_context1 st2 epoch_secret2 group_context2
  )

(*** Relation between stong and weak ***)

val treekem_keyschedule_state_auth_exists_strong_to_weak:
  st:treekem_keyschedule_state bytes ->
  Lemma
  (requires treekem_keyschedule_state_auth_strong_exists st)
  (ensures treekem_keyschedule_state_auth_weak_exists st)
let treekem_keyschedule_state_auth_exists_strong_to_weak st =
  eliminate exists joiner_secret psks group_context. treekem_keyschedule_state_auth_strong st joiner_secret psks group_context
  returns treekem_keyschedule_state_auth_weak_exists st with _. (
    let Success epoch_secret = secret_joiner_to_epoch joiner_secret psks group_context in
    assert(treekem_keyschedule_state_auth_weak st epoch_secret group_context)
  )
