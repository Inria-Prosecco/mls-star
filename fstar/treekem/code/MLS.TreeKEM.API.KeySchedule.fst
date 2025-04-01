module MLS.TreeKEM.API.KeySchedule

open Comparse
open MLS.Crypto
open MLS.NetworkTypes
open MLS.TreeKEM.NetworkTypes
open MLS.TreeKEM.API.KeySchedule.Types
open MLS.TreeKEM.KeySchedule
open MLS.Result

[@"opaque_to_smt"]
val create_from_epoch_secret:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  bytes -> group_context_nt bytes ->
  result (treekem_keyschedule_state bytes & bytes)
let create_from_epoch_secret #bytes #cb epoch_secret group_context =
  let? sender_data_secret = secret_epoch_to_sender_data epoch_secret in
  let? encryption_secret = secret_epoch_to_encryption epoch_secret in
  let? exporter_secret = secret_epoch_to_exporter epoch_secret in
  let? external_secret = secret_epoch_to_external epoch_secret in
  let? confirmation_key = secret_epoch_to_confirmation epoch_secret in
  let? confirmation_tag = compute_confirmation_tag (confirmation_key <: bytes) group_context.confirmed_transcript_hash in
  let? membership_key = secret_epoch_to_membership epoch_secret in
  let? resumption_psk = secret_epoch_to_resumption epoch_secret in
  let? epoch_authenticator = secret_epoch_to_authentication epoch_secret in
  let? init_secret = secret_epoch_to_init epoch_secret in
  return (({
    epoch_keys = {
      sender_data_secret;
      exporter_secret;
      external_secret;
      membership_key;
      resumption_psk;
      epoch_authenticator;
      confirmation_tag;
    };
    init_secret;
  } <: treekem_keyschedule_state bytes), (encryption_secret <: bytes))

[@"opaque_to_smt"]
val create_from_joiner_secret:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  bytes -> list (pre_shared_key_id_nt bytes & bytes) -> group_context_nt bytes ->
  result (treekem_keyschedule_state bytes & bytes)
let create_from_joiner_secret #bytes #cb joiner_secret psks group_context =
  let? epoch_secret = secret_joiner_to_epoch joiner_secret psks group_context in
  create_from_epoch_secret (epoch_secret <: bytes) group_context

type secrets_for_welcome (bytes:Type0) = {
  joiner_secret: bytes;
  welcome_secret: bytes;
}

[@"opaque_to_smt"]
val commit:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  treekem_keyschedule_state bytes ->
  option bytes ->
  list (pre_shared_key_id_nt bytes & bytes) ->
  group_context_nt bytes ->
  result (treekem_keyschedule_state bytes & bytes & secrets_for_welcome bytes)
let commit #bytes #cb st opt_commit_secret psks new_group_context =
  let? joiner_secret: bytes = secret_init_to_joiner st.init_secret opt_commit_secret new_group_context in
  let? epoch_secret: bytes = secret_joiner_to_epoch joiner_secret psks new_group_context in
  let? welcome_secret: bytes = secret_joiner_to_welcome joiner_secret psks in
  let? (new_st, encryption_secret) = create_from_epoch_secret epoch_secret new_group_context in
  return (new_st, encryption_secret, {
    joiner_secret;
    welcome_secret;
  })

[@"opaque_to_smt"]
val export:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  treekem_keyschedule_state bytes ->
  valid_label -> bytes -> len:nat ->
  result (lbytes bytes len)
let export #bytes #cb st label context len =
  mls_exporter st.epoch_keys.exporter_secret label context len
