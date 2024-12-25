module MLS.TreeKEM.API.KeySchedule

open Comparse
open MLS.Crypto
open MLS.NetworkTypes
open MLS.TreeKEM.NetworkTypes
open MLS.TreeKEM.API.KeySchedule.Types
open MLS.TreeKEM.KeySchedule
open MLS.Result

val create:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  bytes ->
  result (treekem_keyschedule_state bytes & bytes)
let create #bytes #cb epoch_secret =
  let? sender_data_secret = secret_epoch_to_sender_data epoch_secret in
  let? encryption_secret = secret_epoch_to_encryption epoch_secret in
  let? exporter_secret = secret_epoch_to_exporter epoch_secret in
  let? external_secret = secret_epoch_to_external epoch_secret in
  let? confirmation_key = secret_epoch_to_confirmation epoch_secret in
  let? membership_key = secret_epoch_to_membership epoch_secret in
  let? resumption_psk = secret_epoch_to_resumption epoch_secret in
  let? epoch_authenticator = secret_epoch_to_authentication epoch_secret in
  let? init_secret = secret_epoch_to_init epoch_secret in
  return (({
    epoch_keys = {
      sender_data_secret;
      exporter_secret;
      external_secret;
      confirmation_key;
      membership_key;
      resumption_psk;
      epoch_authenticator;
    };
    init_secret;
  } <: treekem_keyschedule_state bytes), (encryption_secret <: bytes))

type secrets_for_welcome (bytes:Type0) = {
  joiner_secret: bytes;
  welcome_secret: bytes;
}

val commit:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  treekem_keyschedule_state bytes ->
  option bytes ->
  list (pre_shared_key_id_nt bytes & bytes) ->
  group_context_nt bytes ->
  result (treekem_keyschedule_state bytes & bytes & secrets_for_welcome bytes)
let commit #bytes #cb st opt_commit_secret psks new_group_context =
  let? joiner_secret: bytes = secret_init_to_joiner st.init_secret opt_commit_secret (serialize _ new_group_context) in
  let? epoch_secret: bytes = secret_joiner_to_epoch joiner_secret psks (serialize _ new_group_context) in
  let? welcome_secret: bytes = secret_joiner_to_welcome joiner_secret psks in
  let? (new_st, encryption_secret) = create epoch_secret in
  return (new_st, encryption_secret, {
    joiner_secret;
    welcome_secret;
  })

val export:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  treekem_keyschedule_state bytes ->
  valid_label -> bytes -> len:nat ->
  result (lbytes bytes len)
let export #bytes #cb st label context len =
  mls_exporter st.epoch_keys.exporter_secret label context len
