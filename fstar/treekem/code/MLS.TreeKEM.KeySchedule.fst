module MLS.TreeKEM.KeySchedule

open Comparse
open MLS.Crypto
open MLS.TreeKEM.NetworkTypes
open MLS.TreeKEM.PSK
open MLS.Result

val secret_init_to_joiner:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  bytes -> option bytes -> bytes ->
  result (lbytes bytes (kdf_length #bytes))
let secret_init_to_joiner #bytes #cb init_secret opt_commit_secret group_context =
  let commit_secret =
    match opt_commit_secret with
    | Some commit_secret -> commit_secret
    | None -> zero_vector #bytes
  in
  let? prk = kdf_extract init_secret commit_secret in
  expand_with_label #bytes prk "joiner" group_context (kdf_length #bytes)

// this version is tested in the test vectors
val secret_joiner_to_welcome_internal:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  bytes -> bytes ->
  result (lbytes bytes (kdf_length #bytes))
let secret_joiner_to_welcome_internal #bytes #cb joiner_secret psk_secret =
  let? prk = kdf_extract joiner_secret psk_secret in
  derive_secret #bytes prk "welcome"

val secret_joiner_to_welcome:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  bytes -> list (pre_shared_key_id_nt bytes & bytes) ->
  result (lbytes bytes (kdf_length #bytes))
let secret_joiner_to_welcome #bytes #cb joiner_secret psks =
  let? psk_secret = compute_psk_secret psks in
  secret_joiner_to_welcome_internal joiner_secret psk_secret

// this version is tested in the test vectors
val secret_joiner_to_epoch_internal:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  bytes -> bytes -> bytes ->
  result (lbytes bytes (kdf_length #bytes))
let secret_joiner_to_epoch_internal #bytes #cb joiner_secret psk_secret group_context =
  let? prk = kdf_extract joiner_secret psk_secret in
  expand_with_label #bytes prk "epoch" group_context (kdf_length #bytes)

val secret_joiner_to_epoch:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  bytes -> list (pre_shared_key_id_nt bytes & bytes) -> bytes ->
  result (lbytes bytes (kdf_length #bytes))
let secret_joiner_to_epoch #bytes #cb joiner_secret psks group_context =
  let? psk_secret = compute_psk_secret psks in
  secret_joiner_to_epoch_internal joiner_secret psk_secret group_context

val secret_epoch_to_sender_data:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  bytes ->
  result (lbytes bytes (kdf_length #bytes))
let secret_epoch_to_sender_data #bytes #cb epoch_secret =
  derive_secret epoch_secret "sender data"

val secret_epoch_to_encryption:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  bytes ->
  result (lbytes bytes (kdf_length #bytes))
let secret_epoch_to_encryption #bytes #cb epoch_secret =
  derive_secret epoch_secret "encryption"

val secret_epoch_to_exporter:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  bytes ->
  result (lbytes bytes (kdf_length #bytes))
let secret_epoch_to_exporter #bytes #cb epoch_secret =
  derive_secret epoch_secret "exporter"

val secret_epoch_to_external:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  bytes ->
  result (lbytes bytes (kdf_length #bytes))
let secret_epoch_to_external #bytes #cb epoch_secret =
  derive_secret epoch_secret "external"

val secret_epoch_to_confirmation:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  bytes ->
  result (lbytes bytes (kdf_length #bytes))
let secret_epoch_to_confirmation #bytes #cb epoch_secret =
  derive_secret epoch_secret "confirm"

val secret_epoch_to_membership:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  bytes ->
  result (lbytes bytes (kdf_length #bytes))
let secret_epoch_to_membership #bytes #cb epoch_secret =
  derive_secret epoch_secret "membership"

val secret_epoch_to_resumption:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  bytes ->
  result (lbytes bytes (kdf_length #bytes))
let secret_epoch_to_resumption #bytes #cb epoch_secret =
  derive_secret epoch_secret "resumption"

val secret_epoch_to_authentication:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  bytes ->
  result (lbytes bytes (kdf_length #bytes))
let secret_epoch_to_authentication #bytes #cb epoch_secret =
  derive_secret epoch_secret "authentication"

val secret_epoch_to_init:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  bytes ->
  result (lbytes bytes (kdf_length #bytes))
let secret_epoch_to_init #bytes #cb epoch_secret =
  derive_secret epoch_secret "init"

val secret_external_to_keypair:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  lbytes bytes (kdf_length #bytes) ->
  result (hpke_private_key bytes & hpke_public_key bytes)
let secret_external_to_keypair #bytes #cb external_secret =
  hpke_gen_keypair external_secret

val mls_exporter:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  bytes -> valid_label -> bytes -> len:nat ->
  result (lbytes bytes len)
let mls_exporter #bytes #cb exporter_secret label context len =
  let? derived_secret: bytes = derive_secret exporter_secret label in
  let? hashed_context = hash_hash context in
  expand_with_label #bytes derived_secret "exported" hashed_context len
