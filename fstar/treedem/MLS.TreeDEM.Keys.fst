module MLS.TreeDEM.Keys

open Comparse
open MLS.Crypto
open MLS.Tree
open MLS.Result

type tree_context_nt = {
  generation: nat_lbytes 4;
}

%splice [ps_tree_context_nt] (gen_parser (`tree_context_nt))

instance parseable_serializeable_tree_context_nt (bytes:Type0) {|bytes_like bytes|}: parseable_serializeable bytes tree_context_nt  =
  mk_parseable_serializeable ps_tree_context_nt

val derive_tree_secret: #bytes:Type0 -> {|crypto_bytes bytes|} -> secret:bytes -> label:bytes -> generation:nat -> len:nat -> result (lbytes bytes len)
let derive_tree_secret #bytes #cb secret label generation len =
  if not (generation < pow2 32) then
    internal_failure "derive_tree_secret: generation too high"
  else
    let tree_context = serialize tree_context_nt ({
      generation = generation;
    }) in
    expand_with_label secret label tree_context len

val leaf_kdf: #bytes:Type0 -> {|crypto_bytes bytes|} -> #l:nat -> #i:tree_index l -> bytes -> leaf_index l i -> result bytes
let rec leaf_kdf #bytes #cb #l #i encryption_secret leaf_index =
  if l = 0 then (
    return encryption_secret
  ) else (
    let dir_string = if is_left_leaf leaf_index then "left" else "right" in
    let new_i = if is_left_leaf leaf_index then left_index i else right_index i in
    let? new_encryption_secret = expand_with_label encryption_secret (string_to_bytes #bytes "tree") (string_to_bytes #bytes dir_string) (kdf_length #bytes) in
    leaf_kdf #bytes #cb #_ #new_i new_encryption_secret leaf_index
  )

val opt_secret_to_secret: #bytes:Type0 -> {|crypto_bytes bytes|} -> option bytes -> bytes
let opt_secret_to_secret #bytes #cb opt_secret =
  match opt_secret with
  | Some secret -> secret
  | None -> zero_vector #bytes

val secret_init_to_joiner: #bytes:Type0 -> {|crypto_bytes bytes|} -> bytes -> option bytes -> bytes -> result (lbytes bytes (kdf_length #bytes))
let secret_init_to_joiner #bytes #cb init_secret opt_commit_secret group_context =
  let? prk = kdf_extract init_secret (opt_secret_to_secret opt_commit_secret) in
  expand_with_label #bytes prk (string_to_bytes #bytes "joiner") group_context (kdf_length #bytes)

val secret_joiner_to_welcome: #bytes:Type0 -> {|crypto_bytes bytes|} -> bytes -> option bytes -> result (lbytes bytes (kdf_length #bytes))
let secret_joiner_to_welcome #bytes #cb joiner_secret opt_psk_secret =
  let? prk = kdf_extract joiner_secret (opt_secret_to_secret opt_psk_secret) in
  derive_secret #bytes prk (string_to_bytes #bytes "welcome")

val secret_joiner_to_epoch: #bytes:Type0 -> {|crypto_bytes bytes|} -> bytes -> option bytes -> bytes -> result (lbytes bytes (kdf_length #bytes))
let secret_joiner_to_epoch #bytes #cb joiner_secret opt_psk_secret group_context =
  let? prk = kdf_extract joiner_secret (opt_secret_to_secret opt_psk_secret) in
  expand_with_label #bytes prk (string_to_bytes #bytes "epoch") group_context (kdf_length #bytes)

val secret_epoch_to_sender_data: #bytes:Type0 -> {|crypto_bytes bytes|} -> bytes -> result (lbytes bytes (kdf_length #bytes))
let secret_epoch_to_sender_data #bytes #cb epoch_secret =
  derive_secret epoch_secret (string_to_bytes #bytes "sender data")

val secret_epoch_to_encryption: #bytes:Type0 -> {|crypto_bytes bytes|} -> bytes -> result (lbytes bytes (kdf_length #bytes))
let secret_epoch_to_encryption #bytes #cb epoch_secret =
  derive_secret epoch_secret (string_to_bytes #bytes "encryption")

val secret_epoch_to_exporter: #bytes:Type0 -> {|crypto_bytes bytes|} -> bytes -> result (lbytes bytes (kdf_length #bytes))
let secret_epoch_to_exporter #bytes #cb epoch_secret =
  derive_secret epoch_secret (string_to_bytes #bytes "exporter")

val secret_epoch_to_external: #bytes:Type0 -> {|crypto_bytes bytes|} -> bytes -> result (lbytes bytes (kdf_length #bytes))
let secret_epoch_to_external #bytes #cb epoch_secret =
  derive_secret epoch_secret (string_to_bytes #bytes "external")

val secret_epoch_to_confirmation: #bytes:Type0 -> {|crypto_bytes bytes|} -> bytes -> result (lbytes bytes (kdf_length #bytes))
let secret_epoch_to_confirmation #bytes #cb epoch_secret =
  derive_secret epoch_secret (string_to_bytes #bytes "confirm")

val secret_epoch_to_membership: #bytes:Type0 -> {|crypto_bytes bytes|} -> bytes -> result (lbytes bytes (kdf_length #bytes))
let secret_epoch_to_membership #bytes #cb epoch_secret =
  derive_secret epoch_secret (string_to_bytes #bytes "membership")

val secret_epoch_to_resumption: #bytes:Type0 -> {|crypto_bytes bytes|} -> bytes -> result (lbytes bytes (kdf_length #bytes))
let secret_epoch_to_resumption #bytes #cb epoch_secret =
  derive_secret epoch_secret (string_to_bytes #bytes "resumption")

val secret_epoch_to_authentication: #bytes:Type0 -> {|crypto_bytes bytes|} -> bytes -> result (lbytes bytes (kdf_length #bytes))
let secret_epoch_to_authentication #bytes #cb epoch_secret =
  derive_secret epoch_secret (string_to_bytes #bytes "authentication")

val secret_epoch_to_init: #bytes:Type0 -> {|crypto_bytes bytes|} -> bytes -> result (lbytes bytes (kdf_length #bytes))
let secret_epoch_to_init #bytes #cb epoch_secret =
  derive_secret epoch_secret (string_to_bytes #bytes "init")

val secret_external_to_keypair: #bytes:Type0 -> {|crypto_bytes bytes|} -> lbytes bytes (kdf_length #bytes) -> result (hpke_private_key bytes & hpke_public_key bytes)
let secret_external_to_keypair #bytes #cb external_secret =
  hpke_gen_keypair external_secret

type ratchet_state (bytes:Type0) {|crypto_bytes bytes|} = {
  secret: lbytes bytes (kdf_length #bytes);
  generation: nat;
}

let init_ratchet_state (bytes:Type0) {|crypto_bytes bytes|} = st:ratchet_state bytes{st.generation = 0}

type ratchet_output (bytes:Type0) {|crypto_bytes bytes|} = {
  nonce: lbytes bytes (aead_nonce_length #bytes);
  key: lbytes bytes (aead_key_length #bytes);
}

val init_handshake_ratchet: #bytes:Type0 -> {|crypto_bytes bytes|} -> bytes -> result (init_ratchet_state bytes)
let init_handshake_ratchet #bytes #cb tree_node_secret =
  let? ratchet_secret = expand_with_label tree_node_secret (string_to_bytes #bytes "handshake") (string_to_bytes #bytes "") (kdf_length #bytes) in
  return ({
    secret = ratchet_secret;
    generation = 0;
  } <: init_ratchet_state bytes)

//TODO: this is a copy-paste of init_handeshake_ratchet, factorize?
val init_application_ratchet: #bytes:Type0 -> {|crypto_bytes bytes|} -> bytes -> result (init_ratchet_state bytes)
let init_application_ratchet #bytes #cb tree_node_secret =
  let? ratchet_secret = expand_with_label tree_node_secret (string_to_bytes #bytes "application") (string_to_bytes #bytes "") (kdf_length #bytes) in
  return ({
    secret = ratchet_secret;
    generation = 0;
  } <: init_ratchet_state bytes)

val ratchet_get_key: #bytes:Type0 -> {|crypto_bytes bytes|} -> ratchet_state bytes -> result (ratchet_output bytes)
let ratchet_get_key #bytes #cb st =
  let? nonce = derive_tree_secret st.secret (string_to_bytes #bytes "nonce") st.generation (aead_nonce_length #bytes) in
  let? key = derive_tree_secret st.secret (string_to_bytes #bytes "key") st.generation (aead_key_length #bytes) in
  return ({
    nonce = nonce;
    key = key;
  })

val ratchet_next_state: #bytes:Type0 -> {|crypto_bytes bytes|} -> ratchet_state bytes -> result (ratchet_state bytes)
let ratchet_next_state #bytes #cb st =
  let? new_secret = derive_tree_secret st.secret (string_to_bytes #bytes "secret") st.generation (kdf_length #bytes) in
  return ({
    secret = new_secret;
    generation = st.generation + 1;
  })

//#push-options "--fuel 1 --ifuel 1"
val ratchet_get_generation_key: #bytes:Type0 -> {|crypto_bytes bytes|} -> st:ratchet_state bytes -> i:nat{st.generation <= i} -> Tot (result (ratchet_output bytes)) (decreases i-st.generation)
let rec ratchet_get_generation_key #bytes #cb st i =
  if st.generation = i then (
    ratchet_get_key st
  ) else (
    //Here we have to break encapsulation provided by `result` so fstar knows that `ratchet_next_state` increments `generation`
    match ratchet_next_state st with
    | InternalError s -> InternalError s
    | ProtocolError s -> ProtocolError s
    | Success next_st ->
      ratchet_get_generation_key next_st i
  )
