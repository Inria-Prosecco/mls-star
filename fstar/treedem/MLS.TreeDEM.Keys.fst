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

val derive_tree_secret:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  secret:bytes -> label:valid_label -> generation:nat -> len:nat ->
  result (lbytes bytes len)
let derive_tree_secret #bytes #cb secret label generation len =
  let? generation = mk_nat_lbytes generation "derive_tree_secret" "generation" in
  let tree_context = serialize tree_context_nt ({
    generation = generation;
  }) in
  expand_with_label secret label tree_context len

val leaf_kdf:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  #l:nat -> #i:tree_index l ->
  bytes -> leaf_index l i ->
  result bytes
let rec leaf_kdf #bytes #cb #l #i encryption_secret leaf_index =
  if l = 0 then (
    return encryption_secret
  ) else (
    let dir_string = if is_left_leaf leaf_index then "left" else "right" in
    let new_i = if is_left_leaf leaf_index then left_index i else right_index i in
    let? new_encryption_secret = expand_with_label encryption_secret "tree" (string_to_bytes #bytes dir_string) (kdf_length #bytes) in
    leaf_kdf #bytes #cb #_ #new_i new_encryption_secret leaf_index
  )

type ratchet_state (bytes:Type0) {|crypto_bytes bytes|} = {
  secret: lbytes bytes (kdf_length #bytes);
  generation: nat;
}

let init_ratchet_state (bytes:Type0) {|crypto_bytes bytes|} = st:ratchet_state bytes{st.generation = 0}

type ratchet_output (bytes:Type0) {|crypto_bytes bytes|} = {
  nonce: lbytes bytes (aead_nonce_length #bytes);
  key: lbytes bytes (aead_key_length #bytes);
}

val init_handshake_ratchet:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  bytes ->
  result (init_ratchet_state bytes)
let init_handshake_ratchet #bytes #cb tree_node_secret =
  let? ratchet_secret = expand_with_label tree_node_secret "handshake" (string_to_bytes #bytes "") (kdf_length #bytes) in
  return ({
    secret = ratchet_secret;
    generation = 0;
  } <: init_ratchet_state bytes)

//TODO: this is a copy-paste of init_handeshake_ratchet, factorize?
val init_application_ratchet:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  bytes ->
  result (init_ratchet_state bytes)
let init_application_ratchet #bytes #cb tree_node_secret =
  let? ratchet_secret = expand_with_label tree_node_secret "application" (string_to_bytes #bytes "") (kdf_length #bytes) in
  return ({
    secret = ratchet_secret;
    generation = 0;
  } <: init_ratchet_state bytes)

val ratchet_get_key:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  ratchet_state bytes ->
  result (ratchet_output bytes)
let ratchet_get_key #bytes #cb st =
  let? nonce = derive_tree_secret st.secret "nonce" st.generation (aead_nonce_length #bytes) in
  let? key = derive_tree_secret st.secret "key" st.generation (aead_key_length #bytes) in
  return ({
    nonce = nonce;
    key = key;
  })

val ratchet_next_state:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  ratchet_state bytes ->
  result (ratchet_state bytes)
let ratchet_next_state #bytes #cb st =
  let? new_secret = derive_tree_secret st.secret "secret" st.generation (kdf_length #bytes) in
  return ({
    secret = new_secret;
    generation = st.generation + 1;
  })

//#push-options "--fuel 1 --ifuel 1"
val ratchet_get_generation_key:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  st:ratchet_state bytes -> i:nat{st.generation <= i} ->
  Tot (result (ratchet_output bytes))
  (decreases i-st.generation)
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
