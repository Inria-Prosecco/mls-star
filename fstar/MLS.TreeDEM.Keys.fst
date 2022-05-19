module MLS.TreeDEM.Keys

open Comparse
open MLS.Crypto
open MLS.Tree
open MLS.TreeMath
open MLS.Result

noeq type tree_context_nt = {
  node: nat_lbytes 4;
  generation: nat_lbytes 4;
}

val ps_tree_context: #bytes:Type0 -> {|bytes_like bytes|} -> parser_serializer bytes tree_context_nt
let ps_tree_context #bytes #bl =
  let open Comparse in
  mk_isomorphism tree_context_nt
    (
      _ <-- ps_nat_lbytes 4;
      ps_nat_lbytes 4
    )
    (fun (|node, generation|) -> {node=node; generation=generation})
    (fun x -> (|x.node, x.generation|))

instance parseable_serializeable_tree_context_nt (bytes:Type0) {|bytes_like bytes|}: parseable_serializeable bytes tree_context_nt  =
  mk_parseable_serializeable ps_tree_context

val derive_tree_secret: #bytes:Type0 -> {|crypto_bytes bytes|} -> secret:bytes -> label:bytes -> node:nat -> generation:nat -> len:nat -> result (lbytes bytes len)
let derive_tree_secret #bytes #cb secret label node generation len =
  let open Comparse in
  if not (node < pow2 32) then
    internal_failure "derive_tree_secret: node too high"
  else if not (generation < pow2 32) then
    internal_failure "derive_tree_secret: generation too high"
  else
    let tree_context = serialize tree_context_nt ({
      node = node;
      generation = generation;
    }) in
    expand_with_label secret label tree_context len

val leaf_kdf_aux_normalize_node: l:nat -> n:tree_size l -> node_index l -> nat
let rec leaf_kdf_aux_normalize_node l n root =
  if l = 0 then (
    root
  ) else if n <= pow2 (l-1) then (
    leaf_kdf_aux_normalize_node (l-1) n (left root)
  ) else (
    root
  )

val leaf_kdf: #bytes:Type0 -> {|crypto_bytes bytes|} -> #l:nat -> n:tree_size l -> bytes -> node_index l -> leaf_index n -> result bytes
let rec leaf_kdf #bytes #cb #l n encryption_secret root leaf_index =
  if l = 0 then (
    return encryption_secret
  ) else if n <= pow2 (l-1) then (
    leaf_kdf (n <: tree_size (l-1)) encryption_secret (left root) leaf_index
  ) else (
    let (|dir, new_leaf_index|) = child_index l leaf_index in
    let new_root = (if dir = Left then left root else right root) in
    let new_n = (if dir = Left then pow2 (l-1) else n - pow2 (l-1)) in
    new_encryption_secret <-- derive_tree_secret encryption_secret (string_to_bytes #bytes "tree") (leaf_kdf_aux_normalize_node (l-1) new_n new_root) 0 (kdf_length #bytes);
    leaf_kdf #bytes new_n new_encryption_secret new_root new_leaf_index
  )

val opt_secret_to_secret: #bytes:Type0 -> {|crypto_bytes bytes|} -> option bytes -> bytes
let opt_secret_to_secret #bytes #cb opt_secret =
  match opt_secret with
  | Some secret -> secret
  | None -> zero_vector #bytes

val secret_init_to_joiner: #bytes:Type0 -> {|crypto_bytes bytes|} -> bytes -> option bytes -> bytes -> result (lbytes bytes (kdf_length #bytes))
let secret_init_to_joiner #bytes #cb init_secret opt_commit_secret group_context =
  prk <-- kdf_extract init_secret (opt_secret_to_secret opt_commit_secret);
  expand_with_label #bytes prk (string_to_bytes #bytes "joiner") group_context (kdf_length #bytes)

val secret_joiner_to_welcome: #bytes:Type0 -> {|crypto_bytes bytes|} -> bytes -> option bytes -> result (lbytes bytes (kdf_length #bytes))
let secret_joiner_to_welcome #bytes #cb joiner_secret opt_psk_secret =
  prk <-- kdf_extract joiner_secret (opt_secret_to_secret opt_psk_secret);
  derive_secret #bytes prk (string_to_bytes #bytes "welcome")

val secret_joiner_to_epoch: #bytes:Type0 -> {|crypto_bytes bytes|} -> bytes -> option bytes -> bytes -> result (lbytes bytes (kdf_length #bytes))
let secret_joiner_to_epoch #bytes #cb joiner_secret opt_psk_secret group_context =
  prk <-- kdf_extract joiner_secret (opt_secret_to_secret opt_psk_secret);
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

val secret_epoch_to_authentication: #bytes:Type0 -> {|crypto_bytes bytes|} -> bytes -> result (lbytes bytes (kdf_length #bytes))
let secret_epoch_to_authentication #bytes #cb epoch_secret =
  derive_secret epoch_secret (string_to_bytes #bytes "authentication")

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

val secret_epoch_to_init: #bytes:Type0 -> {|crypto_bytes bytes|} -> bytes -> result (lbytes bytes (kdf_length #bytes))
let secret_epoch_to_init #bytes #cb epoch_secret =
  derive_secret epoch_secret (string_to_bytes #bytes "init")

val secret_external_to_keypair: #bytes:Type0 -> {|crypto_bytes bytes|} -> lbytes bytes (kdf_length #bytes) -> result (hpke_private_key bytes & hpke_public_key bytes)
let secret_external_to_keypair #bytes #cb external_secret =
  hpke_gen_keypair external_secret

noeq type ratchet_state (bytes:Type0) {|crypto_bytes bytes|} = {
  secret: lbytes bytes (kdf_length #bytes);
  generation: nat;
  node: node_index 0;
}

let init_ratchet_state (bytes:Type0) {|crypto_bytes bytes|} = st:ratchet_state bytes{st.generation = 0}

noeq type ratchet_output (bytes:Type0) {|crypto_bytes bytes|} = {
  nonce: lbytes bytes (aead_nonce_length #bytes);
  key: lbytes bytes (aead_key_length #bytes);
}

val init_handshake_ratchet: #bytes:Type0 -> {|crypto_bytes bytes|} -> node_index 0 -> bytes -> result (init_ratchet_state bytes)
let init_handshake_ratchet #bytes #cb node tree_node_secret =
  ratchet_secret <-- derive_tree_secret tree_node_secret (string_to_bytes #bytes "handshake") node 0 (kdf_length #bytes);
  return ({
    secret = ratchet_secret;
    generation = 0;
    node = node;
  } <: init_ratchet_state bytes)

//TODO: this is a copy-paste of init_handeshake_ratchet, factorize?
val init_application_ratchet: #bytes:Type0 -> {|crypto_bytes bytes|} -> node_index 0 -> bytes -> result (init_ratchet_state bytes)
let init_application_ratchet #bytes #cb node tree_node_secret =
  ratchet_secret <-- derive_tree_secret tree_node_secret (string_to_bytes #bytes "application") node 0 (kdf_length #bytes);
  return ({
    secret = ratchet_secret;
    generation = 0;
    node = node;
  } <: init_ratchet_state bytes)

val ratchet_get_key: #bytes:Type0 -> {|crypto_bytes bytes|} -> ratchet_state bytes -> result (ratchet_output bytes)
let ratchet_get_key #bytes #cb st =
  nonce <-- derive_tree_secret st.secret (string_to_bytes #bytes "nonce") st.node st.generation (aead_nonce_length #bytes);
  key <-- derive_tree_secret st.secret (string_to_bytes #bytes "key") st.node st.generation (aead_key_length #bytes);
  return ({
    nonce = nonce;
    key = key;
  })

val ratchet_next_state: #bytes:Type0 -> {|crypto_bytes bytes|} -> ratchet_state bytes -> result (ratchet_state bytes)
let ratchet_next_state #bytes #cb st =
  new_secret <-- derive_tree_secret st.secret (string_to_bytes #bytes "secret") st.node st.generation (kdf_length #bytes);
  return ({
    secret = new_secret;
    generation = st.generation + 1;
    node = st.node;
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
