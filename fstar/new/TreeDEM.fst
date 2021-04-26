module TreeDEM

open Parser
open CryptoMLS
open Tree
open Lib.IntTypes
open Lib.ByteSequence
open Lib.Result
open TreeMath

noeq type tree_context_nt = {
  tc_node: uint32;
  tc_generation: uint32;
}

val ps_tree_context: parser_serializer tree_context_nt
let ps_tree_context =
  let open Parser in //Use `Parser.bind` in this function
  isomorphism tree_context_nt
    (
      _ <-- ps_u32;
      ps_u32
    )
    (fun (|node, generation|) -> {tc_node=node; tc_generation=generation})
    (fun x -> (|x.tc_node, x.tc_generation|))

val derive_tree_secret: cs:ciphersuite -> secret:bytes -> label:bytes -> node:nat -> generation:nat -> len:size_nat -> result (lbytes len)
let derive_tree_secret cs secret label node generation len =
  let open Parser in
  if not (node < pow2 32) then
    fail "derive_tree_secret: node too high"
  else if not (generation < pow2 32) then
    fail "derive_tree_secret: generation too high"
  else
    let tree_context = ps_tree_context.serialize ({
      tc_node = u32 node;
      tc_generation = u32 generation;
    }) in
    expand_with_label cs secret label tree_context len

val leaf_kdf: #l:nat -> n:tree_size l -> ciphersuite -> bytes -> node_index l -> leaf_index n -> result bytes
let rec leaf_kdf #l n cs encryption_secret root leaf_index =
  if l = 0 then (
    return encryption_secret
  ) else if n <= pow2 (l-1) then (
    leaf_kdf #(l-1) n cs encryption_secret (left root) leaf_index
  ) else (
    let (|dir, new_leaf_index|) = child_index l leaf_index in
    let new_root = (if dir = Left then left root else right root) in
    new_encryption_secret <-- derive_tree_secret cs encryption_secret (string_to_bytes "tree") new_root 0 (kdf_length cs);
    leaf_kdf (if dir = Left then pow2 (l-1) else n - pow2 (l-1)) cs new_encryption_secret new_root new_leaf_index
  )

val secret_init_to_joiner: cs:ciphersuite -> bytes -> bytes -> result (lbytes (kdf_length cs))
let secret_init_to_joiner cs init_secret commit_secret =
  prk <-- kdf_extract cs init_secret commit_secret;
  derive_secret cs prk (string_to_bytes "joiner")

val secret_joiner_to_epoch: cs:ciphersuite -> bytes -> bytes -> bytes -> result (lbytes (kdf_length cs))
let secret_joiner_to_epoch cs joiner_secret psk_secret group_context =
  prk <-- kdf_extract cs joiner_secret psk_secret;
  expand_with_label cs prk (string_to_bytes "epoch") group_context (kdf_length cs)

val secret_epoch_to_encryption: cs:ciphersuite -> bytes -> result (lbytes (kdf_length cs))
let secret_epoch_to_encryption cs epoch_secret =
  derive_secret cs epoch_secret (string_to_bytes "encryption")

val secret_epoch_to_init: cs:ciphersuite -> bytes -> result (lbytes (kdf_length cs))
let secret_epoch_to_init cs epoch_secret =
  derive_secret cs epoch_secret (string_to_bytes "init")

noeq type ratchet_state (cs:ciphersuite) = {
  rs_secret: lbytes (kdf_length cs);
  rs_seq: nat;
  rs_node: node_index 0;
}

noeq type ratchet_output (cs:ciphersuite) = {
  ro_nonce: lbytes (aead_nonce_length cs);
  ro_key: lbytes (aead_key_length cs);
}

val init_handshake_ratchet: cs:ciphersuite -> node_index 0 -> (lbytes (kdf_length cs)) -> result (ratchet_state cs)
let init_handshake_ratchet cs node tree_node_secret =
  ratchet_secret <-- derive_tree_secret cs tree_node_secret (string_to_bytes "handshake") node 0 (kdf_length cs);
  return ({
    rs_secret = ratchet_secret;
    rs_seq = 0;
    rs_node = node;
  })

//TODO: this is a copy-paste of init_handeshake_ratchet, factorize?
val init_application_ratchet: cs:ciphersuite -> node_index 0 -> (lbytes (kdf_length cs)) -> result (ratchet_state cs)
let init_application_ratchet cs node tree_node_secret =
  ratchet_secret <-- derive_tree_secret cs tree_node_secret (string_to_bytes "application") node 0 (kdf_length cs);
  return ({
    rs_secret = ratchet_secret;
    rs_seq = 0;
    rs_node = node;
  })

val ratchet_next_key: #cs:ciphersuite -> ratchet_state cs -> result (ratchet_output cs & ratchet_state cs)
let ratchet_next_key #cs st =
  nonce <-- derive_tree_secret cs st.rs_secret (string_to_bytes "nonce") st.rs_node st.rs_seq (aead_nonce_length cs);
  key <-- derive_tree_secret cs st.rs_secret (string_to_bytes "key") st.rs_node st.rs_seq (aead_key_length cs);
  new_secret <-- derive_tree_secret cs st.rs_secret (string_to_bytes "secret") st.rs_node st.rs_seq (kdf_length cs);
  return ({
    ro_nonce = nonce;
    ro_key = key;
  },{
    rs_secret = new_secret;
    rs_seq = st.rs_seq + 1;
    rs_node = st.rs_node;
  })
