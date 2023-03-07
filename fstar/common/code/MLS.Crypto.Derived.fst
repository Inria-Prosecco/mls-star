module MLS.Crypto.Derived

open Comparse
open MLS.Crypto.Builtins
open MLS.NetworkTypes
open MLS.Result


#set-options "--fuel 0 --ifuel 0"

#push-options "--ifuel 1"
val available_ciphersuite_from_network: cipher_suite_nt -> result available_ciphersuite
let available_ciphersuite_from_network cs =
  match cs with
  | CS_reserved -> error "available_ciphersuite_from_network: ciphersuite not available"
  | CS_mls_128_dhkemx25519_aes128gcm_sha256_ed25519 -> return AC_mls_128_dhkemx25519_aes128gcm_sha256_ed25519
  | CS_mls_128_dhkemp256_aes128gcm_sha256_p256 -> error "available_ciphersuite_from_network: ciphersuite not available"
  | CS_mls_128_dhkemx25519_chacha20poly1305_sha256_ed25519 -> return AC_mls_128_dhkemx25519_chacha20poly1305_sha256_ed25519
  | CS_mls_256_dhkemx448_aes256gcm_sha512_ed448 -> error "available_ciphersuite_from_network: ciphersuite not available"
  | CS_mls_256_dhkemp521_aes256gcm_sha512_p521 -> error "available_ciphersuite_from_network: ciphersuite not available"
  | CS_mls_256_dhkemx448_chacha20poly1305_sha512_ed448 -> error "available_ciphersuite_from_network: ciphersuite not available"
  | CS_mls_256_dhkemp384_aes256gcm_sha384_p384 -> error "available_ciphersuite_from_network: ciphersuite not available"
  | CS_unknown _ -> error "available_ciphersuite_from_network: ciphersuite not available"
#pop-options

#push-options "--ifuel 1"
val available_ciphersuite_to_network: available_ciphersuite -> cipher_suite_nt
let available_ciphersuite_to_network cs =
  match cs with
  | AC_mls_128_dhkemx25519_aes128gcm_sha256_ed25519 -> CS_mls_128_dhkemx25519_aes128gcm_sha256_ed25519
  | AC_mls_128_dhkemx25519_chacha20poly1305_sha256_ed25519 -> CS_mls_128_dhkemx25519_chacha20poly1305_sha256_ed25519
#pop-options

#push-options "--ifuel 1"
private let sanity_lemma_1 (cs:available_ciphersuite):
  Lemma (available_ciphersuite_from_network (available_ciphersuite_to_network cs) == return cs)
  = ()
private let sanity_lemma_2 (cs:cipher_suite_nt): Lemma (
  match (available_ciphersuite_from_network cs) with
  | Success acs -> available_ciphersuite_to_network acs == cs
  | _ -> True
) = ()
#pop-options

(*** SignWithLabel / VerifyWithLabel ***)

type sign_content_nt (bytes:Type0) {|bytes_like bytes|} = {
  label: mls_bytes bytes;
  content: mls_bytes bytes;
}

%splice [ps_sign_content_nt] (gen_parser (`sign_content_nt))
%splice [ps_sign_content_nt_length] (gen_length_lemma (`sign_content_nt))
%splice [ps_sign_content_nt_is_well_formed] (gen_is_well_formed_lemma (`sign_content_nt))

instance parseable_serializeable_sign_content_nt (bytes:Type0) {|bytes_like bytes|}: parseable_serializeable bytes (sign_content_nt bytes) = mk_parseable_serializeable ps_sign_content_nt

let valid_label = s:string{b2t (normalize_term (string_is_ascii s)) /\ normalize_term (String.length s) < normalize_term ((pow2 30) - 8)}

val get_mls_label:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  label:valid_label ->
  Pure (mls_bytes bytes)
  (requires True)
  (ensures fun res -> length #bytes res == 8 + String.strlen label)
let get_mls_label #bytes #cb label =
  normalize_term_spec (String.strlen label);
  normalize_term_spec ((pow2 30) - 8);
  assert_norm (String.strlen "MLS 1.0 " == 8);
  let bytes_mls = string_to_bytes #bytes "MLS 1.0 " in
  let bytes_label = string_to_bytes #bytes label in
  concat_length #bytes bytes_mls bytes_label;
  concat #bytes bytes_mls bytes_label

let sign_with_label_pre (#bytes:Type0) {|crypto_bytes bytes|} (label:valid_label) (length_content:mls_nat): bool =
  8 + (8 + String.strlen label) + length_content < sign_max_input_length #bytes

val get_sign_content:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  label:valid_label -> content:mls_bytes bytes ->
  Pure bytes
  (requires sign_with_label_pre #bytes label (length #bytes content))
  (ensures fun res -> length #bytes res < sign_max_input_length #bytes)
let get_sign_content #bytes #cb label content =
  ((ps_prefix_to_ps_whole ps_sign_content_nt).serialize ({
    label = get_mls_label #bytes label;
    content = content;
  }))

val sign_with_label:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  signature_key:sign_private_key bytes -> label:valid_label -> content:mls_bytes bytes{sign_with_label_pre #bytes label (length #bytes content)} -> entropy:sign_nonce bytes ->
  sign_signature bytes
let sign_with_label #bytes #cb signature_key label content entropy =
  let sign_content = get_sign_content label content in
  sign_sign signature_key sign_content entropy

val verify_with_label:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  verification_key:sign_public_key bytes -> label:valid_label -> content:mls_bytes bytes{sign_with_label_pre #bytes label (length #bytes content)} -> signature:sign_signature bytes ->
  bool
let verify_with_label #bytes #cb verification_key label content signature =
  let sign_content = get_sign_content label content in
  sign_verify verification_key sign_content signature

(*** ExpandWithLabel / DeriveSecret ***)

type kdf_label_nt (bytes:Type0) {|bytes_like bytes|} = {
  length: nat_lbytes 2;
  label: mls_bytes bytes;
  context: mls_bytes bytes;
}

%splice [ps_kdf_label_nt] (gen_parser (`kdf_label_nt))

val expand_with_label:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  secret:bytes -> label:bytes -> context:bytes -> len:nat ->
  result (lbytes bytes len)
let expand_with_label #bytes #cb secret label context len =
  assert_norm (String.strlen "MLS 1.0 " == 8);
  if not (len < pow2 16) then
    internal_failure "expand_with_label: len too high"
  else if not (length label < (pow2 30)-8) then
    internal_failure "expand_with_label: label too long"
  else if not (length context < pow2 30) then
    internal_failure "expand_with_label: context too long"
  else (
    concat_length (string_to_bytes #bytes "MLS 1.0 ") label;
    let kdf_label = (ps_prefix_to_ps_whole ps_kdf_label_nt).serialize ({
      length = len;
      label = concat #bytes (string_to_bytes #bytes "MLS 1.0 ") label;
      context = context;
    }) in
    kdf_expand secret kdf_label len
  )

val derive_secret:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  secret:bytes -> label:bytes ->
  result (lbytes bytes (kdf_length #bytes))
let derive_secret #bytes #cb secret label =
  expand_with_label secret label (empty #bytes) (kdf_length #bytes)

(*** EncryptWithLabel / DecryptWithLabel ***)

type encrypt_context_nt (bytes:Type0) {|bytes_like bytes|} = {
  label: mls_bytes bytes;
  context: mls_bytes bytes;
}

%splice[ps_encrypt_context_nt] (gen_parser (`encrypt_context_nt))

instance parseable_serializeable_encrypt_context_nt (bytes:Type0) {|bytes_like bytes|}: parseable_serializeable bytes (encrypt_context_nt bytes) = mk_parseable_serializeable ps_encrypt_context_nt

val compute_encryption_context:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  label:valid_label -> context:bytes ->
  result bytes
let compute_encryption_context #bytes #cb label context =
  if not (length context < pow2 30) then
    internal_failure "compute_encryption_context: context too long"
  else (
    let label_bytes = get_mls_label label in
    let context = {
      label = label_bytes;
      context;
    } in
    return (serialize (encrypt_context_nt bytes) context)
  )

val encrypt_with_label:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  pkR:lbytes bytes (hpke_public_key_length #bytes) -> label:valid_label -> context:bytes -> plaintext:bytes -> entropy:lbytes bytes (hpke_private_key_length #bytes) ->
  result (lbytes bytes (hpke_kem_output_length #bytes) & bytes)
let encrypt_with_label #bytes #cb pkR label context plaintext entropy =
  let? context_bytes = compute_encryption_context label context in
  hpke_encrypt pkR context_bytes empty plaintext entropy

val decrypt_with_label:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  skR:lbytes bytes (hpke_private_key_length #bytes) -> label:valid_label -> context:bytes -> kem_output:lbytes bytes (hpke_kem_output_length #bytes) -> ciphertext:bytes ->
  result bytes
let decrypt_with_label #bytes #cb skR label context kem_output ciphertext =
  let? context_bytes = compute_encryption_context label context in
  hpke_decrypt kem_output skR context_bytes empty ciphertext

(*** Ref hash ***)

type ref_hash_input_nt (bytes:Type0) {|bytes_like bytes|} = {
  label: mls_bytes bytes;
  value: mls_bytes bytes;
}

%splice [ps_ref_hash_input_nt] (gen_parser (`ref_hash_input_nt))

instance parseable_serializeable_ref_hash_input_nt (bytes:Type0) {|bytes_like bytes|}: parseable_serializeable bytes (ref_hash_input_nt bytes) = mk_parseable_serializeable ps_ref_hash_input_nt

val ref_hash:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  bytes -> bytes ->
  result (lbytes bytes (hash_length #bytes))
let ref_hash #bytes #cb label value =
  if not (length label < pow2 30) then
    internal_failure "ref_hash: label too long"
  else if not (length value < pow2 30) then
    internal_failure "ref_hash: value too long"
  else if not (length #bytes (serialize (ref_hash_input_nt bytes) ({label; value;})) < hash_max_input_length #bytes) then
    internal_failure "ref_hash: hash_pre failed"
  else (
    return (hash_hash (serialize #bytes (ref_hash_input_nt bytes) ({label; value;})))
  )

val make_keypackage_ref:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  bytes ->
  result (lbytes bytes (hash_length #bytes))
let make_keypackage_ref #bytes #cb buf =
  ref_hash (string_to_bytes #bytes "MLS 1.0 KeyPackage Reference") buf

val make_proposal_ref:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  bytes ->
  result (lbytes bytes (hash_length #bytes))
let make_proposal_ref #bytes #cb buf =
  ref_hash (string_to_bytes #bytes "MLS 1.0 Proposal Reference") buf

(*** Utility functions ***)

#push-options "--fuel 1 --ifuel 1"
val split_randomness:
  #bytes:Type0 -> {|bytes_like bytes|} ->
  #l1:list nat -> #l2:list nat ->
  randomness bytes (List.Tot.append l1 l2) ->
  (randomness bytes l1 & randomness bytes l2)
let rec split_randomness #bytes #bl #l1 #l2 r =
  match l1 with
  | [] -> (mk_empty_randomness bytes, r)
  | h1::t1 ->
    let (rh, rt) = dest_randomness (r <: randomness bytes (h1::(t1@l2))) in
    let (rt1, rl2) = split_randomness rt in
    (mk_randomness (rh, rt1), rl2)
#pop-options

val mk_zero_vector:
  #bytes:Type0 -> {|bytes_like bytes|} ->
  n:nat ->
  lbytes bytes n
let mk_zero_vector #bytes #bl n =
  FStar.Math.Lemmas.pow2_le_compat n 0;
  from_nat #bytes n 0

val zero_vector:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  bytes
let zero_vector #bytes #cb =
  mk_zero_vector #bytes (kdf_length #bytes)
