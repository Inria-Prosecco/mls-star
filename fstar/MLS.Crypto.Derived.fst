module MLS.Crypto.Derived

friend MLS.Crypto.Builtins

open MLS.NetworkTypes
open MLS.Crypto.Builtins
open MLS.Result

module DH = Spec.Agile.DH
module AEAD = Spec.Agile.AEAD
module Hash = Spec.Agile.Hash

#set-options "--fuel 0 --ifuel 0"

#push-options "--ifuel 1"
let available_ciphersuite_from_network cs =
  match cs with
  | CS_mls_128_dhkemx25519_aes128gcm_sha256_ed25519 () -> return AC_mls_128_dhkemx25519_aes128gcm_sha256_ed25519
  | CS_mls_128_dhkemp256_aes128gcm_sha256_p256 () -> return AC_mls_128_dhkemp256_aes128gcm_sha256_p256
  | CS_mls_128_dhkemx25519_chacha20poly1305_sha256_ed25519 () -> return AC_mls_128_dhkemx25519_chacha20poly1305_sha256_ed25519
  | CS_mls_256_dhkemx448_aes256gcm_sha512_ed448 () -> error "available_ciphersuite_from_network: ciphersuite not available"
  | CS_mls_256_dhkemp521_aes256gcm_sha512_p521 () -> error "available_ciphersuite_from_network: ciphersuite not available"
  | CS_mls_256_dhkemx448_chacha20poly1305_sha512_ed448 () -> error "available_ciphersuite_from_network: ciphersuite not available"
  | CS_mls_256_dhkemp384_aes256gcm_sha384_p384 () -> error "available_ciphersuite_from_network: ciphersuite not available"
#pop-options

#push-options "--ifuel 1"
let available_ciphersuite_to_network cs =
  match cs with
  | AC_mls_128_dhkemx25519_aes128gcm_sha256_ed25519 -> CS_mls_128_dhkemx25519_aes128gcm_sha256_ed25519 ()
  | AC_mls_128_dhkemp256_aes128gcm_sha256_p256 -> CS_mls_128_dhkemp256_aes128gcm_sha256_p256 ()
  | AC_mls_128_dhkemx25519_chacha20poly1305_sha256_ed25519 -> CS_mls_128_dhkemx25519_chacha20poly1305_sha256_ed25519 ()
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

noeq type sign_content_nt (bytes:Type0) {|bytes_like bytes|} = {
  label: tls_bytes bytes ({min=9; max=255});
  content: tls_bytes bytes ({min=0; max=(pow2 32)-1});
}

%splice [ps_sign_content_nt] (gen_parser (`sign_content_nt))

val get_sign_content: #bytes:Type0 -> {|crypto_bytes bytes|} -> label:bytes -> content:bytes -> result bytes
let get_sign_content #bytes #cb label content =
  assert_norm (String.strlen "MLS 1.0 " == 8);
  if not (1 <= length label) then
    internal_failure "get_sign_content: label too short"
  else if not (length label <= 255-8) then
    internal_failure "get_sign_content: label too long"
  else if not (length content < pow2 32) then
    internal_failure "get_sign_content: context too long"
  else (
    concat_length (string_to_bytes #bytes "MLS 1.0 ") label;
    return ((ps_to_pse ps_sign_content_nt).serialize_exact ({
      label = concat #bytes (string_to_bytes #bytes "MLS 1.0 ") label;
      content = content;
    }))
  )

let sign_with_label #bytes #cb signature_key label content entropy =
  sign_content <-- get_sign_content label content;
  sign_sign signature_key sign_content entropy

let verify_with_label #bytes #cb verification_key label content signature =
  sign_content <-- get_sign_content label content;
  return (sign_verify verification_key sign_content signature)

noeq type kdf_label_nt (bytes:Type0) {|bytes_like bytes|} = {
  length: nat_lbytes 2;
  label: tls_bytes bytes ({min=7; max=255});
  context: tls_bytes bytes ({min=0; max=(pow2 32)-1});
}

%splice [ps_kdf_label_nt] (gen_parser (`kdf_label_nt))

let expand_with_label #bytes #cb secret label context len =
  assert_norm (String.strlen "MLS 1.0 " == 8);
  if not (len < pow2 16) then
    internal_failure "expand_with_label: len too high"
  else if not (1 <= length label) then
    internal_failure "expand_with_label: label too short"
  else if not (length label <= 255-8) then
    internal_failure "expand_with_label: label too long"
  else if not (length context < pow2 32) then
    internal_failure "expand_with_label: context too long"
  else (
    concat_length (string_to_bytes #bytes "MLS 1.0 ") label;
    let kdf_label = (ps_to_pse ps_kdf_label_nt).serialize_exact ({
      length = len;
      label = concat #bytes (string_to_bytes #bytes "MLS 1.0 ") label;
      context = context;
    }) in
    kdf_expand secret kdf_label len
  )

let derive_secret #bytes #cb secret label =
  expand_with_label secret label (empty #bytes) (kdf_length #bytes)

let make_keypackage_ref #bytes #cb buf =
  tmp <-- kdf_extract (empty #bytes) buf;
  kdf_expand (tmp <: bytes) (string_to_bytes #bytes "MLS 1.0 KeyPackage Reference") 16

let make_leafnode_ref #bytes #cb buf =
  tmp <-- kdf_extract (empty #bytes) buf;
  kdf_expand (tmp <: bytes) (string_to_bytes #bytes "MLS 1.0 Leaf Node Reference") 16

let make_proposal_ref #bytes #cb buf =
  tmp <-- kdf_extract (empty #bytes) buf;
  kdf_expand (tmp <: bytes) (string_to_bytes #bytes "MLS 1.0 Proposal Reference") 16

#push-options "--fuel 1 --ifuel 1"
let rec split_randomness #bytes #bl #l1 #l2 r =
  match l1 with
  | [] -> (mk_empty_randomness bytes, r)
  | h1::t1 ->
    let (rh, rt) = dest_randomness (r <: randomness bytes (h1::(t1@l2))) in
    let (rt1, rl2) = split_randomness rt in
    (mk_randomness (rh, rt1), rl2)
#pop-options

let mk_zero_vector #bytes #bl n =
  FStar.Math.Lemmas.pow2_le_compat n 0;
  from_nat #bytes n 0

let zero_vector #bytes #cb =
  mk_zero_vector #bytes (kdf_length #bytes)
