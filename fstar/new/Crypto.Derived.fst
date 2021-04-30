module Crypto.Derived

friend Crypto.Builtins

open Parser
open NetworkTypes
open Lib.IntTypes

module DH = Spec.Agile.DH
module AEAD = Spec.Agile.AEAD
module Hash = Spec.Agile.Hash

let ciphersuite_from_nt cs =
  match cs with
  | CS_mls10_128_dhkemx25519_aes128gcm_sha256_ed25519 -> return ({
    kem_dh = DH.DH_Curve25519;
    kem_hash = Hash.SHA2_256;
    aead = AEAD.AES128_GCM;
    kdf_hash = Hash.SHA2_256;
    signature = Ed_25519;
  })
  | CS_mls10_128_dhkemp256_aes128gcm_sha256_p256 -> return ({
    kem_dh = DH.DH_P256;
    kem_hash = Hash.SHA2_256;
    aead = AEAD.AES128_GCM;
    kdf_hash = Hash.SHA2_256;
    signature = P_256;
  })
  | CS_mls10_128_dhkemx25519_chacha20poly1305_sha256_ed25519 -> return ({
    kem_dh = DH.DH_Curve25519;
    kem_hash = Hash.SHA2_256;
    aead = AEAD.CHACHA20_POLY1305;
    kdf_hash = Hash.SHA2_256;
    signature = Ed_25519;
  })
  | CS_mls10_256_dhkemx448_aes256gcm_sha512_ed448 -> fail "ciphersuite_from_nt: ciphersuite not available"
  | CS_mls10_256_dhkemp521_aes256gcm_sha512_p521 -> fail "ciphersuite_from_nt: ciphersuite not available"
  | CS_mls10_256_dhkemx448_chacha20poly1305_sha512_ed448 -> fail "ciphersuite_from_nt: ciphersuite not available"
  | _ -> fail "ciphersuite_from_nt: bad ciphersuite"

noeq type kdf_label_nt = {
  kln_length: uint16;
  kln_label: blbytes ({min=7; max=255});
  kln_context: blbytes ({min=0; max=(pow2 32)-1});
}

val ps_kdf_label: parser_serializer kdf_label_nt
let ps_kdf_label =
  isomorphism kdf_label_nt
    (
      _ <-- ps_u16;
      _ <-- ps_bytes _;
      ps_bytes _
    )
    (fun (|length, (|label, context|)|) -> {kln_length=length; kln_label=label; kln_context=context;})
    (fun x -> (|x.kln_length, (|x.kln_label, x.kln_context|)|))

let expand_with_label cs secret label context len =
  assert_norm (String.strlen "mls10 " == 6);
  if not (len < pow2 16) then
    fail "expand_with_label: len too high"
  else if not (1 <= Seq.length label) then
    fail "expand_with_label: label too short"
  else if not (Seq.length label < 255-6) then
    fail "expand_with_label: label too long"
  else if not (Seq.length context < pow2 32) then
    fail "expand_with_label: context too long"
  else
    let kdf_label = ps_kdf_label.serialize ({
      kln_length = u16 len;
      kln_label = Seq.append (string_to_bytes "mls10 ") label;
      kln_context = context;
    }) in
    kdf_expand cs secret kdf_label len

let derive_secret cs secret label =
  expand_with_label cs secret label bytes_empty (kdf_length cs)
