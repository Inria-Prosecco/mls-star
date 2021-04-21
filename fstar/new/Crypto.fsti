module Crypto

open Spec.Agile.DH
open Spec.Agile.AEAD
open Spec.Agile.Hash

open Lib.Result
open Lib.ByteSequence
open Lib.IntTypes

module DH = Spec.Agile.DH
module AEAD = Spec.Agile.AEAD
module Hash = Spec.Agile.Hash

(*** Ciphersuite ***)

type signature_algorithm =
  | Ed_25519
  | P_256

val ciphersuite: Type0

(*** Cryptographic randomness ***)

val randomness: nat -> Type0
val split_randomness: #n:nat -> randomness n -> len:nat{len <= n} -> (randomness (n-len) & randomness len)

(*** KDF ***)

val kdf_length: ciphersuite -> size_nat

val kdf_extract_tot: cs:ciphersuite -> key:bytes{Seq.length key < pow2 31} -> data:bytes{Seq.length data < pow2 60} -> lbytes (kdf_length cs)
val kdf_expand_tot: cs:ciphersuite -> prk:bytes{kdf_length cs <= Seq.length prk /\ Seq.length prk <= pow2 31} -> info:bytes{Seq.length info <= pow2 60} -> len:nat{len <= 4080} -> lbytes len

val kdf_extract: cs:ciphersuite -> key:bytes -> data:bytes -> result (lbytes (kdf_length cs))
val kdf_expand: cs:ciphersuite -> prk:bytes -> info:bytes -> len:size_nat -> result (lbytes len)

(*** HPKE ***)

val hpke_public_key_length: ciphersuite -> n:size_nat{1 <= n /\ n < pow2 16}
val hpke_private_key_length: cs:ciphersuite -> n:size_nat{n <= kdf_length cs}
val hpke_kem_output_length: ciphersuite -> size_nat

type hpke_public_key (cs:ciphersuite) = lbytes (hpke_public_key_length cs)
type hpke_private_key (cs:ciphersuite) = lbytes (hpke_private_key_length cs)
type hpke_kem_output (cs:ciphersuite) = lbytes (hpke_kem_output_length cs)

val hpke_gen_keypair: cs:ciphersuite -> ikm:bytes{Seq.length ikm >= hpke_private_key_length cs} -> result (hpke_private_key cs & hpke_public_key cs)
val hpke_encrypt: cs:ciphersuite -> pkR:hpke_public_key cs -> info:bytes -> ad:bytes -> plaintext:bytes -> randomness (hpke_private_key_length cs) -> result (hpke_kem_output cs & bytes)
val hpke_decrypt: cs:ciphersuite -> enc:hpke_kem_output cs -> skR:hpke_private_key cs -> info:bytes -> ad:bytes -> ciphertext:bytes -> result bytes

(*** Signature ***)

val sign_public_key_length: ciphersuite -> size_nat
val sign_private_key_length: ciphersuite -> size_nat
val sign_nonce_length: ciphersuite -> size_nat
val sign_signature_length: ciphersuite -> size_nat

type sign_public_key (cs:ciphersuite) = lbytes (sign_public_key_length cs)
type sign_private_key (cs:ciphersuite) = lbytes (sign_private_key_length cs)
type sign_signature (cs:ciphersuite) = lbytes (sign_signature_length cs)

val sign_sign: cs:ciphersuite -> sign_private_key cs -> bytes -> randomness (sign_nonce_length cs) -> result (sign_signature cs)
val sign_verify: cs:ciphersuite -> sign_public_key cs -> bytes -> sign_signature cs -> bool

(*** AEAD ***)

val aead_nonce_length: ciphersuite -> size_nat
val aead_key_length: ciphersuite -> size_nat

type aead_key (cs:ciphersuite) = lbytes (aead_key_length cs)
type aead_nonce (cs:ciphersuite) = lbytes (aead_nonce_length cs)

val aead_encrypt: cs:ciphersuite -> aead_key cs -> aead_nonce cs -> ad:bytes -> plaintext:bytes -> result bytes
val aead_decrypt: cs:ciphersuite -> aead_key cs -> aead_nonce cs -> ad:bytes -> ciphertext:bytes -> result bytes

(*** String to bytes ***)

let string_is_ascii (s:string) = List.Tot.for_all (fun x -> FStar.Char.int_of_char x < 256) (FStar.String.list_of_string s)
val string_to_bytes: s:string{b2t (normalize_term (string_is_ascii s && String.strlen s < max_size_t))} -> lbytes (String.strlen s)
