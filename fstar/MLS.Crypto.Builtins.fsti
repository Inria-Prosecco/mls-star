module MLS.Crypto.Builtins

open Comparse
open MLS.Result

let string_is_ascii (s:string) = List.Tot.for_all (fun x -> FStar.Char.int_of_char x < 256) (FStar.String.list_of_string s)

(*** Typeclass definition ***)

type available_ciphersuite =
  | AC_mls_128_dhkemx25519_aes128gcm_sha256_ed25519
  | AC_mls_128_dhkemp256_aes128gcm_sha256_p256
  | AC_mls_128_dhkemx25519_chacha20poly1305_sha256_ed25519

class crypto_bytes (bytes:Type0) = {
  [@@@FStar.Tactics.Typeclasses.tcinstance]
  base: bytes_like bytes;

  //TODO: stronger than bytes_like.recognize_empty
  //Useful to check hashes
  bytes_hasEq: squash (hasEq bytes);

  ciphersuite: available_ciphersuite;

  hash_length: nat;
  hash_length_bound: squash (hash_length < 256);
  hash_hash: bytes -> result (lbytes bytes hash_length);

  kdf_length: nat;
  kdf_extract: key:bytes -> data:bytes -> result (lbytes bytes kdf_length);
  kdf_expand: prk:bytes -> info:bytes -> len:nat -> result (lbytes bytes len);

  hpke_public_key_length: nat;
  hpke_public_key_length_bound: squash (1 <= hpke_public_key_length /\ hpke_public_key_length < pow2 16);
  hpke_private_key_length: nat;
  hpke_private_key_length_bound: squash(hpke_private_key_length <= kdf_length);
  hpke_kem_output_length: nat;
  hpke_gen_keypair: ikm:bytes{length ikm >= hpke_private_key_length} -> result (lbytes bytes hpke_private_key_length & lbytes bytes hpke_public_key_length);
  hpke_encrypt: pkR:lbytes bytes hpke_public_key_length -> info:bytes -> ad:bytes -> plaintext:bytes -> entropy:lbytes bytes hpke_private_key_length -> result (lbytes bytes hpke_kem_output_length & bytes);
  hpke_decrypt: enc:lbytes bytes hpke_kem_output_length -> skR:lbytes bytes hpke_private_key_length -> info:bytes -> ad:bytes -> ciphertext:bytes -> result bytes;

  sign_public_key_length: nat;
  sign_private_key_length: nat;
  sign_nonce_length: nat;
  sign_signature_length: nat;
  sign_gen_keypair: entropy:lbytes bytes sign_private_key_length -> result (lbytes bytes sign_public_key_length & lbytes bytes sign_private_key_length);
  sign_sign: lbytes bytes sign_private_key_length -> bytes -> entropy:lbytes bytes sign_nonce_length -> result (lbytes bytes sign_signature_length);
  sign_verify: lbytes bytes sign_public_key_length -> bytes -> lbytes bytes sign_signature_length -> bool;

  aead_nonce_length: nat;
  aead_nonce_length_bound: squash (4 <= aead_nonce_length);
  aead_key_length: nat;
  aead_encrypt: lbytes bytes aead_key_length -> lbytes bytes aead_nonce_length -> ad:bytes -> plaintext:bytes -> result bytes;
  aead_decrypt: lbytes bytes aead_key_length -> lbytes bytes aead_nonce_length -> ad:bytes -> ciphertext:bytes -> result bytes;

  hmac_length: nat;
  hmac_length_bound: squash (hmac_length < 256);
  hmac_hmac: key:bytes -> data:bytes -> result (lbytes bytes hmac_length);

  string_to_bytes: s:string{b2t (normalize_term (string_is_ascii s))} -> lbytes bytes (String.strlen s);

  //TODO: in symbolic bytes, how do we do this?
  unsafe_split: b:bytes -> i:nat{i <= length b} -> bytes & bytes;
  xor: #n:nat -> lbytes bytes n -> lbytes bytes n -> lbytes bytes n;
}

(*** Utility types ***)

//type hash_type (bytes:Type0) {|crypto_bytes bytes|} = lbytes bytes (hash_length #bytes)

type hpke_public_key (bytes:Type0) {|crypto_bytes bytes|} = lbytes bytes (hpke_public_key_length #bytes)
type hpke_private_key (bytes:Type0) {|crypto_bytes bytes|} = lbytes bytes (hpke_private_key_length #bytes)
type hpke_kem_output (bytes:Type0) {|crypto_bytes bytes|} = lbytes bytes (hpke_kem_output_length #bytes)

type sign_public_key (bytes:Type0) {|crypto_bytes bytes|} = lbytes bytes (sign_public_key_length #bytes)
type sign_private_key (bytes:Type0) {|crypto_bytes bytes|} = lbytes bytes (sign_private_key_length #bytes)
type sign_nonce (bytes:Type0) {|crypto_bytes bytes|} = lbytes bytes (sign_nonce_length #bytes)
type sign_signature (bytes:Type0) {|crypto_bytes bytes|} = lbytes bytes (sign_signature_length #bytes)

type aead_nonce (bytes:Type0) {|crypto_bytes bytes|} = lbytes bytes (aead_nonce_length #bytes)
type aead_key (bytes:Type0) {|crypto_bytes bytes|} = lbytes bytes (aead_key_length #bytes)

(*** Instances ***)

type hacl_star_bytes = Lib.ByteSequence.bytes
val bytes_like_hacl_star_bytes: bytes_like hacl_star_bytes
val mk_concrete_crypto_bytes: available_ciphersuite -> Pure (crypto_bytes hacl_star_bytes)
  (requires True) (ensures fun cb -> cb.base == bytes_like_hacl_star_bytes)

//TODO
//val mk_symbolic_crypto_bytes: available_ciphersuite -> crypto_bytes dolev_yao_star_bytes

(*** Randomness ***)

val randomness: bytes:Type0 -> {|bytes_like bytes|} -> list nat -> Type0
val mk_empty_randomness: bytes:Type0 -> {|bytes_like bytes|} -> randomness bytes []
val mk_randomness:   #bytes:Type0 -> {|bytes_like bytes|} -> #head_size:nat -> #tail_size:list nat -> (lbytes bytes head_size & randomness bytes tail_size) -> randomness bytes (head_size::tail_size)
val dest_randomness: #bytes:Type0 -> {|bytes_like bytes|} -> #head_size:nat -> #tail_size:list nat -> randomness bytes (head_size::tail_size) -> (lbytes bytes head_size & randomness bytes tail_size)
