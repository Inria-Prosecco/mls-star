module MLS.Crypto.Builtins

open Comparse
open MLS.Result

(*** Typeclass definition ***)

type available_ciphersuite =
  | AC_mls_128_dhkemx25519_aes128gcm_sha256_ed25519
  | AC_mls_128_dhkemx25519_chacha20poly1305_sha256_ed25519

class crypto_bytes (bytes:Type0) = {
  [@@@FStar.Tactics.Typeclasses.tcinstance]
  base: bytes_like bytes;

  //TODO: stronger than bytes_like.recognize_empty
  //Useful to check hashes
  bytes_hasEq: squash (hasEq bytes);

  ciphersuite: available_ciphersuite;

  hash_hash: buf:bytes -> result bytes;
  hash_max_input_length: nat;
  hash_hash_pre: buf:bytes -> Lemma (requires length buf < hash_max_input_length) (ensures Success? (hash_hash buf));
  // Condition necessary for TreeSync's security theorem
  hash_output_length_bound: buf:bytes -> Lemma (hash_hash buf <> Success empty);

  kdf_length: nat;
  kdf_extract: key:bytes -> data:bytes -> result (lbytes bytes kdf_length);
  kdf_expand: prk:bytes -> info:bytes -> len:nat -> result (lbytes bytes len);

  hpke_public_key_length: nat;
  hpke_public_key_length_bound: squash (hpke_public_key_length < pow2 16);
  hpke_private_key_length: nat;
  hpke_private_key_length_bound: squash(hpke_private_key_length <= kdf_length);
  hpke_kem_output_length: nat;
  hpke_gen_keypair: ikm:bytes{length ikm >= hpke_private_key_length} -> result (lbytes bytes hpke_private_key_length & lbytes bytes hpke_public_key_length);
  hpke_encrypt: pkR:lbytes bytes hpke_public_key_length -> info:bytes -> ad:bytes -> plaintext:bytes -> entropy:lbytes bytes hpke_private_key_length -> result (lbytes bytes hpke_kem_output_length & bytes);
  hpke_decrypt: enc:lbytes bytes hpke_kem_output_length -> skR:lbytes bytes hpke_private_key_length -> info:bytes -> ad:bytes -> ciphertext:bytes -> result bytes;

  sign_gen_keypair_min_entropy_length: nat;
  sign_gen_keypair: entropy:bytes{length entropy >= sign_gen_keypair_min_entropy_length} -> result (verification:bytes * signature:bytes);
  sign_sign_min_entropy_length: nat;
  sign_sign: signature_key:bytes -> buf:bytes -> entropy:bytes{length entropy >= sign_sign_min_entropy_length} -> result bytes;
  sign_verify: verification_key:bytes -> buf:bytes -> signature:bytes -> bool;

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

  //For debugging purposes
  debug_bytes_to_string: bytes -> string;
}

(*** Utility types ***)

//type hash_type (bytes:Type0) {|crypto_bytes bytes|} = lbytes bytes (hash_length #bytes)

type hpke_public_key (bytes:Type0) {|crypto_bytes bytes|} = lbytes bytes (hpke_public_key_length #bytes)
type hpke_private_key (bytes:Type0) {|crypto_bytes bytes|} = lbytes bytes (hpke_private_key_length #bytes)
type hpke_kem_output (bytes:Type0) {|crypto_bytes bytes|} = lbytes bytes (hpke_kem_output_length #bytes)
type hpke_ikm (bytes:Type0) {|crypto_bytes bytes|} = b:bytes{length b >= hpke_private_key_length #bytes}

type sign_nonce (bytes:Type0) {|crypto_bytes bytes|} = b:bytes{length b >= sign_sign_min_entropy_length #bytes}

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

val randomness:
  bytes:Type0 -> {|bytes_like bytes|} ->
  list nat ->
  Type0
val mk_empty_randomness:
  bytes:Type0 -> {|bytes_like bytes|} ->
  randomness bytes []
val mk_randomness:
  #bytes:Type0 -> {|bytes_like bytes|} ->
  #head_size:nat -> #tail_size:list nat ->
  (lbytes bytes head_size & randomness bytes tail_size) ->
  randomness bytes (head_size::tail_size)
val dest_randomness:
  #bytes:Type0 -> {|bytes_like bytes|} ->
  #head_size:nat -> #tail_size:list nat ->
  randomness bytes (head_size::tail_size) ->
  (lbytes bytes head_size & randomness bytes tail_size)
