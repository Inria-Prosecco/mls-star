module MLS.Crypto.Builtins

open FStar.Mul

open Lib.Sequence
open Lib.ByteSequence
open Lib.IntTypes

module DH = Spec.Agile.DH
module AEAD = Spec.Agile.AEAD
module Hash = Spec.Agile.Hash
module HKDF = Spec.Agile.HKDF
module HPKE = Spec.Agile.HPKE
module Ed25519 = Spec.Ed25519
module HMAC = Spec.Agile.HMAC

(*** Ciphersuite ***)

type ciphersuite_t = {
  kem_dh:  DH.algorithm;
  kem_hash: Hash.algorithm;
  aead: AEAD.alg;
  kdf_hash: Hash.algorithm;
  signature: signature_algorithm
}

val is_valid_ciphersuite_t: ciphersuite_t -> bool
let is_valid_ciphersuite_t cs =
  HPKE.is_valid_hash (cs.kem_hash) &&
  HPKE.is_valid_kem (cs.kem_dh, cs.kem_hash) &&
  HPKE.is_valid_aead (HPKE.Seal cs.aead) &&
  HPKE.is_valid_hash (cs.kdf_hash)

let ciphersuite = cs:ciphersuite_t{is_valid_ciphersuite_t cs}

val ciphersuite_to_hpke_ciphersuite: ciphersuite -> HPKE.ciphersuite
let ciphersuite_to_hpke_ciphersuite cs =
  (cs.kem_dh, cs.kem_hash, HPKE.Seal cs.aead, cs.kdf_hash)

(*** Cryptographic randomness ***)


type randomness (n:nat) = b:bytes{Seq.length b == n}
let mk_randomness #n r = r
let split_randomness #n e len =
    (Seq.slice e len n, Seq.slice e 0 len)

(*** Hash ***)

let hash_length cs =
  Hash.hash_length cs.kdf_hash

let hash_hash cs buf =
  if not (Seq.length buf <= Hash.max_input_length (cs.kdf_hash)) then
    fail "hash_hash: buf too long"
  else
    return (Hash.hash cs.kdf_hash buf)

(*** KDF ***)

val max_input_length_bound: a:Hash.hash_alg -> Lemma (pow2 61 - 1 <= Hash.max_input_length a)
let max_input_length_bound a =
  FStar.Math.Lemmas.pow2_le_compat 128 61;
  FStar.Math.Lemmas.pow2_le_compat 125 61;
  FStar.Math.Lemmas.pow2_le_compat 64 61

let kdf_length cs = Hash.hash_length cs.kdf_hash

let kdf_extract_tot cs key data =
  assert (Hash.block_length (cs.kdf_hash) <= 128);
  max_input_length_bound (cs.kdf_hash);
  assert_norm (pow2 60 < pow2 61 - 129); //==> Seq.length data + block_length a <= max_input_length a
  assert_norm (pow2 31 < pow2 32 - 128); //==> keysized (Seq.length key)
  assert_norm (pow2 31 < pow2 61 - 1); //==> keysized (Seq.length key)
  HKDF.extract (cs.kdf_hash) key data

let kdf_expand_tot cs prk info len =
  assert(16 <= Hash.hash_length cs.kdf_hash);
  assert (Hash.hash_length cs.kdf_hash <= 64);
  assert (Hash.block_length cs.kdf_hash <= 128);
  max_input_length_bound cs.kdf_hash;
  assert_norm(pow2 60 < pow2 61 - 194); //==> hash_length a + Seq.length info + 1 + block_length a <= max_input_length a
  assert_norm(pow2 31 < pow2 32 - 128); //==> keysized (Seq.length prk)
  assert_norm(pow2 31 < pow2 61 - 1); //==> keysized (Seq.length prk)
  HKDF.expand cs.kdf_hash prk info len

let kdf_extract cs key data =
  if not (Seq.length key <= Hash.max_input_length cs.kdf_hash && Seq.length key + Hash.block_length cs.kdf_hash < pow2 32) then
    fail "kdf_extract_dyn: bad key size"
  else if not (Seq.length data + Hash.block_length (cs.kdf_hash) <= Hash.max_input_length (cs.kdf_hash)) then
    fail "kdf_extract_dyn: bad data size"
  else
    return (HKDF.extract (cs.kdf_hash) key data)

let kdf_expand cs prk info len =
  if not (Hash.hash_length cs.kdf_hash <= Seq.length prk) then
    fail "kdf_expand_dyn: prk too small"
  else if not (Seq.length prk <= Hash.max_input_length cs.kdf_hash && Seq.length prk + Hash.block_length cs.kdf_hash < pow2 32) then
    fail "kdf_expand_dyn: prk too long"
  else if not (Hash.hash_length cs.kdf_hash + Seq.length info + 1 + Hash.block_length cs.kdf_hash <= Hash.max_input_length cs.kdf_hash) then
    fail "kdf_expand_dyn: info too long"
  else if not (len <= 255 * Hash.hash_length cs.kdf_hash) then
    fail "kdf_expand_dyn: len too high"
  else
    return (HKDF.expand cs.kdf_hash prk info len)

(*** HPKE ***)

let hpke_public_key_length cs = HPKE.size_dh_public (ciphersuite_to_hpke_ciphersuite cs)
let hpke_private_key_length cs = HPKE.size_dh_key (ciphersuite_to_hpke_ciphersuite cs)
let hpke_kem_output_length cs = HPKE.size_dh_public (ciphersuite_to_hpke_ciphersuite cs)

let hpke_gen_keypair cs ikm =
  if not (Seq.length ikm <= HPKE.max_length_dkp_ikm (cs.kem_hash)) then
    fail "hpke_gen_keypair: ikm too long"
  else (
    match HPKE.derive_key_pair (ciphersuite_to_hpke_ciphersuite cs) ikm with
    | None -> fail "hpke_gen_keypair: HPKE.derive_key_pair failed"
    | Some (sk, pk) -> return (sk, pk)
  )

let hpke_encrypt cs pkR info ad plaintext rand =
  match HPKE.derive_key_pair (ciphersuite_to_hpke_ciphersuite cs) rand with
  | None -> fail "hpke_encrypt: HPKE.derive_key_pair failed"
  | Some (skE, _) -> (
    let pkR = HPKE.deserialize_public_key (ciphersuite_to_hpke_ciphersuite cs) pkR in
    if not (Seq.length info <= HPKE.max_length_info cs.kdf_hash) then
      fail "hpke_encrypt: info too long"
    else if not (Seq.length ad <= AEAD.max_length cs.aead) then
      fail "hpke_encrypt: ad too long"
    else if not (Seq.length plaintext <= AEAD.max_length cs.aead) then
      fail "hpke_encrypt: plaintext too long"
    else (
      match HPKE.sealBase (ciphersuite_to_hpke_ciphersuite cs) skE pkR info ad plaintext with
      | None -> fail "hpke_encrypt: HPKE.sealBase failed"
      | Some (kem_output, ciphertext) -> return (kem_output, ciphertext)
    )
  )

let hpke_decrypt cs enc skR info ad ciphertext =
  if not (Seq.length info <= HPKE.max_length_info cs.kdf_hash) then
    fail "hpke_decrypt: info too long"
  else if not (Seq.length ad <= AEAD.max_length cs.aead) then
    fail "hpke_decrypt: ad too long"
  else if not (Seq.length ciphertext >= AEAD.tag_length cs.aead) then
    fail "hpke_decrypt: ciphertext too short"
  else if not (Seq.length ciphertext <= AEAD.cipher_max_length cs.aead) then
    fail "hpke_decrypt: ciphertext too short"
  else (
    match HPKE.openBase (ciphersuite_to_hpke_ciphersuite cs) enc skR info ad ciphertext with
    | None -> fail "hpke_decrypt: HPKE.openBase failed"
    | Some res -> return res
  )

(*** Signature ***)

let sign_public_key_length cs =
  match cs.signature with
  | Ed_25519 -> 32
  | P_256 -> 0 //TODO

let sign_private_key_length cs =
  match cs.signature with
  | Ed_25519 -> 32
  | P_256 -> 0 //TODO

let sign_nonce_length cs =
  match cs.signature with
  | Ed_25519 -> 0
  | P_256 -> 0 //TODO

let sign_signature_length cs =
  match cs.signature with
  | Ed_25519 -> 64
  | P_256 -> 0 //TODO


let sign_sign cs sk msg rand =
  match cs.signature with
  | Ed_25519 ->
    if not (64 + Seq.length msg <= max_size_t) then
      fail "sign_sign: msg too long"
    else
      return (Ed25519.sign sk msg)
  | P_256 -> fail "sign_sign: P_256 not implemented"

let sign_verify cs pk msg signature =
  match cs.signature with
  | Ed_25519 ->
    if not (64 + Seq.length msg <= max_size_t) then
      false
    else
      Ed25519.verify pk msg signature
  | P_256 -> false //TODO

(*** AEAD ***)

let aead_nonce_length cs =
  HPKE.size_aead_nonce (ciphersuite_to_hpke_ciphersuite cs)

let aead_key_length cs =
  AEAD.key_length (cs.aead)

let aead_encrypt cs key nonce ad plaintext =
  if not (Seq.length ad <= AEAD.max_length (cs.aead)) then
    fail "aead_encrypt: ad too long"
  else if not (Seq.length plaintext <= AEAD.max_length (cs.aead)) then
    fail "aead_encrypt: plaintext too long"
  else
    return (AEAD.encrypt #(cs.aead) key nonce ad plaintext)

let aead_decrypt cs key nonce ad ciphertext =
  if not (Seq.length ad <= AEAD.max_length (cs.aead)) then
    fail "aead_decrypt: ad too long"
  else if not (AEAD.tag_length (cs.aead) <= Seq.length ciphertext) then
    fail "aead_decrypt: ciphertext too short"
  else if not ( Seq.length ciphertext <= AEAD.max_length (cs.aead) + AEAD.tag_length (cs.aead)) then
    fail "aead_decrypt: ciphertext too long"
  else (
    result <-- from_option "aead_decrypt: AEAD.decrypt failed" (AEAD.decrypt #(cs.aead) key nonce ad ciphertext);
    return (result <: bytes)
  )

(*** HMAC ***)

let hmac_hmac cs key data =
  if not (let l = Seq.length key in l < Hash.max_input_length cs.kdf_hash && l + Hash.block_length cs.kdf_hash < pow2 32) then (
    fail "hmac_hmac: wrong key size"
  ) else if not (Seq.length data + Hash.block_length cs.kdf_hash < Hash.max_input_length cs.kdf_hash) then (
    fail "hmac_hmac: data too long"
  ) else (
    return (HMAC.hmac cs.kdf_hash key data)
  )

(*** String to bytes ***)

let string_to_bytes s =
  let open FStar.String in
  let open FStar.Char in
  let open FStar.List.Tot in
  let rec aux (l:list char{for_all (fun x -> int_of_char x < 256) l /\ length l < max_size_t}): lbytes (length l) =
    match l with
    | [] -> bytes_empty
    | h::t -> FStar.Seq.append (create 1 (u8 (int_of_char h))) (aux t)
  in
  aux (list_of_string s)
