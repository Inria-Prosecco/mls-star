module Crypto


open Spec.Agile.HKDF
open FStar.Mul
open Spec.Hash.Definitions

open Spec.Agile.DH
open Spec.Agile.AEAD
open Spec.Agile.Hash
open Spec.Agile.HKDF
open HPKE

open Lib.Sequence
open Lib.ByteSequence
open Lib.IntTypes

module DH = Spec.Agile.DH
module AEAD = Spec.Agile.AEAD
module Hash = Spec.Agile.Hash
module HKDF = Spec.Agile.HKDF
module HPKE = HPKE

(*** Ciphersuite ***)

type ciphersuite_t = {
  kem_dh:  DH.algorithm;
  kem_hash: Hash.algorithm;
  aead: AEAD.alg;
  kdf_hash: Hash.algorithm;
  //TODO: signature
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
let split_randomness #n e len =
    (Seq.slice e len n, Seq.slice e 0 len)

(*** KDF ***)

val max_input_length_bound: a:Hash.hash_alg -> Lemma (pow2 61 - 1 <= max_input_length a)
let max_input_length_bound a =
  FStar.Math.Lemmas.pow2_le_compat 128 61;
  FStar.Math.Lemmas.pow2_le_compat 125 61;
  FStar.Math.Lemmas.pow2_le_compat 64 61

let kdf_length cs = hash_length cs.kdf_hash

let kdf_extract_tot cs key data =
  assert (block_length (cs.kdf_hash) <= 128);
  max_input_length_bound (cs.kdf_hash);
  assert_norm (pow2 60 < pow2 61 - 129); //==> Seq.length data + block_length a <= max_input_length a
  assert_norm (pow2 31 < pow2 32 - 128); //==> keysized (Seq.length key)
  assert_norm (pow2 31 < pow2 61 - 1); //==> keysized (Seq.length key)
  extract (cs.kdf_hash) key data

let kdf_expand_tot cs prk info len =
  assert(16 <= hash_length cs.kdf_hash);
  assert (hash_length cs.kdf_hash <= 64);
  assert (block_length cs.kdf_hash <= 128);
  max_input_length_bound cs.kdf_hash;
  assert_norm(pow2 60 < pow2 61 - 194); //==> hash_length a + Seq.length info + 1 + block_length a <= max_input_length a
  assert_norm(pow2 31 < pow2 32 - 128); //==> keysized (Seq.length prk)
  assert_norm(pow2 31 < pow2 61 - 1); //==> keysized (Seq.length prk)
  expand cs.kdf_hash prk info len

let kdf_extract cs key data =
  if not (Seq.length key <= max_input_length cs.kdf_hash && Seq.length key + block_length cs.kdf_hash < pow2 32) then
    Error "kdf_extract_dyn: bad key size"
  else if not (Seq.length data + block_length (cs.kdf_hash) <= max_input_length (cs.kdf_hash)) then
    Error "kdf_extract_dyn: bad data size"
  else
    Success (extract (cs.kdf_hash) key data)

let kdf_expand cs prk info len =
  if not (hash_length cs.kdf_hash <= Seq.length prk) then
    Error "kdf_expand_dyn: prk too small"
  else if not (Seq.length prk <= max_input_length cs.kdf_hash && Seq.length prk + block_length cs.kdf_hash < pow2 32) then
    Error "kdf_expand_dyn: prk too long"
  else if not (hash_length cs.kdf_hash + Seq.length info + 1 + block_length cs.kdf_hash <= max_input_length cs.kdf_hash) then
    Error "kdf_expand_dyn: info too long"
  else if not (len <= 255 * hash_length cs.kdf_hash) then
    Error "kdf_expand_dyn: len too high"
  else
    Success (expand cs.kdf_hash prk info len)

(*** HPKE ***)

let hpke_public_key_length cs = HPKE.size_dh_public (ciphersuite_to_hpke_ciphersuite cs)
let hpke_private_key_length cs = HPKE.size_dh_key (ciphersuite_to_hpke_ciphersuite cs)
let hpke_kem_output_length cs = HPKE.size_dh_public (ciphersuite_to_hpke_ciphersuite cs)

let hpke_gen_keypair cs ikm =
  if not (Seq.length ikm <= max_length_dkp_ikm (cs.kem_hash)) then
    Error "hpke_gen_keypair: ikm too long"
  else (
    match HPKE.derive_key_pair (ciphersuite_to_hpke_ciphersuite cs) ikm with
    | None -> Error "hpke_gen_keypair: HPKE.derive_key_pair failed"
    | Some (sk, pk) -> Success (sk, pk)
  )

let hpke_encrypt cs pkR info ad plaintext rand =
  match HPKE.derive_key_pair (ciphersuite_to_hpke_ciphersuite cs) rand with
  | None -> Error "hpke_encrypt: HPKE.derive_key_pair failed"
  | Some (skE, _) -> (
    let pkR = HPKE.deserialize_public_key (ciphersuite_to_hpke_ciphersuite cs) pkR in
    if not (Seq.length info <= max_length_info cs.kdf_hash) then
      Error "hpke_encrypt: info too long"
    else if not (Seq.length ad <= AEAD.max_length cs.aead) then
      Error "hpke_encrypt: ad too long"
    else if not (Seq.length plaintext <= AEAD.max_length cs.aead) then
      Error "hpke_encrypt: plaintext too long"
    else (
      match HPKE.sealBase (ciphersuite_to_hpke_ciphersuite cs) skE pkR info ad plaintext with
      | None -> Error "hpke_encrypt: HPKE.sealBase failed"
      | Some (kem_output, ciphertext) -> Success (kem_output, ciphertext)
    )
  )

let hpke_decrypt cs enc skR info ad ciphertext =
  if not (Seq.length info <= max_length_info cs.kdf_hash) then
    Error "hpke_decrypt: info too long"
  else if not (Seq.length ad <= AEAD.max_length cs.aead) then
    Error "hpke_decrypt: ad too long"
  else if not (Seq.length ciphertext >= AEAD.tag_length cs.aead) then
    Error "hpke_decrypt: plaintext too short"
  else (
    match HPKE.openBase (ciphersuite_to_hpke_ciphersuite cs) enc skR info ad ciphertext with
    | None -> Error "hpke_decrypt: HPKE.openBase failed"
    | Some res -> Success res
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
