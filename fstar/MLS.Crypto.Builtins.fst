module MLS.Crypto.Builtins

open FStar.Mul

open Lib.IntTypes

open Comparse
open MLS.Result

module DH = Spec.Agile.DH
module AEAD = Spec.Agile.AEAD
module Hash = Spec.Agile.Hash
module HKDF = Spec.Agile.HKDF
module HPKE = Spec.Agile.HPKE
module Ed25519 = Spec.Ed25519
module HMAC = Spec.Agile.HMAC

(*** Concrete instance ***)

noeq type concrete_ciphersuite_ = {
  kem_dh:  DH.algorithm;
  kem_hash: Hash.algorithm;
  aead: AEAD.alg;
  kdf_hash: Hash.algorithm;
}

val is_valid_concrete_ciphersuite_: concrete_ciphersuite_ -> bool
let is_valid_concrete_ciphersuite_ cs =
  HPKE.is_valid_hash (cs.kem_hash) &&
  HPKE.is_valid_kem (cs.kem_dh, cs.kem_hash) &&
  HPKE.is_valid_aead (HPKE.Seal cs.aead) &&
  HPKE.is_valid_hash (cs.kdf_hash)

let concrete_ciphersuite = cs:concrete_ciphersuite_{is_valid_concrete_ciphersuite_ cs}

val concrete_ciphersuite_to_hpke_ciphersuite: concrete_ciphersuite -> HPKE.ciphersuite
let concrete_ciphersuite_to_hpke_ciphersuite cs =
  (cs.kem_dh, cs.kem_hash, HPKE.Seal cs.aead, cs.kdf_hash)

//Copy-pasted from `crypto_bytes` typeclass
noeq type signature_functions (bytes:Type0) {|bytes_like bytes|} = {
  sign_public_key_length: nat;
  sign_private_key_length: nat;
  sign_nonce_length: nat;
  sign_signature_length: nat;
  sign_gen_keypair: entropy:lbytes bytes sign_private_key_length -> result (lbytes bytes sign_public_key_length & lbytes bytes sign_private_key_length);
  sign_sign: lbytes bytes sign_private_key_length -> bytes -> entropy:lbytes bytes sign_nonce_length -> result (lbytes bytes sign_signature_length);
  sign_verify: lbytes bytes sign_public_key_length -> bytes -> lbytes bytes sign_signature_length -> bool;
}

let bytes_like_hacl_star_bytes = seq_u8_bytes_like

val ed25519_signature_functions: signature_functions hacl_star_bytes #bytes_like_hacl_star_bytes
let ed25519_signature_functions = {
  sign_public_key_length = 32;
  sign_private_key_length = 32;
  sign_nonce_length = 0;
  sign_signature_length = 64;
  sign_gen_keypair = (fun rand ->
    return (Ed25519.secret_to_public rand, rand)
  );
  sign_sign = (fun sk msg rand ->
    if not (64 + Seq.length msg <= max_size_t) then
      internal_failure "sign_sign: msg too long"
    else
      return (Ed25519.sign sk (msg <: hacl_star_bytes))
  );
  sign_verify = (fun pk msg signature ->
    if not (64 + Seq.length msg <= max_size_t) then
      false
    else
      Ed25519.verify pk msg signature
  );
}

//TODO
val p256_signature_functions: signature_functions hacl_star_bytes #bytes_like_hacl_star_bytes
let p256_signature_functions = {
  sign_public_key_length = 0;
  sign_private_key_length = 0;
  sign_nonce_length = 0;
  sign_signature_length = 0;
  sign_gen_keypair = (fun rand ->
    internal_failure "sign_gen_keypair: P_256 not implemented"
  );
  sign_sign = (fun sk msg rand ->
    internal_failure "sign_sign: P_256 not implemented"
  );
  sign_verify = (fun pk msg signature ->
    false
  );
}


val available_ciphersuite_to_ciphersuite_t: available_ciphersuite -> concrete_ciphersuite & signature_functions hacl_star_bytes #bytes_like_hacl_star_bytes
let available_ciphersuite_to_concrete_ciphersuite cs =
  match cs with
  | AC_mls_128_dhkemx25519_aes128gcm_sha256_ed25519 -> ({
    kem_dh = DH.DH_Curve25519;
    kem_hash = Hash.SHA2_256;
    aead = AEAD.AES128_GCM;
    kdf_hash = Hash.SHA2_256;
  }, ed25519_signature_functions)
  | AC_mls_128_dhkemp256_aes128gcm_sha256_p256 -> ({
    kem_dh = DH.DH_P256;
    kem_hash = Hash.SHA2_256;
    aead = AEAD.AES128_GCM;
    kdf_hash = Hash.SHA2_256;
  }, p256_signature_functions)
  | AC_mls_128_dhkemx25519_chacha20poly1305_sha256_ed25519 -> ({
    kem_dh = DH.DH_Curve25519;
    kem_hash = Hash.SHA2_256;
    aead = AEAD.CHACHA20_POLY1305;
    kdf_hash = Hash.SHA2_256;
  }, ed25519_signature_functions)


val hacl_string_to_bytes: s:string{b2t (normalize_term (string_is_ascii s))} -> lbytes hacl_star_bytes #bytes_like_hacl_star_bytes (String.strlen s)
let hacl_string_to_bytes s =
  let open FStar.String in
  let open FStar.Char in
  let open FStar.List.Tot in
  let rec aux (l:list char{for_all (fun x -> int_of_char x < 256) l}): lbytes hacl_star_bytes #seq_u8_bytes_like (length l) =
    match l with
    | [] -> empty #hacl_star_bytes #bytes_like_hacl_star_bytes
    | h::t -> FStar.Seq.append (Seq.create 1 (u8 (int_of_char h))) (aux t)
  in
  aux (list_of_string s)

private let rec map2 (#a1 #a2 #b: Type) (f:a1 -> a2 -> b) (l1:list a1) (l2:list a2): Pure (list b)
  (requires (List.Tot.length l1 == List.Tot.length l2))
  (ensures fun res -> List.Tot.length res == List.Tot.length l1) =
  match l1, l2 with
  | [], [] -> []
  | h1::t1, h2::t2 -> (f h1 h2)::map2 f t1 t2

let mk_concrete_crypto_bytes acs =
  let (cs, sign) = available_ciphersuite_to_concrete_ciphersuite acs in {
  base = seq_u8_bytes_like;

  bytes_hasEq = ();

  ciphersuite = acs;

  hash_length = Hash.hash_length cs.kdf_hash;
  hash_length_bound = ();
  hash_hash = (fun buf ->
    if not (Seq.length buf <= Hash.max_input_length (cs.kdf_hash)) then
      internal_failure "hash_hash: buf too long"
    else (
      return (Hash.hash cs.kdf_hash buf)
    )
  );

  kdf_length = Hash.hash_length cs.kdf_hash;
  kdf_extract = (fun key data ->
    if not (Seq.length key <= Hash.max_input_length cs.kdf_hash && Seq.length key + Hash.block_length cs.kdf_hash < pow2 32) then
      internal_failure "kdf_extract: bad key size"
    else if not (Seq.length data + Hash.block_length (cs.kdf_hash) <= Hash.max_input_length (cs.kdf_hash)) then
      internal_failure "kdf_extract: bad data size"
    else
      return (HKDF.extract (cs.kdf_hash) key data)
  );
  kdf_expand = (fun prk info len ->
    if not (Hash.hash_length cs.kdf_hash <= Seq.length prk) then
      internal_failure "kdf_expand: prk too small"
    else if not (Seq.length prk <= Hash.max_input_length cs.kdf_hash && Seq.length prk + Hash.block_length cs.kdf_hash < pow2 32) then
      internal_failure "kdf_expand: prk too long"
    else if not (Hash.hash_length cs.kdf_hash + Seq.length info + 1 + Hash.block_length cs.kdf_hash <= Hash.max_input_length cs.kdf_hash) then
      internal_failure "kdf_expand: info too long"
    else if not (len <= 255 * Hash.hash_length cs.kdf_hash) then
      internal_failure "kdf_expand: len too high"
    else
      return (HKDF.expand cs.kdf_hash prk info len)
  );

  hpke_public_key_length = HPKE.size_dh_public (concrete_ciphersuite_to_hpke_ciphersuite cs);
  hpke_public_key_length_bound = ();
  hpke_private_key_length = HPKE.size_dh_key (concrete_ciphersuite_to_hpke_ciphersuite cs);
  hpke_private_key_length_bound = ();
  hpke_kem_output_length = HPKE.size_dh_public (concrete_ciphersuite_to_hpke_ciphersuite cs);
  hpke_gen_keypair = (fun ikm ->
    if not (Seq.length ikm <= HPKE.max_length_dkp_ikm (cs.kem_hash)) then
      internal_failure "hpke_gen_keypair: ikm too long"
    else (
      match HPKE.derive_key_pair (concrete_ciphersuite_to_hpke_ciphersuite cs) ikm with
      | None -> internal_failure "hpke_gen_keypair: HPKE.derive_key_pair failed"
      | Some (sk, pk) -> return (sk, pk)
    )
  );
  hpke_encrypt = (fun pkR info ad plaintext rand ->
    match HPKE.derive_key_pair (concrete_ciphersuite_to_hpke_ciphersuite cs) rand with
    | None -> internal_failure "hpke_encrypt: HPKE.derive_key_pair failed"
    | Some (skE, _) -> (
      let pkR = HPKE.deserialize_public_key (concrete_ciphersuite_to_hpke_ciphersuite cs) pkR in
      if not (Seq.length info <= HPKE.max_length_info cs.kdf_hash) then
        internal_failure "hpke_encrypt: info too long"
      else if not (Seq.length ad <= AEAD.max_length cs.aead) then
        internal_failure "hpke_encrypt: ad too long"
      else if not (Seq.length plaintext <= AEAD.max_length cs.aead) then
        internal_failure "hpke_encrypt: plaintext too long"
      else (
        match HPKE.sealBase (concrete_ciphersuite_to_hpke_ciphersuite cs) skE pkR info ad plaintext with
        | None -> internal_failure "hpke_encrypt: HPKE.sealBase failed"
        | Some (kem_output, ciphertext) -> return (kem_output, ciphertext)
      )
    )
  );
  hpke_decrypt = (fun enc skR info ad ciphertext ->
    if not (Seq.length info <= HPKE.max_length_info cs.kdf_hash) then
      internal_failure "hpke_decrypt: info too long"
    else if not (Seq.length ad <= AEAD.max_length cs.aead) then
      internal_failure "hpke_decrypt: ad too long"
    else if not (Seq.length ciphertext >= AEAD.tag_length cs.aead) then
      error "hpke_decrypt: ciphertext too short"
    else if not (Seq.length ciphertext <= AEAD.cipher_max_length cs.aead) then
      error "hpke_decrypt: ciphertext too long"
    else (
      match HPKE.openBase (concrete_ciphersuite_to_hpke_ciphersuite cs) enc skR info ad ciphertext with
      | None -> error "hpke_decrypt: HPKE.openBase failed"
      | Some res -> return res
    )
  );

  sign_public_key_length = sign.sign_public_key_length;
  sign_private_key_length = sign.sign_private_key_length;
  sign_nonce_length = sign.sign_nonce_length;
  sign_signature_length = sign.sign_signature_length;
  sign_gen_keypair = sign.sign_gen_keypair;
  sign_sign = sign.sign_sign;
  sign_verify = sign.sign_verify;

  aead_nonce_length = HPKE.size_aead_nonce (concrete_ciphersuite_to_hpke_ciphersuite cs);
  aead_nonce_length_bound = ();
  aead_key_length = AEAD.key_length (cs.aead);
  aead_encrypt = (fun key nonce ad plaintext ->
    if not (Seq.length ad <= AEAD.max_length (cs.aead)) then
      internal_failure "aead_encrypt: ad too long"
    else if not (Seq.length plaintext <= AEAD.max_length (cs.aead)) then
      internal_failure "aead_encrypt: plaintext too long"
    else
      return (AEAD.encrypt #(cs.aead) key nonce ad plaintext)
  );
  aead_decrypt = (fun key nonce ad ciphertext ->
    if not (Seq.length ad <= AEAD.max_length (cs.aead)) then
      internal_failure "aead_decrypt: ad too long"
    else if not (AEAD.tag_length (cs.aead) <= Seq.length ciphertext) then
      error "aead_decrypt: ciphertext too short"
    else if not ( Seq.length ciphertext <= AEAD.max_length (cs.aead) + AEAD.tag_length (cs.aead)) then
      error "aead_decrypt: ciphertext too long"
    else (
      result <-- from_option "aead_decrypt: AEAD.decrypt failed" (AEAD.decrypt #(cs.aead) key nonce ad ciphertext);
      return (result <: hacl_star_bytes)
    )
  );

  hmac_length = Hash.hash_length cs.kdf_hash;
  hmac_hmac = (fun key data ->
    if not (let l = Seq.length key in l < Hash.max_input_length cs.kdf_hash && l + Hash.block_length cs.kdf_hash < pow2 32) then (
      internal_failure "hmac_hmac: wrong key size"
    ) else if not (Seq.length data + Hash.block_length cs.kdf_hash < Hash.max_input_length cs.kdf_hash) then (
      internal_failure "hmac_hmac: data too long"
    ) else (
      return (HMAC.hmac cs.kdf_hash key data)
    )
  );

  string_to_bytes = hacl_string_to_bytes;

  unsafe_split = (fun buf i ->
    Some?.v (split #hacl_star_bytes #bytes_like_hacl_star_bytes buf i)
  );
  xor = (fun b1 b2 ->
    Seq.seq_of_list (map2 (fun x1 x2 -> Lib.IntTypes.logxor #U8 #PUB x1 x2) (Seq.seq_to_list b1) (Seq.seq_to_list b2))
  );
}

(*** Randomness ***)

// We would like to have `| [] -> unit`, but that's not an option because of FStarLang/FStar#2594
let rec randomness bytes #bl l =
  match l with
  | [] -> n:nat{n == 0}
  | h::t -> lbytes bytes h & randomness bytes t

let mk_empty_randomness bytes #bl = 0
let mk_randomness #bytes #bl #head_size #tail_size (head_rand, tail_rand) =
  (head_rand, tail_rand)
let dest_randomness #bytes #bl #head_size #tail_size (head_rand, tail_rand) =
  (head_rand, tail_rand)
