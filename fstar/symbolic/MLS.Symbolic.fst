module MLS.Symbolic

open Comparse
open DY.Core
open MLS.Crypto
open MLS.Result

#set-options "--fuel 0 --ifuel 0"

(*** Typeclass instantiation on DY* ***)

#push-options "--ifuel 1"
val bytes_has_crypto_bytes: available_ciphersuite -> crypto_bytes bytes
let bytes_has_crypto_bytes acs = {
  base = DY.Lib.bytes_like_bytes;

  bytes_hasEq = ();

  ciphersuite = acs;

  hash_hash = (fun buf ->
    return (DY.Core.hash buf)
  );
  hash_max_input_length = pow2 256; //infinity!
  hash_hash_pre = (fun buf -> ());
  hash_output_length_bound = (fun buf -> assume(DY.Core.hash buf <> empty));
  hash_output_length = 32;
  hash_output_length_lemma = (fun buf -> assume(length (hash buf) == 32));

  kdf_length = 32;
  kdf_extract = (fun salt ikm ->
    assume(DY.Core.length (DY.Core.kdf_extract salt ikm) == 32);
    return (DY.Core.kdf_extract salt ikm)
  );
  kdf_expand = (fun prk info len ->
    if len = 0 then
      internal_failure "kdf_expand: len cannot be zero"
    else (
      assume(DY.Core.length (DY.Core.kdf_expand prk info len) == len);
      return (DY.Core.kdf_expand prk info len)
    )
  );

  hpke_public_key_length = 32;
  hpke_public_key_length_bound = ();
  hpke_private_key_length = 32;
  hpke_private_key_length_bound = ();
  hpke_kem_output_length = 32;
  hpke_gen_keypair = (fun ikm ->
    if not (length ikm = 32) then
      error "hpke_gen_keypair: ikm too big"
    else (
      assume(length (DY.Lib.HPKE.hpke_pk ikm) == 32);
      return (ikm, DY.Lib.HPKE.hpke_pk ikm)
    )
  );
  hpke_encrypt = (fun pkR info ad plaintext rand ->
    let (enc, cipher) = DY.Lib.HPKE.hpke_enc pkR rand plaintext info ad in
    assume(length enc == 32);
    return (enc, cipher)
  );
  hpke_decrypt = (fun enc skR info ad ciphertext ->
    from_option "hpke_decrypt failed" (DY.Lib.HPKE.hpke_dec skR (enc, ciphertext) info ad)
  );

  sign_gen_keypair_min_entropy_length = magic();
  sign_gen_keypair = (fun rand ->
    return (DY.Core.vk rand, rand)
  );
  sign_sign_min_entropy_length = magic();
  sign_sign = (fun sk msg rand ->
    return (DY.Core.sign sk rand msg)
  );
  sign_verify = (fun pk msg signature ->
    DY.Core.verify pk msg signature
  );

  aead_nonce_length = magic();
  aead_nonce_length_bound = magic();
  aead_key_length = magic();
  aead_encrypt = (fun key nonce ad plaintext ->
    return (DY.Core.aead_enc key nonce plaintext ad)
  );
  aead_decrypt = (fun key nonce ad ciphertext ->
    match DY.Core.aead_dec key nonce ciphertext ad with
    | Some res -> return res
    | None -> error "aead_decrypt: couldn't decrypt"
  );

  hmac_length = 32;
  hmac_length_bound = ();
  hmac_hmac = (fun key data ->
    let result = DY.Core.mac_compute key data in
    if length result <> 32 then
      internal_failure "bad hmac length"
    else
      return result
  );

  string_to_bytes = (fun s ->
    (ps_whole_ascii_string.serialize s <: bytes)
  );

  unsafe_split = (fun buf i ->
    admit()
  );
  xor = (fun b1 b2 ->
    admit()
  );

  debug_bytes_to_string = (fun b -> "");
}
#pop-options

instance crypto_bytes_bytes: crypto_bytes bytes = bytes_has_crypto_bytes AC_mls_128_dhkemx25519_chacha20poly1305_sha256_ed25519

type mls_principal = {
  who: principal;
}

%splice [ps_mls_principal] (gen_parser (`mls_principal))

instance parseable_serializeable_bytes_mls_principal: parseable_serializeable bytes mls_principal =
  mk_parseable_serializeable ps_mls_principal

val mk_mls_sigkey_usage: principal -> usage
let mk_mls_sigkey_usage who =
  SigKey "MLS.LeafSignKey" (serialize _ { who })

#push-options "--ifuel 1"
val extract_result: #a:Type -> x:MLS.Result.result a -> traceful (option a)
let extract_result #a x =
  let open DY.Core in
  match x with
  | Success y -> return (Some y)
  | _ -> return None
#pop-options
