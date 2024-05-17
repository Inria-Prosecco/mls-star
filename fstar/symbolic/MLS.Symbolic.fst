module MLS.Symbolic

open Comparse
open DY.Core
open MLS.Crypto
open MLS.NetworkTypes
open DY.Lib.SplitPredicate
open MLS.Result

#push-options "--fuel 0 --ifuel 0"

(*** Typeclass instantiation on DY* ***)

val dy_bytes: eqtype
let dy_bytes = DY.Core.bytes

#push-options "--ifuel 1"
val dy_bytes_has_crypto: available_ciphersuite -> crypto_bytes dy_bytes
let dy_bytes_has_crypto acs = {
  base = DY.Lib.bytes_like_bytes;

  bytes_hasEq = ();

  ciphersuite = acs;

  hash_hash = (fun buf ->
    return (DY.Core.hash buf)
  );
  hash_max_input_length = pow2 256; //infinity!
  hash_hash_pre = (fun buf -> ());
  hash_output_length_bound = (fun buf -> assume(DY.Core.hash buf <> empty));

  kdf_length = magic();
  kdf_extract = (fun key data ->
    admit()
  );
  kdf_expand = (fun prk info len ->
    admit()
  );

  hpke_public_key_length = magic();
  hpke_public_key_length_bound = magic();
  hpke_private_key_length = magic();
  hpke_private_key_length_bound = magic();
  hpke_kem_output_length = magic();
  hpke_gen_keypair = (fun ikm ->
    admit()
  );
  hpke_encrypt = (fun pkR info ad plaintext rand ->
    admit()
  );
  hpke_decrypt = (fun enc skR info ad ciphertext ->
    admit()
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

  hmac_length = magic();
  hmac_length_bound = magic();
  hmac_hmac = (fun key data ->
    admit()
  );

  string_to_bytes = (fun s ->
    (ps_whole_ascii_string.serialize s <: dy_bytes)
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

instance crypto_dy_bytes: crypto_bytes dy_bytes = dy_bytes_has_crypto AC_mls_128_dhkemx25519_chacha20poly1305_sha256_ed25519

(*** Labeled signature predicate ***)

val get_mls_label_inj:
  l1:valid_label -> l2:valid_label ->
  Lemma
  (requires get_mls_label l1 == get_mls_label l2)
  (ensures l1 == l2)
let get_mls_label_inj l1 l2 =
  String.concat_injective "MLS 1.0 " "MLS 1.0 " l1 l2

type verif_key_t {|crypto_usages|} = vk:dy_bytes{SigKey? (get_signkey_usage vk)}

noeq
type mls_sign_pred {|crypto_usages|} = {
  pred: trace -> key:verif_key_t -> msg:dy_bytes -> prop;
  pred_later:
    tr1:trace -> tr2:trace ->
    key:verif_key_t -> msg:dy_bytes ->
    Lemma
    (requires pred tr1 key msg /\ tr1 <$ tr2)
    (ensures pred tr2 key msg)
  ;
}

let split_sign_pred_func {|crypto_usages|}: split_predicate_input_values = {
  local_pred = mls_sign_pred;
  global_pred = trace -> verif_key_t -> dy_bytes -> prop;

  raw_data_t = (trace & verif_key_t & dy_bytes);
  tagged_data_t = (trace & verif_key_t & dy_bytes);

  apply_local_pred = (fun pred (tr, vk, content) -> pred.pred tr vk content);
  apply_global_pred = (fun pred (tr, vk, msg) -> pred tr vk msg);
  mk_global_pred = (fun pred tr vk msg -> pred (tr, vk, msg));
  apply_mk_global_pred = (fun _ _ -> ());

  tag_t = valid_label;
  encoded_tag_t = mls_ascii_string;

  encode_tag = get_mls_label;
  encode_tag_inj = get_mls_label_inj;

  decode_tagged_data = (fun (tr, key, data) -> (
    match parse (sign_content_nt dy_bytes) data with
    | Some ({label; content}) -> Some (label, (tr, key, content))
    | None -> None
  ));
}

val has_sign_pred: crypto_invariants -> (valid_label & mls_sign_pred) -> prop
let has_sign_pred ci (lab, spred) =
  has_local_pred split_sign_pred_func (sign_pred #ci) (lab, spred)

#push-options "--z3rlimit 25"
val bytes_invariant_sign_with_label:
  {|ci:crypto_invariants|} -> spred:mls_sign_pred -> tr:trace ->
  sk:dy_bytes -> lab:valid_label -> msg:mls_bytes dy_bytes -> nonce:sign_nonce dy_bytes ->
  Lemma
  (requires
    bytes_invariant tr sk /\
    bytes_invariant tr nonce /\
    bytes_invariant tr msg /\
    SigKey? (get_usage sk) /\
    SigNonce? (get_usage nonce) /\
    (get_label sk) `can_flow tr` (get_label nonce) /\
    has_sign_pred ci (lab, spred) /\
    spred.pred tr (vk sk) msg
  )
  (ensures
    bytes_invariant tr (Success?.v (sign_with_label sk lab msg nonce)) /\
    (get_label (Success?.v (sign_with_label sk lab msg nonce))) `can_flow tr` (get_label msg)
  )
let bytes_invariant_sign_with_label #ci spred tr sk lab msg nonce =
  let sign_content: sign_content_nt dy_bytes = {
    label = get_mls_label lab;
    content = msg;
  } in
  serialize_wf_lemma (sign_content_nt dy_bytes) (bytes_invariant tr) sign_content;
  serialize_wf_lemma (sign_content_nt dy_bytes) (is_knowable_by (get_label msg) tr) sign_content;
  let sign_content_bytes = serialize _ sign_content in
  assert(split_sign_pred_func.decode_tagged_data (tr, (vk sk), sign_content_bytes) == Some (split_sign_pred_func.encode_tag lab, (tr, (vk sk), msg)))
#pop-options

val bytes_invariant_verify_with_label:
  {|ci:crypto_invariants|} -> spred:mls_sign_pred -> tr:trace ->
  vk:dy_bytes -> lab:valid_label -> content:mls_bytes dy_bytes -> signature:dy_bytes ->
  Lemma
  (requires
    has_sign_pred ci (lab, spred) /\
    bytes_invariant tr vk /\
    bytes_invariant tr content /\
    bytes_invariant tr signature /\
    verify_with_label vk lab content signature
  )
  (ensures
    (
      SigKey? (get_signkey_usage vk) ==>
      spred.pred tr vk content
    ) \/ (
      (get_signkey_label vk) `can_flow tr` public 
    )
  )
let bytes_invariant_verify_with_label #ci spred tr vk lab content signature =
  let sign_content: sign_content_nt dy_bytes = {
    label = get_mls_label lab;
    content = content;
  } in
  serialize_wf_lemma (sign_content_nt dy_bytes) (bytes_invariant tr) sign_content;
  let sign_content_bytes = serialize _ sign_content in
  if SigKey? (get_signkey_usage vk) then
    assert(split_sign_pred_func.decode_tagged_data (tr, vk, sign_content_bytes) == Some (split_sign_pred_func.encode_tag lab, (tr, vk, content)))
  else ()

val mk_sign_pred:
  {|crypto_usages|} ->
  list (valid_label & mls_sign_pred) ->
  trace -> verif_key_t -> dy_bytes ->
  prop
let mk_sign_pred l tr key msg =
  mk_global_pred split_sign_pred_func l tr key msg

#push-options "--ifuel 1"
val mk_sign_pred_later:
  {|crypto_usages|} ->
  lspred:list (valid_label & mls_sign_pred) ->
  tr1:trace -> tr2:trace ->
  vk:verif_key_t -> msg:dy_bytes ->
  Lemma
  (requires
    mk_sign_pred lspred tr1 vk msg /\
    tr1 <$ tr2
  )
  (ensures mk_sign_pred lspred tr2 vk msg)
let mk_sign_pred_later lspred tr1 tr2 vk msg =
  mk_global_pred_eq split_sign_pred_func lspred (tr1, vk, msg);
  eliminate exists tag spred raw_data.
    List.Tot.memP (tag, spred) lspred /\
    split_sign_pred_func.apply_local_pred spred raw_data /\
    split_sign_pred_func.decode_tagged_data (tr1, vk, msg) == Some (split_sign_pred_func.encode_tag tag, raw_data)
  returns mk_sign_pred lspred tr2 vk msg
  with _. (
    let Some (_, (_, _, msg_sub)) = split_sign_pred_func.decode_tagged_data (tr1, vk, msg) in
    spred.pred_later tr1 tr2 vk msg_sub;
    mk_global_pred_eq split_sign_pred_func lspred (tr2, vk, msg);
    assert(split_sign_pred_func.apply_local_pred spred (tr2, vk, msg_sub))
  )
#pop-options

#push-options "--ifuel 1"
val mk_sign_pred_correct:
  ci:crypto_invariants -> lspred:list (valid_label & mls_sign_pred) ->
  Lemma
  (requires
    sign_pred == mk_sign_pred lspred /\
    List.Tot.no_repeats_p (List.Tot.map fst lspred)
  )
  (ensures for_allP (has_sign_pred ci) lspred)
let mk_sign_pred_correct ci lspred =
  for_allP_eq (has_sign_pred ci) lspred;
  FStar.Classical.forall_intro_2 (FStar.Classical.move_requires_2 (mk_global_pred_correct split_sign_pred_func lspred))
#pop-options
