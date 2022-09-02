module MLS.Symbolic

open Comparse
open MLS.Crypto
open ComparseGlue
open MLS.NetworkTypes
open MLS.Symbolic.SplitPredicate
open MLS.Result

#push-options "--fuel 1 --ifuel 1"

(*** Typeclass instantiation on DY* ***)

val dy_bytes: eqtype
let dy_bytes = CryptoLib.bytes

/// At this time, DY* doesn't expose lengths for cryptographic functions. Therefore we assume them here.
/// Assuming them is sound since no similar properties are exposed by DY*.
/// This will have to be cleaned up the day DY* exposes lengths for cryptographic functions.

assume val dy_hash_length: n:nat{1 <= n /\ n < 256}
assume val dy_hash_length_lemma: b:dy_bytes -> Lemma (length (CryptoLib.hash b) == dy_hash_length)

assume val dy_kdf_length: nat
assume val dy_kdf_length_lemma: key:dy_bytes -> data:dy_bytes -> Lemma (length (CryptoLib.extract key data) == dy_kdf_length)

assume val dy_sign_public_key_length: nat
assume val dy_sign_private_key_length: nat
assume val dy_sign_nonce_length: nat
assume val dy_sign_signature_length: n:nat{n < 256}
assume val dy_sign_signture_length_lemma: sk:dy_bytes -> rand:dy_bytes -> msg:dy_bytes -> Lemma
  (requires length sk == dy_sign_private_key_length /\ length rand == dy_sign_nonce_length)
  (ensures length (CryptoLib.sign sk rand msg) == dy_sign_signature_length)
assume val dy_sign_public_key_length_lemma: sk:dy_bytes -> Lemma
  (requires length sk == dy_sign_private_key_length)
  (ensures length (CryptoLib.vk sk) == dy_sign_public_key_length)

assume val dy_aead_nonce_length: n:nat{4 <= n}
assume val dy_aead_key_length: nat

assume val dy_hmac_length: n:nat{n < 256}
assume val dy_hmac_length_lemma: key:dy_bytes -> data:dy_bytes -> Lemma (length (CryptoLib.mac key data) == dy_hmac_length)

val dy_bytes_has_crypto: available_ciphersuite -> crypto_bytes dy_bytes
let dy_bytes_has_crypto acs = {
  base = dy_bytes_like;

  bytes_hasEq = ();

  ciphersuite = acs;

  hash_length = dy_hash_length;
  hash_length_bound = ();
  hash_max_input_length = pow2 256; //infinity!
  hash_hash = (fun buf ->
    dy_hash_length_lemma buf;
    CryptoLib.hash buf
  );

  kdf_length = dy_kdf_length;
  kdf_extract = (fun key data ->
    dy_kdf_length_lemma key data;
    return (CryptoLib.extract key data)
  );
  kdf_expand = (fun prk info len ->
    // TODO: expose the length in DY*
    // (used in TreeKEM, TreeDEM)
    admit();
    return (CryptoLib.expand prk info)
  );

  hpke_public_key_length = magic();
  hpke_public_key_length_bound = magic();
  hpke_private_key_length = magic();
  hpke_private_key_length_bound = magic();
  hpke_kem_output_length = magic();
  hpke_gen_keypair = (fun ikm ->
    // TODO: actually implement HPKE in DY*
    // (used in TreeKEM)
    admit();
    return (ikm, CryptoLib.pk ikm)
  );
  hpke_encrypt = (fun pkR info ad plaintext rand ->
    // TODO: actually implement HPKE in DY*
    // (no info/ad nor kem output)
    // (used in TreeKEM)
    admit();
    return (CryptoLib.pke_enc pkR rand plaintext, CryptoLib.empty)
  );
  hpke_decrypt = (fun enc skR info ad ciphertext ->
    // TODO: actually implement HPKE in DY*
    // (no info/ad nor kem output)
    // (used in TreeKEM)
    match CryptoLib.pke_dec skR ciphertext with
    | SecrecyLabels.Success res -> return res
    | SecrecyLabels.Error e -> error e
  );

  sign_public_key_length = dy_sign_public_key_length;
  sign_private_key_length = dy_sign_private_key_length;
  sign_nonce_length = dy_sign_nonce_length;
  sign_signature_length = dy_sign_signature_length;
  sign_signature_length_bound = ();
  sign_gen_keypair = (fun rand ->
    dy_sign_public_key_length_lemma rand;
    (CryptoLib.vk rand, rand)
  );
  sign_max_input_length = pow2 256; //infinity!
  sign_sign = (fun sk msg rand ->
    dy_sign_signture_length_lemma sk rand msg;
    CryptoLib.sign sk rand msg
  );
  sign_verify = (fun pk msg signature ->
    CryptoLib.verify pk msg signature
  );

  aead_nonce_length = dy_aead_nonce_length;
  aead_nonce_length_bound = ();
  aead_key_length = dy_aead_key_length;
  aead_encrypt = (fun key nonce ad plaintext ->
    return (CryptoLib.aead_enc key nonce plaintext ad)
  );
  aead_decrypt = (fun key nonce ad ciphertext ->
    match CryptoLib.aead_dec key nonce ciphertext ad with
    | SecrecyLabels.Success res -> return res
    | SecrecyLabels.Error e -> error e
  );

  hmac_length = dy_hmac_length;
  hmac_length_bound = ();
  hmac_hmac = (fun key data ->
    dy_hmac_length_lemma key data;
    return (CryptoLib.mac key data)
  );

  string_to_bytes = (fun s ->
    CryptoLib.string_to_bytes_len s;
    CryptoLib.string_to_bytes s
  );

  unsafe_split = (fun buf i ->
    admit()
  );
  xor = (fun b1 b2 ->
    admit()
  );
}

instance crypto_dy_bytes: crypto_bytes dy_bytes = dy_bytes_has_crypto AC_mls_128_dhkemx25519_chacha20poly1305_sha256_ed25519

(*** Abbreviations for DY* functions ***)

val principal: Type0
let principal = SecrecyLabels.principal

val timestamp: Type0
let timestamp = SecrecyLabels.timestamp

// In universe 1 because it contains predicates
val global_usage: Type u#1
let global_usage = LabeledCryptoAPI.global_usage

val label: Type0
let label = SecrecyLabels.label

val id: Type0
let id = SecrecyLabels.id

// Exposing the constructor directly would have been nice, but that's not possible
val p_id: principal -> id
let p_id p = SecrecyLabels.P p

val ps_id: principal -> nat -> id
let ps_id p s = SecrecyLabels.S p s

val psv_id: principal -> nat -> nat -> id
let psv_id p s v = SecrecyLabels.V p s v

val public: label
let public = SecrecyLabels.public

val readers: list id -> label
let readers l = SecrecyLabels.readers l

val usage: Type0
let usage = CryptoLib.usage

val sig_usage: string -> usage
let sig_usage usg = CryptoLib.sig_usage usg

val can_flow: ts:timestamp -> from:label -> to:label -> prop
let can_flow = LabeledCryptoAPI.can_flow

// Why a dollar? Because time is money!
let (<$) (t1:timestamp) (t2:timestamp) = SecrecyLabels.later_than t2 t1

val get_usage: global_usage -> dy_bytes -> (option usage)
let get_usage p b = LabeledCryptoAPI.get_usage p.key_usages b

val get_label: global_usage -> dy_bytes -> label
let get_label p b = LabeledCryptoAPI.get_label p.key_usages b

val is_valid: p:global_usage -> i:timestamp -> bytes_compatible_pre dy_bytes
let is_valid p i = LabeledCryptoAPI.is_valid p i

val is_labeled: global_usage -> label -> timestamp -> dy_bytes -> prop
let is_labeled p l i b = is_valid p i b /\ get_label p b == l

val has_usage: global_usage -> usage -> timestamp -> dy_bytes -> prop
let has_usage p u i b = LabeledCryptoAPI.has_usage p i b u

val is_secret: global_usage -> usage -> label -> timestamp -> dy_bytes -> prop
let is_secret p u l i b = LabeledCryptoAPI.is_secret p i b l u

val is_msg: global_usage -> label -> timestamp -> bytes_compatible_pre dy_bytes
let is_msg p l i = ComparseGlue.is_msg p l i

val is_publishable: global_usage -> timestamp -> bytes_compatible_pre dy_bytes
let is_publishable p i = is_msg p SecrecyLabels.public i

val is_verification_key: global_usage -> string -> timestamp -> label -> dy_bytes -> prop
let is_verification_key gu usg time sk_lab vk = LabeledCryptoAPI.is_verification_key gu time vk sk_lab usg (* convert to prop *) /\ True

val hash_hash_inj: b1:dy_bytes -> b2:dy_bytes -> Lemma (
  length b1 < hash_max_input_length #dy_bytes /\
  length b2 < hash_max_input_length #dy_bytes /\
  hash_hash b1 == hash_hash b2 ==>
  b1 == b2
  )
let hash_hash_inj b1 b2 = CryptoLib.hash_inj_lemma b1 b2

val is_corrupt: timestamp -> id -> prop
let is_corrupt time x = LabeledCryptoAPI.corrupt_id time x

val can_flow_to_public_implies_corruption: time:timestamp -> x:id -> Lemma
  (requires (can_flow time (readers [x]) public))
  (ensures is_corrupt time x)
let can_flow_to_public_implies_corruption time x = LabeledCryptoAPI.can_flow_to_public_implies_corruption time x

(*** Labeled signature predicate ***)

val get_mls_label_inj: l1:valid_label -> l2:valid_label -> Lemma
  (requires get_mls_label #dy_bytes l1 == get_mls_label #dy_bytes l2)
  (ensures l1 == l2)
let get_mls_label_inj l1 l2 =
  let bytes_mls = CryptoLib.string_to_bytes "MLS 1.0 " in
  let bytes_label1 = CryptoLib.string_to_bytes l1 in
  let bytes_label2 = CryptoLib.string_to_bytes l2 in
  CryptoLib.split_at_raw_concat_lemma bytes_mls bytes_label1;
  CryptoLib.split_at_raw_concat_lemma bytes_mls bytes_label2;
  CryptoLib.string_to_bytes_lemma l1;
  CryptoLib.string_to_bytes_lemma l2

let split_sign_pred_func: split_predicate_input_values = {
  labeled_data_t = (string & timestamp & dy_bytes & dy_bytes);
  label_t = valid_label;
  encoded_label_t = dy_bytes;
  raw_data_t = (string & timestamp & dy_bytes & dy_bytes);

  decode_labeled_data = (fun (usg, time, key, data) -> (
    match parse (sign_content_nt dy_bytes) data with
    | Some ({label; content}) -> Some (label, (usg, time, key, content))
    | None -> None
  ));

  encode_label = get_mls_label #dy_bytes;
  encode_label_inj = get_mls_label_inj;
}

let sign_pred = usage:string -> timestamp -> key:dy_bytes -> msg:dy_bytes -> prop

val sign_pred_to_local_pred: sign_pred -> local_pred split_sign_pred_func
let sign_pred_to_local_pred spred (usg, time, key, msg) =
  spred usg time key msg

val global_usage_to_global_pred: global_usage -> global_pred split_sign_pred_func
let global_usage_to_global_pred gu (usg, time, key, msg) =
  gu.usage_preds.can_sign time usg key msg (* convert to prop *) /\ True

val has_sign_pred: global_usage -> valid_label -> sign_pred -> prop
let has_sign_pred gu lab spred =
  has_local_pred split_sign_pred_func (global_usage_to_global_pred gu) lab (sign_pred_to_local_pred spred)

val get_mls_label_is_valid: gu:global_usage -> time:timestamp -> lab:valid_label -> Lemma (is_valid gu time (get_mls_label #dy_bytes lab))
let get_mls_label_is_valid gu time lab =
  LabeledCryptoAPI.string_to_bytes_lemma #gu #time "MLS 1.0 ";
  LabeledCryptoAPI.string_to_bytes_lemma #gu #time lab;
  let bytes_mls = string_to_bytes #dy_bytes "MLS 1.0 " in
  let bytes_label = string_to_bytes #dy_bytes lab in
  LabeledCryptoAPI.raw_concat_lemma #gu #time #SecrecyLabels.public bytes_mls bytes_label

// We can omit the `is_publishable` disjunction in the precondition,
// because it will never be used inside a protocol security proof.
// It can however be used to demonstrate attacks, but that is not our goal.
val sign_with_label_valid: gu:global_usage -> spred:sign_pred -> usg:string -> time:timestamp -> sk:sign_private_key dy_bytes -> lab:valid_label -> msg:mls_bytes dy_bytes -> nonce:sign_nonce dy_bytes -> Lemma
  (requires
    sign_with_label_pre #dy_bytes lab (length #dy_bytes msg) /\
    is_valid gu time sk /\ ( (* is_publishable gu time sk \/ *) get_usage gu sk == Some (sig_usage usg)) /\
    is_valid gu time nonce /\
    get_label gu sk == get_label gu nonce /\
    is_valid gu time msg /\
    has_sign_pred gu lab spred /\ (exists time_sig. time_sig <$ time /\ spred usg time_sig (CryptoLib.vk sk) msg)
  )
  (ensures is_valid gu time (sign_with_label sk lab msg nonce))
let sign_with_label_valid gu spred usg time sk lab msg nonce =
  assert_norm (forall msg usg time key. global_usage_to_global_pred gu (usg, time, key, msg) <==> gu.usage_preds.can_sign time usg key msg); //???
  get_mls_label_is_valid gu time lab;
  let sign_content: sign_content_nt dy_bytes = {
    label = get_mls_label #dy_bytes lab;
    content = msg;
  } in
  serialize_pre_lemma (sign_content_nt dy_bytes) (is_valid gu time) sign_content;
  parse_serialize_inv_lemma #dy_bytes (sign_content_nt dy_bytes) sign_content;
  let sign_content_bytes: dy_bytes = serialize (sign_content_nt dy_bytes) sign_content in
  LabeledCryptoAPI.sign_lemma #gu #time #(get_label gu sk) #SecrecyLabels.private_label sk nonce sign_content_bytes

val verify_with_label_is_valid: gu:global_usage -> spred:sign_pred -> usg:string -> sk_label:label -> time:timestamp -> vk:sign_public_key dy_bytes -> lab:valid_label -> content:mls_bytes dy_bytes -> signature:sign_signature dy_bytes -> Lemma
  (requires
    has_sign_pred gu lab spred /\
    is_verification_key gu usg time sk_label vk /\
    is_valid gu time content /\
    is_valid gu time signature /\
    sign_with_label_pre #dy_bytes lab (length #dy_bytes content) /\
    verify_with_label vk lab content signature
  )
  (ensures can_flow time sk_label public \/ (exists time_sig. time_sig <$ time /\ spred usg time_sig vk content))
let verify_with_label_is_valid gu spred usg sk_label time vk lab content signature =
  assert_norm (forall msg usg time key. global_usage_to_global_pred gu (usg, time, key, msg) <==> gu.usage_preds.can_sign time usg key msg); //???
  get_mls_label_is_valid gu time lab;
  let sign_content: sign_content_nt dy_bytes = {
    label = get_mls_label #dy_bytes lab;
    content = content;
  } in
  serialize_pre_lemma (sign_content_nt dy_bytes) (is_valid gu time) sign_content;
  parse_serialize_inv_lemma #dy_bytes (sign_content_nt dy_bytes) sign_content;
  let sign_content_bytes: dy_bytes = serialize (sign_content_nt dy_bytes) sign_content in
  LabeledCryptoAPI.verify_lemma #gu #time #SecrecyLabels.private_label #SecrecyLabels.private_label vk sign_content_bytes signature

val label_sign_pred_to_label_local_pred: valid_label & sign_pred -> valid_label & local_pred split_sign_pred_func
let label_sign_pred_to_label_local_pred (label, spred) =
  (label, sign_pred_to_local_pred spred)

val mk_can_sign: list (valid_label & sign_pred) -> timestamp -> string -> dy_bytes -> dy_bytes -> prop
let mk_can_sign l time usg key msg =
  mk_global_pred split_sign_pred_func (List.Tot.map label_sign_pred_to_label_local_pred l) (usg, time, key, msg)

val mk_can_sign_correct: gu:global_usage -> lspred:list (valid_label & sign_pred) -> lab:valid_label -> spred:sign_pred -> Lemma
  (requires
    gu.usage_preds.can_sign == mk_can_sign lspred /\
    List.Tot.no_repeats_p (List.Tot.map fst lspred) /\
    List.Tot.memP (lab, spred) lspred
  )
  (ensures has_sign_pred gu lab spred)
let mk_can_sign_correct gu lspred lab spred =
  let open MLS.MiscLemmas in
  assert_norm (forall msg usg time key. global_usage_to_global_pred gu (usg, time, key, msg) <==> gu.usage_preds.can_sign time usg key msg); //???
  memP_map (lab, spred) label_sign_pred_to_label_local_pred lspred;
  FStar.Classical.forall_intro_2 (index_map label_sign_pred_to_label_local_pred);
  FStar.Classical.forall_intro_2 (index_map (fst #valid_label #sign_pred));
  FStar.Classical.forall_intro_2 (index_map (fst #valid_label #(local_pred split_sign_pred_func)));
  List.Tot.index_extensionality (List.Tot.map fst lspred) (List.Tot.map fst (List.Tot.map label_sign_pred_to_label_local_pred lspred));
  mk_global_pred_correct split_sign_pred_func (List.Tot.map label_sign_pred_to_label_local_pred lspred) lab (sign_pred_to_local_pred spred)
