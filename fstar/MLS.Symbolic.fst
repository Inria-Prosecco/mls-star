module MLS.Symbolic

open Comparse
open MLS.Crypto
open ComparseGlue
open MLS.NetworkTypes
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
let is_verification_key gu usg time sk_lab vk = True /\ LabeledCryptoAPI.is_verification_key gu time vk sk_lab usg

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

(*** Labeled signature predicate ***)

let sign_predicate = usage:string -> timestamp -> key:dy_bytes -> msg:dy_bytes -> prop

val has_sign_predicate: global_usage -> valid_label -> sign_predicate -> prop
let has_sign_predicate gu lab spred =
  forall (time:timestamp) (usg:string) (key:dy_bytes) (msg:dy_bytes).
    match (parse (sign_content_nt dy_bytes) msg) with
    | Some ({label; content;}) ->
      label == get_mls_label lab ==> (gu.usage_preds.can_sign time usg key msg <==> spred usg time key content)
    | None -> True

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
val sign_with_label_valid: gu:global_usage -> spred:sign_predicate -> usg:string -> time:timestamp -> sk:sign_private_key dy_bytes -> lab:valid_label -> msg:mls_bytes dy_bytes -> nonce:sign_nonce dy_bytes -> Lemma
  (requires
    sign_with_label_pre #dy_bytes lab (length #dy_bytes msg) /\
    is_valid gu time sk /\ ( (* is_publishable gu time sk \/ *) get_usage gu sk == Some (sig_usage usg)) /\
    is_valid gu time nonce /\
    get_label gu sk == get_label gu nonce /\
    is_valid gu time msg /\
    has_sign_predicate gu lab spred /\ (exists time_sig. time_sig <$ time /\ spred usg time_sig (CryptoLib.vk sk) msg)
  )
  (ensures is_valid gu time (sign_with_label sk lab msg nonce))
let sign_with_label_valid gu spred usg time sk lab msg nonce =
  get_mls_label_is_valid gu time lab;
  let sign_content: sign_content_nt dy_bytes = {
    label = get_mls_label #dy_bytes lab;
    content = msg;
  } in
  serialize_pre_lemma (sign_content_nt dy_bytes) (is_valid gu time) sign_content;
  parse_serialize_inv_lemma #dy_bytes (sign_content_nt dy_bytes) sign_content;
  let sign_content_bytes: dy_bytes = serialize (sign_content_nt dy_bytes) sign_content in
  LabeledCryptoAPI.sign_lemma #gu #time #(get_label gu sk) #SecrecyLabels.private_label sk nonce sign_content_bytes

val verify_with_label_is_valid: gu:global_usage -> spred:sign_predicate -> usg:string -> sk_label:label -> time:timestamp -> vk:sign_public_key dy_bytes -> lab:valid_label -> content:mls_bytes dy_bytes -> signature:sign_signature dy_bytes -> Lemma
  (requires
    has_sign_predicate gu lab spred /\
    is_verification_key gu usg time sk_label vk /\
    is_valid gu time content /\
    is_valid gu time signature /\
    sign_with_label_pre #dy_bytes lab (length #dy_bytes content) /\
    verify_with_label vk lab content signature
  )
  (ensures can_flow time sk_label public \/ (exists time_sig. time_sig <$ time /\ spred usg time_sig vk content))
let verify_with_label_is_valid gu spred usg sk_label time vk lab content signature =
  get_mls_label_is_valid gu time lab;
  let sign_content: sign_content_nt dy_bytes = {
    label = get_mls_label #dy_bytes lab;
    content = content;
  } in
  serialize_pre_lemma (sign_content_nt dy_bytes) (is_valid gu time) sign_content;
  parse_serialize_inv_lemma #dy_bytes (sign_content_nt dy_bytes) sign_content;
  let sign_content_bytes: dy_bytes = serialize (sign_content_nt dy_bytes) sign_content in
  LabeledCryptoAPI.verify_lemma #gu #time #SecrecyLabels.private_label #SecrecyLabels.private_label vk sign_content_bytes signature

// The following proof on `mk_can_sign` can probably be generalized for other authentication predicates, maybe even key usages?

val mk_can_sign: list (valid_label & sign_predicate) -> timestamp -> string -> dy_bytes -> dy_bytes -> prop
let rec mk_can_sign l time usg key msg =
  match l with
  | [] -> False
  | (lab, spred)::t ->
    let cur_prop =
      match parse (sign_content_nt dy_bytes) msg with
      | Some ({label; content;}) ->
      label == get_mls_label lab /\ spred usg time key content
      | None -> False
    in
    cur_prop \/ mk_can_sign t time usg key msg

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

val mk_can_sign_wrong_label: lab:valid_label -> l:list (valid_label & sign_predicate) -> time:timestamp -> usg:string -> key:dy_bytes -> msg:dy_bytes -> Lemma
  (requires ~(List.Tot.memP lab (List.Tot.map fst l)))
  (ensures (
    match parse (sign_content_nt dy_bytes) msg with
    | Some ({label; content;}) ->
      label == get_mls_label lab ==> ~(mk_can_sign l time usg key msg)
    | None -> ~(mk_can_sign l time usg key msg)
  ))
let rec mk_can_sign_wrong_label lab l time usg key msg =
  match l with
  | [] -> ()
  | (h_lab, _)::t -> (
    FStar.Classical.move_requires_2 get_mls_label_inj lab h_lab;
    mk_can_sign_wrong_label lab t time usg key msg
  )

val disjointP: #a:Type -> list a -> list a -> prop
let rec disjointP #a l1 l2 =
  match l1 with
  | [] -> True
  | h1::t1 ->
    ~(List.Tot.memP h1 l2) /\ disjointP t1 l2

val disjointP_cons: #a:Type -> x:a -> l1:list a -> l2:list a -> Lemma
  (requires disjointP l1 l2 /\ ~(List.Tot.memP x l1))
  (ensures disjointP l1 (x::l2))
let rec disjointP_cons #a x l1 l2 =
  match l1 with
  | [] -> ()
  | h1::t1 -> disjointP_cons x t1 l2

val memP_map: #a:Type -> #b:Type -> x:a -> f:(a -> b) -> l:list a -> Lemma
  (requires List.Tot.memP x l)
  (ensures List.Tot.memP (f x) (List.Tot.map f l))
let rec memP_map #a #b x f l =
  match l with
  | [] -> ()
  | h::t ->
    introduce x =!= h ==> List.Tot.memP (f x) (List.Tot.map f t)
    with _. memP_map x f t

val mk_can_sign_correct_aux: gu:global_usage -> lspred1:list (valid_label & sign_predicate) -> lspred2:list (valid_label & sign_predicate) -> lab:valid_label -> spred:sign_predicate -> Lemma
  (requires
    (forall time usg key msg. (mk_can_sign lspred1 time usg key msg \/ mk_can_sign lspred2 time usg key msg) <==> gu.usage_preds.can_sign time usg key msg) /\
    List.Tot.no_repeats_p (List.Tot.map fst lspred1) /\
    disjointP (List.Tot.map fst lspred1) (List.Tot.map fst lspred2) /\
    List.Tot.memP (lab, spred) lspred1
  )
  (ensures has_sign_predicate gu lab spred)
let rec mk_can_sign_correct_aux gu lspred1 lspred2 lab spred =
  match lspred1 with
  | [] -> ()
  | (h_lab, h_spred)::t -> (
    if h_lab = lab then (
      introduce forall (time:timestamp) (usg:string) (key:dy_bytes) (msg:dy_bytes). (
        match parse (sign_content_nt dy_bytes) msg with
        | Some ({label; content;}) ->
          label == get_mls_label lab ==> (gu.usage_preds.can_sign time usg key msg <==> spred usg time key content)
        | None -> True
      ) with (
        match parse (sign_content_nt dy_bytes) msg with
        | Some ({label; content;}) -> (
          if label = get_mls_label lab then (
            get_mls_label_inj lab h_lab;
            mk_can_sign_wrong_label lab t time usg key msg;
            mk_can_sign_wrong_label lab lspred2 time usg key msg;
            FStar.Classical.move_requires_3 memP_map (lab, spred) fst t
          ) else ()
        )
        | None -> ()
      )
    ) else (
      disjointP_cons h_lab (List.Tot.map fst t) (List.Tot.map fst lspred2);
      mk_can_sign_correct_aux gu t ((h_lab, h_spred)::lspred2) lab spred
    )
  )

val disjointP_nil: #a:Type -> l:list a -> Lemma (disjointP l [])
let rec disjointP_nil #a l =
  match l with
  | [] -> ()
  | _::t -> disjointP_nil t

val mk_can_sign_correct: gu:global_usage -> lspred:list (valid_label & sign_predicate) -> lab:valid_label -> spred:sign_predicate -> Lemma
  (requires
    gu.usage_preds.can_sign == mk_can_sign lspred /\
    List.Tot.no_repeats_p (List.Tot.map fst lspred) /\
    List.Tot.memP (lab, spred) lspred
  )
  (ensures has_sign_predicate gu lab spred)
let mk_can_sign_correct gu lspred lab spred =
  disjointP_nil (List.Tot.map fst lspred);
  mk_can_sign_correct_aux gu lspred [] lab spred
