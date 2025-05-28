module MLS.Crypto.Derived.Symbolic.EncryptWithLabel

open FStar.List.Tot { for_allP, for_allP_eq }
open Comparse
open DY.Core
open DY.Lib
open MLS.NetworkTypes
open MLS.Crypto
open MLS.Crypto.Derived.Lemmas
open MLS.Symbolic
open MLS.Result

#set-options "--fuel 0 --ifuel 0"

(*** Split predicate for EncryptWithLabel ***)

noeq
type encryptwithlabel_crypto_pred {|crypto_usages|} = {
  pred: tr:trace -> key_usg_data:bytes -> msg:bytes -> context:bytes -> prop;
  pred_later:
    tr1:trace -> tr2:trace ->
    key_usg_data:bytes ->
    msg:bytes -> context:bytes ->
    Lemma
    (requires
      pred tr1 key_usg_data msg context /\
      bytes_well_formed tr1 msg /\
      bytes_well_formed tr1 context /\
      tr1 <$ tr2
    )
    (ensures pred tr2 key_usg_data msg context)
  ;
}

let split_encryptwithlabel_crypto_pred_params {|crypto_usages|}: split_function_parameters = {
  tag_set_t = valid_label;
  tag_t = MLS.NetworkTypes.mls_ascii_string;
  is_disjoint = unequal;
  tag_belong_to = (fun tag tag_set ->
    tag = get_mls_label tag_set
  );
  cant_belong_to_disjoint_sets = (fun tag tag_set_1 tag_set_2 ->
    FStar.Classical.move_requires_2 get_mls_label_inj tag_set_1 tag_set_2
  );

  tagged_data_t = (trace & (string & bytes) & bytes & bytes & bytes);
  raw_data_t = (trace & bytes & bytes & bytes);
  output_t = prop;

  decode_tagged_data = (fun (tr, (usg_tag, usg_data), msg, info, ad) -> (
    match parse (encrypt_context_nt bytes) info with
    | Some {label; context} -> Some (label, (tr, usg_data, msg, context))
    | None -> None
  ));

  local_fun_t = mk_dependent_type encryptwithlabel_crypto_pred;
  global_fun_t = trace -> (string & bytes) -> bytes -> bytes -> bytes -> prop;

  default_global_fun = (fun tr usg msg info ad -> False);


  apply_local_fun = (fun pred (tr, usg_data, msg, context) -> pred.pred tr usg_data msg context);
  apply_global_fun = (fun pred (tr, usg, msg, info, ad) -> pred tr usg msg info ad);
  mk_global_fun = (fun pred tr usg msg info ad -> pred (tr, usg, msg, info, ad));
  apply_mk_global_fun = (fun _ _ -> ());
}

#push-options "--ifuel 1"
val has_encryptwithlabel_pred: {|crypto_usages|} -> hpke_crypto_predicate -> (valid_label & encryptwithlabel_crypto_pred) -> prop
let has_encryptwithlabel_pred #cusgs hpke (lab, local_pred) =
  forall tr usg plaintext info ad.
    {:pattern hpke.pred tr usg plaintext info ad}
    match parse (encrypt_context_nt bytes) info with
    | Some {label; context} -> (
      label == get_mls_label lab ==> (
        hpke.pred tr usg plaintext info ad ==
        local_pred.pred tr (snd usg) plaintext context
      )
    )
    | _ -> True
#pop-options

// F* is extremely slow on this one, even with --lax?
val intro_has_encryptwithlabel_pred:
  {|crypto_usages|} ->
  hpke_pred:hpke_crypto_predicate -> tag:valid_label -> local_pred:encryptwithlabel_crypto_pred ->
  Lemma
  (requires has_local_fun split_encryptwithlabel_crypto_pred_params hpke_pred.pred (|tag, local_pred|))
  (ensures has_encryptwithlabel_pred hpke_pred (tag, local_pred))
let intro_has_encryptwithlabel_pred #cusgs hpke_pred tag local_pred =
  introduce
    forall tr usg plaintext info ad.
      match parse (encrypt_context_nt bytes) info with
      | Some {label; context} -> (
        label == get_mls_label tag ==> (
          hpke_pred.pred tr usg plaintext info ad ==
          local_pred.pred tr (snd usg) plaintext context
        )
      )
      | _ -> True
  with (
    has_local_fun_elim split_encryptwithlabel_crypto_pred_params hpke_pred.pred tag local_pred (tr, usg, plaintext, info, ad)
  )

val mk_global_hpke_mls_pred:
  {|crypto_usages|} ->
  list (valid_label & encryptwithlabel_crypto_pred) ->
  trace -> string & bytes -> bytes -> bytes -> bytes -> prop
let mk_global_hpke_mls_pred #cusgs tagged_local_preds =
  mk_global_fun split_encryptwithlabel_crypto_pred_params (mk_dependent_tagged_local_funs tagged_local_preds)

#push-options "--ifuel 2 --z3rlimit 15"
val mk_global_hpke_mls_pred_later:
  {|crypto_usages|} ->
  tagged_local_preds:list (valid_label & encryptwithlabel_crypto_pred) ->
  tr1:trace -> tr2:trace ->
  usage:(string & bytes) -> plaintext:bytes -> info:bytes -> ad:bytes ->
  Lemma
  (requires
    mk_global_hpke_mls_pred tagged_local_preds tr1 usage plaintext info ad /\
    bytes_well_formed tr1 plaintext /\
    bytes_well_formed tr1 info /\
    tr1 <$ tr2
  )
  (ensures mk_global_hpke_mls_pred tagged_local_preds tr2 usage plaintext info ad)
let mk_global_hpke_mls_pred_later #cusgs tagged_local_preds tr1 tr2 usage plaintext info ad =
  let params = split_encryptwithlabel_crypto_pred_params in
  mk_global_fun_eq params (mk_dependent_tagged_local_funs tagged_local_preds) (tr1, usage, plaintext, info, ad);
  mk_global_fun_eq params (mk_dependent_tagged_local_funs tagged_local_preds) (tr2, usage, plaintext, info, ad);
  let Some {label; context} = parse (encrypt_context_nt bytes) info in
  parse_wf_lemma (encrypt_context_nt bytes) (bytes_well_formed tr1) info;
  introduce forall tag_set local_pred. params.apply_local_fun local_pred (tr1, (snd usage), plaintext, (context <: bytes)) ==> params.apply_local_fun #tag_set local_pred (tr2, (snd usage), plaintext, (context <: bytes)) with (
    introduce _ ==> _ with _. (
      local_pred.pred_later tr1 tr2 (snd usage) plaintext context
    )
  )
#pop-options

val mk_hpke_mls_pred:
  {|crypto_usages|} ->
  list (valid_label & encryptwithlabel_crypto_pred) ->
  hpke_crypto_predicate
let mk_hpke_mls_pred #cusgs tagged_local_preds = {
  pred = mk_global_hpke_mls_pred tagged_local_preds;
  pred_later = mk_global_hpke_mls_pred_later tagged_local_preds;
}

#push-options "--ifuel 1"
val mk_hpke_mls_pred_correct:
  {|crypto_usages|} ->
  hpke_pred:hpke_crypto_predicate -> tagged_local_preds:list (valid_label & encryptwithlabel_crypto_pred) ->
  Lemma
  (requires
    hpke_pred == mk_hpke_mls_pred tagged_local_preds /\
    List.Tot.no_repeats_p (List.Tot.map fst tagged_local_preds)
  )
  (ensures for_allP (has_encryptwithlabel_pred hpke_pred) tagged_local_preds)
let mk_hpke_mls_pred_correct #cusgs hpke_pred tagged_local_preds =
  no_repeats_p_implies_for_all_pairsP_unequal (List.Tot.map fst tagged_local_preds);
  map_dfst_mk_dependent_tagged_local_funs tagged_local_preds;
  for_allP_eq (has_encryptwithlabel_pred hpke_pred) tagged_local_preds;
  FStar.Classical.forall_intro_2 (memP_mk_dependent_tagged_local_funs tagged_local_preds);
  FStar.Classical.forall_intro_2 (FStar.Classical.move_requires_2 (mk_global_fun_correct split_encryptwithlabel_crypto_pred_params (mk_dependent_tagged_local_funs tagged_local_preds)));
  FStar.Classical.forall_intro_2 (FStar.Classical.move_requires_2 (intro_has_encryptwithlabel_pred hpke_pred))
#pop-options

val has_mls_encryptwithlabel_pred: {|crypto_invariants|} -> (string & valid_label & encryptwithlabel_crypto_pred) -> prop
let has_mls_encryptwithlabel_pred #cinvs (tag, lab, local_pred) =
  exists (hpke_invs:hpke_crypto_invariants) mls_hpke_pred.
    has_hpke_invariants /\
    has_hpke_predicate (tag, mls_hpke_pred) /\
    has_encryptwithlabel_pred mls_hpke_pred (lab, local_pred)

val compute_encryption_context_is_knowable_by:
  {|crypto_invariants|} ->
  l:label -> tr:trace ->
  label:valid_label -> context:bytes ->
  Lemma
  (requires is_knowable_by l tr context)
  (ensures (
    match compute_encryption_context label context with
    | Success res ->
      is_knowable_by l tr res
    | _ -> True
  ))
let compute_encryption_context_is_knowable_by #cinvs l tr label context =
  match compute_encryption_context label context with
  | Success res -> (
    serialize_wf_lemma (encrypt_context_nt bytes) (is_knowable_by l tr) {
      label = get_mls_label label;
      context;
    }
  )
  | _ -> ()

val bytes_invariant_encrypt_with_label:
  {|crypto_invariants|} -> lpred:encryptwithlabel_crypto_pred ->
  usg_tag:string -> usg_data:bytes ->
  tr:trace ->
  pkR:hpke_public_key bytes -> label:valid_label -> context:bytes -> plaintext:bytes -> entropy:lbytes bytes (hpke_private_key_length #bytes) ->
  Lemma
  (requires
    bytes_invariant tr pkR /\
    bytes_invariant tr entropy /\
    bytes_invariant tr context /\
    bytes_invariant tr plaintext /\
    (get_label tr plaintext) `can_flow tr` (get_label tr entropy) /\
    (get_label tr entropy) `can_flow tr` (get_hpke_sk_label tr pkR) /\
    entropy `has_usage tr` mk_hpke_entropy_usage (usg_tag, usg_data) /\
    (
      (
        pkR `has_hpke_sk_usage tr` mk_hpke_sk_usage (usg_tag, usg_data) /\
        lpred.pred tr usg_data plaintext context
      ) \/ (
        get_label tr entropy `can_flow tr` public
      )
    ) /\
    has_mls_encryptwithlabel_pred (usg_tag, label, lpred)
  )
  (ensures (
    match encrypt_with_label pkR label context plaintext entropy with
    | Success (enc, ciphertext) -> (
      is_publishable tr enc /\
      is_publishable tr ciphertext
    )
    | _ -> True
  ))
let bytes_invariant_encrypt_with_label #cinvs lpred usg_tag usg_data tr pkR label context plaintext entropy =
  match compute_encryption_context label context with
  | Success context_bytes -> (
    compute_encryption_context_is_knowable_by secret tr label context;
    assert(parse (encrypt_context_nt bytes) context_bytes == Some ({ label = get_mls_label label; context; } <: encrypt_context_nt bytes))
  )
  | _ -> ()

val bytes_invariant_decrypt_with_label:
  {|crypto_invariants|} -> lpred:encryptwithlabel_crypto_pred ->
  usg_tag:string -> usg_data:bytes ->
  tr:trace ->
  skR:hpke_private_key bytes -> label:valid_label -> context:bytes -> enc:hpke_kem_output bytes -> ciphertext:bytes ->
  Lemma
  (requires
    bytes_invariant tr skR /\
    skR `has_usage tr` mk_hpke_sk_usage (usg_tag, usg_data) /\
    bytes_invariant tr enc /\
    bytes_invariant tr context /\
    bytes_invariant tr ciphertext /\
    has_mls_encryptwithlabel_pred (usg_tag, label, lpred)
  )
  (ensures (
    match decrypt_with_label skR label context enc ciphertext with
    | Success plaintext -> (
      is_knowable_by (get_label tr skR) tr plaintext /\ (
        lpred.pred tr usg_data plaintext context \/
        is_publishable tr plaintext
      )
    )
    | _ -> True
  ))
let bytes_invariant_decrypt_with_label #cinvs lpred usg_tag usg_data tr skR label context enc ciphertext =
  match compute_encryption_context label context with
  | Success context_bytes -> (
    match DY.Lib.HPKE.hpke_dec skR (enc, ciphertext) context_bytes empty with
    | Some res -> (
      compute_encryption_context_is_knowable_by secret tr label context;
      assert(parse (encrypt_context_nt bytes) context_bytes == Some ({ label = get_mls_label label; context; } <: encrypt_context_nt bytes))
    )
    | _ -> ()
  )
  | _ -> ()
