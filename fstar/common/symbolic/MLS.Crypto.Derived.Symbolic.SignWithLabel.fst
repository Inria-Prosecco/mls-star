module MLS.Crypto.Derived.Symbolic.SignWithLabel

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

(*** Split predicate for SignWithLabel ***)

noeq
type signwithlabel_crypto_pred {|crypto_usages|} = {
  pred: trace -> sk_usg:usage{SigKey? sk_usg} -> vk:bytes -> msg:bytes -> prop;
  pred_later:
    tr1:trace -> tr2:trace ->
    sk_usg:usage{SigKey? sk_usg} -> vk:bytes -> msg:bytes ->
    Lemma
    (requires
      pred tr1 sk_usg vk msg /\
      bytes_well_formed tr1 vk /\
      bytes_well_formed tr1 msg /\
      tr1 <$ tr2
    )
    (ensures pred tr2 sk_usg vk msg)
  ;
}

let split_signwithlabel_crypto_pred_params {|crypto_usages|}: split_function_parameters = {
  tag_set_t = valid_label;
  tag_t = mls_ascii_string;
  is_disjoint = unequal;
  tag_belong_to = (fun tag tag_set ->
    tag = get_mls_label tag_set
  );
  cant_belong_to_disjoint_sets = (fun tag tag_set_1 tag_set_2 ->
    FStar.Classical.move_requires_2 get_mls_label_inj tag_set_1 tag_set_2
  );

  tagged_data_t = (trace & (sk_usg:usage{SigKey? sk_usg}) & bytes & bytes);
  raw_data_t = (trace & (sk_usg:usage{SigKey? sk_usg}) & bytes & bytes);
  output_t = prop;

  decode_tagged_data = (fun (tr, sk_usage, vk, data) -> (
    match parse (sign_content_nt bytes) data with
    | Some ({label; content}) -> Some (label, (tr, sk_usage, vk, content))
    | None -> None
  ));

  local_fun_t = mk_dependent_type signwithlabel_crypto_pred;
  global_fun_t = trace -> sk_usg:usage{SigKey? sk_usg} -> bytes -> bytes -> prop;

  default_global_fun = (fun tr sk_usage vk content -> False);


  apply_local_fun = (fun pred (tr, sk_usage, vk, content) -> pred.pred tr sk_usage vk content);
  apply_global_fun = (fun pred (tr, sk_usage, vk, msg) -> pred tr sk_usage vk msg);
  mk_global_fun = (fun pred tr sk_usage vk msg -> pred (tr, sk_usage, vk, msg));
  apply_mk_global_fun = (fun _ _ -> ());
}

#push-options "--ifuel 1"
val has_signwithlabel_pred: {|crypto_usages|} -> sign_crypto_predicate -> (valid_label & signwithlabel_crypto_pred) -> prop
let has_signwithlabel_pred #cusgs sign_pred (lab, local_pred) =
  forall tr sk_usage vk msg.
    {:pattern sign_pred.pred tr sk_usage vk msg}
    match parse (sign_content_nt bytes) msg with
    | Some {label; content} -> (
      label == get_mls_label lab ==> (
        sign_pred.pred tr sk_usage vk msg ==
        local_pred.pred tr sk_usage vk content
      )
    )
    | _ -> True
#pop-options

val intro_has_signwithlabel_pred:
  {|crypto_usages|} ->
  sign_pred:sign_crypto_predicate -> tag:valid_label -> local_pred:signwithlabel_crypto_pred ->
  Lemma
  (requires has_local_fun split_signwithlabel_crypto_pred_params sign_pred.pred (|tag, local_pred|))
  (ensures has_signwithlabel_pred sign_pred (tag, local_pred))
let intro_has_signwithlabel_pred #cusgs sign_pred tag local_pred =
  introduce
    forall tr sk_usage vk msg.
      match parse (sign_content_nt bytes) msg with
      | Some {label; content} -> (
        label == get_mls_label tag ==> (
          sign_pred.pred tr sk_usage vk msg ==
          local_pred.pred tr sk_usage vk content
        )
      )
      | _ -> True
  with (
    has_local_fun_elim split_signwithlabel_crypto_pred_params sign_pred.pred tag local_pred (tr, sk_usage, vk, msg)
  )

val mk_global_mls_sign_pred:
  {|crypto_usages|} ->
  list (valid_label & signwithlabel_crypto_pred) ->
  trace -> sk_usg:usage{SigKey? sk_usg} -> bytes -> bytes ->
  prop
let mk_global_mls_sign_pred tagged_local_preds sk_usage vk msg =
  mk_global_fun split_signwithlabel_crypto_pred_params (mk_dependent_tagged_local_funs tagged_local_preds) sk_usage vk msg

#push-options "--ifuel 2"
val mk_global_mls_sign_pred_later:
  {|crypto_usages|} ->
  tagged_local_preds:list (valid_label & signwithlabel_crypto_pred) ->
  tr1:trace -> tr2:trace ->
  sk_usg:usage{SigKey? sk_usg} -> vk:bytes -> msg:bytes ->
  Lemma
  (requires
    mk_global_mls_sign_pred tagged_local_preds tr1 sk_usg vk msg /\
    bytes_well_formed tr1 vk /\
    bytes_well_formed tr1 msg /\
    tr1 <$ tr2
  )
  (ensures mk_global_mls_sign_pred tagged_local_preds tr2 sk_usg vk msg)
let mk_global_mls_sign_pred_later tagged_local_preds tr1 tr2 sk_usg vk msg =
  let params = split_signwithlabel_crypto_pred_params in
  mk_global_fun_eq params (mk_dependent_tagged_local_funs tagged_local_preds) (tr1, sk_usg, vk, msg);
  mk_global_fun_eq params (mk_dependent_tagged_local_funs tagged_local_preds) (tr2, sk_usg, vk, msg);
  parse_wf_lemma (sign_content_nt bytes) (bytes_well_formed tr1) msg;
  introduce forall tag_set lpred content. bytes_well_formed tr1 content /\ params.apply_local_fun lpred (tr1, sk_usg, vk, content) ==> params.apply_local_fun #tag_set lpred (tr2, sk_usg, vk, content) with (
    introduce _ ==> _ with _. (
      lpred.pred_later tr1 tr2 sk_usg vk content
    )
  )
#pop-options

val mk_mls_sign_pred:
  {|crypto_usages|} ->
  list (valid_label & signwithlabel_crypto_pred) ->
  sign_crypto_predicate
let mk_mls_sign_pred #cusgs tagged_local_preds = {
  pred = mk_global_mls_sign_pred tagged_local_preds;
  pred_later = mk_global_mls_sign_pred_later tagged_local_preds;
}

#push-options "--ifuel 1"
val mk_mls_sign_pred_correct:
  {|crypto_usages|} ->
  sign_pred:sign_crypto_predicate -> tagged_local_preds:list (valid_label & signwithlabel_crypto_pred) ->
  Lemma
  (requires
    sign_pred == mk_mls_sign_pred tagged_local_preds /\
    List.Tot.no_repeats_p (List.Tot.map fst tagged_local_preds)
  )
  (ensures for_allP (has_signwithlabel_pred sign_pred) tagged_local_preds)
let mk_mls_sign_pred_correct #cusgs sign_pred tagged_local_preds =
  no_repeats_p_implies_for_all_pairsP_unequal (List.Tot.map fst tagged_local_preds);
  map_dfst_mk_dependent_tagged_local_funs tagged_local_preds;
  for_allP_eq (has_signwithlabel_pred sign_pred) tagged_local_preds;
  FStar.Classical.forall_intro_2 (memP_mk_dependent_tagged_local_funs tagged_local_preds);
  FStar.Classical.forall_intro_2 (FStar.Classical.move_requires_2 (mk_global_fun_correct split_signwithlabel_crypto_pred_params (mk_dependent_tagged_local_funs tagged_local_preds)));
  FStar.Classical.forall_intro_2 (FStar.Classical.move_requires_2 (intro_has_signwithlabel_pred sign_pred))
#pop-options

(*** ***)

val has_mls_signwithlabel_pred: {|crypto_invariants|} -> (valid_label & signwithlabel_crypto_pred) -> prop
let has_mls_signwithlabel_pred #cinvs tagged_local_pred =
  exists mls_sign_pred.
    has_sign_predicate ("MLS.LeafSignKey", mls_sign_pred) /\
    has_signwithlabel_pred mls_sign_pred tagged_local_pred

(*** Lemmas on SignWithLabel and VerifyWithLabel ***)

val bytes_invariant_sign_with_label:
  {|crypto_invariants|} -> spred:signwithlabel_crypto_pred ->
  tr:trace -> prin:principal ->
  sk:bytes -> lab:valid_label -> msg:mls_bytes bytes -> nonce:sign_nonce bytes ->
  Lemma
  (requires
    bytes_invariant tr sk /\
    bytes_invariant tr nonce /\
    bytes_invariant tr msg /\
    sk `has_usage tr` mk_mls_sigkey_usage prin /\
    nonce `has_usage tr` SigNonce /\
    (get_label tr sk) `can_flow tr` (get_label tr nonce) /\ (
      spred.pred tr (mk_mls_sigkey_usage prin) (vk sk) msg
      \/
      get_label tr sk `can_flow tr` public
    ) /\
    has_mls_signwithlabel_pred (lab, spred)
  )
  (ensures
    bytes_invariant tr (Success?.v (sign_with_label sk lab msg nonce)) /\
    (get_label tr (Success?.v (sign_with_label sk lab msg nonce))) `can_flow tr` (get_label tr msg)
  )
let bytes_invariant_sign_with_label #ci spred tr prin sk lab msg nonce =
  let sign_content: sign_content_nt bytes = {
    label = get_mls_label lab;
    content = msg;
  } in
  serialize_wf_lemma (sign_content_nt bytes) (bytes_invariant tr) sign_content;
  serialize_wf_lemma (sign_content_nt bytes) (is_knowable_by (get_label tr msg) tr) sign_content

val bytes_invariant_verify_with_label:
  {|ci:crypto_invariants|} -> spred:signwithlabel_crypto_pred ->
  tr:trace -> prin:principal ->
  vk:bytes -> lab:valid_label -> content:mls_bytes bytes -> signature:bytes ->
  Lemma
  (requires
    bytes_invariant tr vk /\
    bytes_invariant tr content /\
    bytes_invariant tr signature /\
    vk `has_signkey_usage tr` mk_mls_sigkey_usage prin /\
    verify_with_label vk lab content signature /\
    has_mls_signwithlabel_pred (lab, spred)
  )
  (ensures
    (
      spred.pred tr (mk_mls_sigkey_usage prin) vk content
    ) \/ (
      (get_signkey_label tr vk) `can_flow tr` public
    )
  )
let bytes_invariant_verify_with_label #ci spred tr prin vk lab content signature =
  let sign_content: sign_content_nt bytes = {
    label = get_mls_label lab;
    content = content;
  } in
  serialize_wf_lemma (sign_content_nt bytes) (bytes_invariant tr) sign_content
