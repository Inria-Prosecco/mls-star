module MLS.Symbolic.Session

open Comparse
open ComparseGlue
open MLS.Symbolic
open MLS.Symbolic.SplitPredicate

open GlobalRuntimeLib
open LabeledRuntimeAPI

#set-options "--fuel 1 --ifuel 1"

(*** Session predicates ***)

type labeled_session (bytes:Type0) {|bytes_like bytes|} = {
  label: bytes;
  content: bytes;
}

%splice [ps_labeled_session] (gen_parser (`labeled_session))
%splice [ps_labeled_session_is_valid] (gen_is_valid_lemma (`labeled_session))

instance parseable_serializeable_labeled_session (bytes:Type0) {|bytes_like bytes|}: parseable_serializeable bytes (labeled_session bytes) = mk_parseable_serializeable (ps_labeled_session)

let split_session_pred_func: split_predicate_input_values = {
  labeled_data_t = principal & timestamp & nat & nat & dy_bytes;
  label_t = string;
  encoded_label_t = dy_bytes;
  raw_data_t = principal & timestamp & nat & nat & dy_bytes;

  decode_labeled_data = (fun (p, time, si, vi, session) -> (
    match parse (labeled_session dy_bytes) session with
    | Some ({label; content}) -> Some (label, (p, time, si, vi, content))
    | None -> None
  ));

  encode_label = CryptoLib.string_to_bytes;
  encode_label_inj = (fun l1 l2 ->
    CryptoLib.string_to_bytes_lemma l1;
    CryptoLib.string_to_bytes_lemma l2
  );
}

type bare_session_pred = gu:global_usage -> p:principal -> time:timestamp -> si:nat -> vi:nat -> session:dy_bytes -> prop

val bare_session_pred_later: bare_session_pred -> prop
let bare_session_pred_later spred =
  forall gu p time0 time1 si vi session.
    (spred gu p time0 si vi session /\ time0 <$ time1)
    ==>
    spred gu p time1 si vi session

val bare_session_pred_is_msg: bare_session_pred -> prop
let bare_session_pred_is_msg spred =
  forall gu p time si vi session.
    spred gu p time si vi session
    ==>
    is_msg gu (readers [psv_id p si vi]) time session

type session_pred = spred:bare_session_pred{bare_session_pred_later spred /\ bare_session_pred_is_msg spred}

val mk_session_pred:
  spred:bare_session_pred ->
  (gu:global_usage -> p:principal -> time0:timestamp -> time1:timestamp -> si:nat -> vi:nat -> session:dy_bytes -> Lemma
    (requires spred gu p time0 si vi session /\ time0 <$ time1)
    (ensures spred gu p time1 si vi session)
  ) ->
  (gu:global_usage -> p:principal -> time:timestamp -> si:nat -> vi:nat -> session:dy_bytes -> Lemma
    (requires spred gu p time si vi session)
    (ensures is_msg gu (readers [psv_id p si vi]) time session)
  ) ->
  session_pred

let mk_session_pred spred later_lemma is_msg_lemma =
  introduce forall gu p time0 time1 si vi session. (spred gu p time0 si vi session /\ time0 <$ time1) ==> spred gu p time1 si vi session
  with (
    introduce _ ==> _ with _. (
      later_lemma gu p time0 time1 si vi session
    )
  );
  introduce forall gu p time si vi session. spred gu p time si vi session ==> is_msg gu (readers [psv_id p si vi]) time session
  with (
    introduce _ ==> _ with _. (
      is_msg_lemma gu p time si vi session
    )
  );
  spred

val session_pred_to_local_pred: global_usage -> session_pred -> local_pred split_session_pred_func
let session_pred_to_local_pred gu spred (p, time, si, vi, session) =
  spred gu p time si vi session

val preds_to_global_pred: preds -> global_pred split_session_pred_func
let preds_to_global_pred pr (p, time, si, vi, session) =
  pr.trace_preds.session_st_inv time p si vi session

val has_session_pred: preds -> string -> session_pred -> prop
let has_session_pred pr lab spred =
  has_local_pred split_session_pred_func (preds_to_global_pred pr) lab (session_pred_to_local_pred pr.global_usage spred)

(*** Global session predicate builder ***)

val label_session_pred_to_label_local_pred: global_usage -> string & session_pred -> string & local_pred split_session_pred_func
let label_session_pred_to_label_local_pred gu (label, spred) =
  (label, session_pred_to_local_pred gu spred)

val mk_global_session_pred: list (string & session_pred) -> global_usage -> timestamp -> principal -> nat -> nat -> dy_bytes -> prop
let mk_global_session_pred l gu time p si vi session =
  mk_global_pred split_session_pred_func (List.Tot.map (label_session_pred_to_label_local_pred gu) l) (p, time, si, vi, session)

val mk_global_session_pred_correct: pr:preds -> lspred:list (string & session_pred) -> lab:string -> spred:session_pred -> Lemma
  (requires
    pr.trace_preds.session_st_inv == mk_global_session_pred lspred pr.global_usage /\
    List.Tot.no_repeats_p (List.Tot.map fst lspred) /\
    List.Tot.memP (lab, spred) lspred
  )
  (ensures has_session_pred pr lab spred)
let mk_global_session_pred_correct pr lspred lab spred =
  let open MLS.MiscLemmas in
  assert_norm (forall session p time si vi. preds_to_global_pred pr (p, time, si, vi, session) <==> pr.trace_preds.session_st_inv time p si vi session);
  memP_map (lab, spred) (label_session_pred_to_label_local_pred pr.global_usage) lspred;
  FStar.Classical.forall_intro_2 (index_map (label_session_pred_to_label_local_pred pr.global_usage));
  FStar.Classical.forall_intro_2 (index_map (fst #string #session_pred));
  FStar.Classical.forall_intro_2 (index_map (fst #string #(local_pred split_session_pred_func)));
  List.Tot.index_extensionality (List.Tot.map fst lspred) (List.Tot.map fst (List.Tot.map (label_session_pred_to_label_local_pred pr.global_usage) lspred));
  mk_global_pred_correct split_session_pred_func (List.Tot.map (label_session_pred_to_label_local_pred pr.global_usage) lspred) lab (session_pred_to_local_pred pr.global_usage spred)

val mk_global_session_pred_is_msg: lspred:list (string & session_pred) -> gu:global_usage -> time:timestamp -> p:principal -> si:nat -> vi:nat -> st:dy_bytes -> Lemma
  (requires mk_global_session_pred lspred gu time p si vi st)
  (ensures is_msg gu (readers [psv_id p si vi]) time st)
let rec mk_global_session_pred_is_msg lspred gu time p si vi st =
  match lspred with
  | [] -> ()
  | (current_label, current_spred)::tspred ->
    FStar.Classical.move_requires (mk_global_session_pred_is_msg tspred gu time p si vi) st;
    match parse (labeled_session dy_bytes) st with
    | None -> ()
    | Some ({label; content}) -> (
      if label = CryptoLib.string_to_bytes current_label then (
        introduce current_spred gu p time si vi content ==> is_msg gu (readers [psv_id p si vi]) time st
        with _. (
          // This is the first time I use this lemma from Comparse!
          // All that proof effort wasn't for nothing!!!
          serialize_parse_inv_lemma (labeled_session dy_bytes) st;
          LabeledCryptoAPI.string_to_bytes_lemma #gu #time current_label;
          serialize_pre_lemma (labeled_session dy_bytes) (is_msg gu (readers [psv_id p si vi]) time) ({label; content})
        )
      ) else ()
    )

val mk_global_session_pred_later: lspred:list (string & session_pred) -> gu:global_usage -> time0:timestamp -> time1:timestamp -> p:principal -> si:nat -> vi:nat -> st:dy_bytes -> Lemma
  (requires mk_global_session_pred lspred gu time0 p si vi st /\ time0 <$ time1)
  (ensures mk_global_session_pred lspred gu time1 p si vi st)
let rec mk_global_session_pred_later lspred gu time0 time1 p si vi st =
  match lspred with
  | [] -> ()
  | (current_label, current_spred)::tspred -> (
    FStar.Classical.move_requires (mk_global_session_pred_later tspred gu time0 time1 p si vi) st;
    match parse (labeled_session dy_bytes) st with
    | None -> ()
    | Some ({label; content}) -> (
      if label = CryptoLib.string_to_bytes current_label then (
        assert(current_spred gu p time0 si vi content ==> mk_global_session_pred lspred gu time1 p si vi st)
      ) else ()
    )
  )

(*** LCrypto API for labeled sessions ***)

let global_timestamp = global_timestamp

val new_session_number:
  pr:preds -> p:principal -> LCrypto nat pr
  (requires fun t0 -> True)
  (ensures fun t0 r t1 -> t1 == t0)
let new_session_number pr p = new_session_number #pr p

val new_session:
  pr:preds -> label:string -> spred:session_pred ->
  p:principal -> si:nat -> vi:nat -> st:dy_bytes ->
  LCrypto unit pr
  (requires fun t0 -> spred pr.global_usage p (trace_len t0) si vi st /\ has_session_pred pr label spred)
  (ensures fun t0 r t1 -> trace_len t1 == trace_len t0 + 1)
let new_session pr label spred p si vi st =
  assert_norm (forall session p time si vi. preds_to_global_pred pr (p, time, si, vi, session) <==> pr.trace_preds.session_st_inv time p si vi session);
  let time = global_timestamp () in
  let session = {
    label = CryptoLib.string_to_bytes label;
    content = st;
  } in
  let session_bytes = serialize (labeled_session dy_bytes) session in
  parse_serialize_inv_lemma #dy_bytes (labeled_session dy_bytes) session;
  new_session #pr #time p si vi session_bytes

// Roughly a copy-paste of the above
val update_session:
  pr:preds -> label:string -> spred:session_pred ->
  p:principal -> si:nat -> vi:nat -> st:dy_bytes ->
  LCrypto unit pr
  (requires fun t0 -> spred pr.global_usage p (trace_len t0) si vi st /\ has_session_pred pr label spred)
  (ensures fun t0 r t1 -> trace_len t1 == trace_len t0 + 1)
let update_session pr label spred p si vi st =
  assert_norm (forall session p time si vi. preds_to_global_pred pr (p, time, si, vi, session) <==> pr.trace_preds.session_st_inv time p si vi session);
  let time = global_timestamp () in
  let session = {
    label = CryptoLib.string_to_bytes label;
    content = st;
  } in
  let session_bytes = serialize (labeled_session dy_bytes) session in
  parse_serialize_inv_lemma #dy_bytes (labeled_session dy_bytes) session;
  update_session #pr #time p si vi session_bytes

val get_session:
  pr:preds -> label:string -> spred:session_pred ->
  p:principal -> si:nat ->
  LCrypto (nat & dy_bytes) pr
  (requires fun t0 -> has_session_pred pr label spred)
  (ensures fun t0 (vi,st) t1 ->
    t1 == t0 /\
    spred pr.global_usage p (trace_len t0) si vi st /\
    is_msg pr.global_usage (readers [psv_id p si vi]) (trace_len t0) st
  )
let get_session pr label spred p si =
  assert_norm (forall session p time si vi. preds_to_global_pred pr (p, time, si, vi, session) <==> pr.trace_preds.session_st_inv time p si vi session);
  let time = global_timestamp () in
  let (|vi, session_bytes|) = get_session #pr #time p si in
  // Why the typeclass instantiation??
  match parse (labeled_session dy_bytes) #(parseable_serializeable_labeled_session dy_bytes) (session_bytes <: dy_bytes) with
  | Some session -> (
    if session.label = CryptoLib.string_to_bytes label then (
      (vi, session.content)
    ) else (
      error "session has wrong label"
    )
  )
  | None ->
    error "session isn't properly labeled (however it should be forbidden by the session invariant)"
