module MLS.Symbolic.TypedSession

open Comparse
open MLS.Symbolic
open MLS.Symbolic.Session
open LabeledRuntimeAPI

type bare_typed_session_pred (a:Type) {|parseable_serializeable dy_bytes a|} = gu:global_usage -> p:principal -> time:timestamp -> si:nat -> vi:nat -> session:a -> prop

val bare_typed_session_pred_later: #a:Type -> {|parseable_serializeable dy_bytes a|} -> bare_typed_session_pred a -> prop
let bare_typed_session_pred_later #a #ps_a spred =
  forall gu p time0 time1 si vi session.
    (spred gu p time0 si vi session /\ time0 <$ time1)
    ==>
    spred gu p time1 si vi session

val bare_typed_session_pred_is_msg: #a:Type -> {|parseable_serializeable dy_bytes a|} -> bare_typed_session_pred a -> prop
let bare_typed_session_pred_is_msg #a #ps_a spred =
  forall gu p time si vi session.
    spred gu p time si vi session
    ==>
    is_well_formed _ (is_msg gu (readers [psv_id p si vi]) time) session

type typed_session_pred (a:Type) {|parseable_serializeable dy_bytes a|} = spred:bare_typed_session_pred a{bare_typed_session_pred_later spred /\ bare_typed_session_pred_is_msg spred}

val typed_session_pred_to_session_pred: #a:Type -> {|parseable_serializeable dy_bytes a|} -> typed_session_pred a -> session_pred
let typed_session_pred_to_session_pred #a #ps_a tspred =
  let bare_spred gu p time si vi session: prop =
    match parse a session with
    | None -> False
    | Some st -> tspred gu p time si vi st
  in
  mk_session_pred bare_spred
    (fun gu p time0 time1 si vi session -> ())
    (fun gu p time si vi session ->
      let st = Some?.v (parse a session) in
      let pre = is_msg gu (readers [psv_id p si vi]) time in
      serialize_parse_inv_lemma a session;
      serialize_wf_lemma a pre st
    )

val mk_typed_session_pred:
  #a:Type -> {|parseable_serializeable dy_bytes a|} ->
  tspred:bare_typed_session_pred a ->
  (gu:global_usage -> p:principal -> time0:timestamp -> time1:timestamp -> si:nat -> vi:nat -> session:a -> Lemma
    (requires tspred gu p time0 si vi session /\ time0 <$ time1)
    (ensures tspred gu p time1 si vi session)
  ) ->
  (gu:global_usage -> p:principal -> time:timestamp -> si:nat -> vi:nat -> session:a -> Lemma
    (requires tspred gu p time si vi session)
    (ensures is_well_formed _ (is_msg gu (readers [psv_id p si vi]) time) session)
  ) ->
  typed_session_pred a
let mk_typed_session_pred #a #ps_a tspred later_lemma is_msg_lemma =
  introduce forall gu p time0 time1 si vi session. (tspred gu p time0 si vi session /\ time0 <$ time1) ==> tspred gu p time1 si vi session
  with (
    introduce _ ==> _ with _. (
      later_lemma gu p time0 time1 si vi session
    )
  );
  introduce forall gu p time si vi session. tspred gu p time si vi session ==> is_well_formed _ (is_msg gu (readers [psv_id p si vi]) time) session
  with (
    introduce _ ==> _ with _. (
      is_msg_lemma gu p time si vi session
    )
  );
  tspred
