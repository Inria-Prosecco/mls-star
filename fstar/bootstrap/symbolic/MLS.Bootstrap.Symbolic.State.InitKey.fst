module MLS.Bootstrap.Symbolic.State.InitKey

open Comparse
open DY.Core
open DY.Lib
open MLS.Symbolic.MyMkRand

#set-options "--fuel 0 --ifuel 0"

[@@ with_bytes bytes]
type bootstrap_init_key_state = {
  leaf_pk: bytes;
  init_sk:bytes;
}

%splice [ps_bootstrap_init_key_state] (gen_parser (`bootstrap_init_key_state))
%splice [ps_bootstrap_init_key_state_is_well_formed] (gen_is_well_formed_lemma (`bootstrap_init_key_state))

instance local_state_bootstrap_init_key_state: local_state bootstrap_init_key_state = {
  tag = "MLS.Bootstrap.InitKeyState";
  format = mk_parseable_serializeable ps_bootstrap_init_key_state;
}

val init_key_label_pred:
  principal -> bytes ->
  principal -> string -> state_id -> bootstrap_init_key_state -> prop
let init_key_label_pred prin1 init_pk =
  fun prin2 tag sid st ->
    prin1 == prin2 /\
    tag == "MLS.Bootstrap.InitKeyState" /\
    hpke_pk st.init_sk == init_pk

val init_key_label:
  principal -> bytes ->
  label
let init_key_label prin init_pk =
  typed_state_pred_label (init_key_label_pred prin init_pk)

#push-options "--ifuel 1"
val init_key_label_can_flow_public:
  tr:trace ->
  prin:principal -> init_pk:bytes ->
  Lemma
  (requires
    (init_key_label prin init_pk) `can_flow tr` public
  )
  (ensures
    exists sid init_sk leaf_pk.
      state_was_corrupt tr prin "MLS.Bootstrap.InitKeyState" sid { leaf_pk; init_sk; } /\
      hpke_pk init_sk == init_pk
  )
let init_key_label_can_flow_public tr prin init_pk = ()
#pop-options

[@@ with_bytes bytes]
type init_key_usage_t = {
  me: principal;
  leaf_public_key: bytes;
}

%splice[ps_init_key_usage_t] (gen_parser (`init_key_usage_t))

instance parseable_serializeable_init_key_usage_t: parseable_serializeable bytes init_key_usage_t = mk_parseable_serializeable ps_init_key_usage_t

val init_key_usage_data:
  principal -> bytes ->
  bytes
let init_key_usage_data me leaf_public_key =
  serialize _ {me; leaf_public_key;}

val init_key_usage:
  principal -> bytes ->
  usage
let init_key_usage me leaf_public_key =
  (mk_hpke_sk_usage ("MLS.InitHpkeKey", init_key_usage_data me leaf_public_key))

val entropy_usage_for_init_key:
  principal -> bytes ->
  usage
let entropy_usage_for_init_key me leaf_public_key =
  (mk_hpke_entropy_usage ("MLS.InitHpkeKey", init_key_usage_data me leaf_public_key))

val is_init_key_sk: {|crypto_invariants|} -> trace -> principal -> bytes -> bytes -> prop
let is_init_key_sk #cinvs tr prin leaf_pk init_sk =
  bytes_invariant tr init_sk /\
  get_label tr init_sk == init_key_label prin (hpke_pk init_sk) /\
  init_sk `has_usage tr` init_key_usage prin leaf_pk

val is_init_key_pk: {|crypto_invariants|} -> trace -> principal -> bytes -> bytes -> prop
let is_init_key_pk #cinvs tr prin leaf_pk init_pk =
  bytes_invariant tr init_pk /\
  get_hpke_sk_label tr init_pk == init_key_label prin init_pk /\
  init_pk `has_hpke_sk_usage tr` (init_key_usage prin leaf_pk)

val bootstrap_init_key_state_pred: {|crypto_invariants|} -> local_state_predicate bootstrap_init_key_state
let bootstrap_init_key_state_pred #cinvs = {
  pred = (fun tr prin sid (content:bootstrap_init_key_state) ->
    is_publishable tr content.leaf_pk /\
    is_init_key_sk tr prin content.leaf_pk content.init_sk
  );
  pred_later = (fun tr1 tr2 prin sid content -> ());
  pred_knowable = (fun tr prin sid content ->
    assert(is_knowable_by (principal_typed_state_content_label prin (local_state_bootstrap_init_key_state.tag) sid content) tr content.leaf_pk)
  );
}

val has_bootstrap_init_key_state_invariant: {|protocol_invariants|} -> prop
let has_bootstrap_init_key_state_invariant #invs =
  has_local_state_predicate bootstrap_init_key_state_pred

val bootstrap_init_key_state_tag_and_invariant: {|crypto_invariants|} -> dtuple2 string local_bytes_state_predicate
let bootstrap_init_key_state_tag_and_invariant #ci = (|local_state_bootstrap_init_key_state.tag, local_state_predicate_to_local_bytes_state_predicate bootstrap_init_key_state_pred|)

val init_sk_to_init_key_label:
  principal -> bytes ->
  label
let init_sk_to_init_key_label prin init_sk =
  init_key_label prin (hpke_pk init_sk)

val mk_init_key:
  principal -> bytes ->
  traceful state_id
let mk_init_key prin leaf_pk =
  let* init_sk = my_mk_rand (const (init_key_usage prin leaf_pk)) (init_sk_to_init_key_label prin) 32 in
  let* sid = new_session_id prin in
  set_state prin sid { leaf_pk; init_sk; };*
  return sid

val mk_init_key_invariant:
  {|protocol_invariants|} ->
  prin:principal -> leaf_pk:bytes ->
  tr:trace ->
  Lemma
  (requires
    is_publishable tr leaf_pk /\
    trace_invariant tr /\
    has_bootstrap_init_key_state_invariant
  )
  (ensures (
    let (sid, tr_out) = mk_init_key prin leaf_pk tr in
    trace_invariant tr_out
  ))
let mk_init_key_invariant #invs prin leaf_pk tr = ()

val get_init_key_sk:
  principal -> state_id -> bytes ->
  traceful (option bytes)
let get_init_key_sk prin sid leaf_pk =
  let*? st = get_state prin sid in
  guard_tr (leaf_pk = st.leaf_pk);*?
  return (Some (st.init_sk))

val get_init_key_sk_invariant:
  {|protocol_invariants|} ->
  prin:principal -> sid:state_id -> leaf_pk:bytes ->
  tr:trace ->
  Lemma
  (requires
    trace_invariant tr /\
    has_bootstrap_init_key_state_invariant
  )
  (ensures (
    let (opt_init_sk, tr_out) = get_init_key_sk prin sid leaf_pk tr in
    tr_out == tr /\ (
      match opt_init_sk with
      | None -> True
      | Some init_sk -> is_init_key_sk tr prin leaf_pk init_sk
    )
  ))
let get_init_key_sk_invariant #invs prin sid leaf_pk tr = ()

val get_init_key_pk:
  principal -> state_id -> bytes ->
  traceful (option bytes)
let get_init_key_pk prin sid leaf_pk =
  let*? init_sk = get_init_key_sk prin sid leaf_pk in
  return (Some (hpke_pk init_sk))

val get_init_key_pk_invariant:
  {|protocol_invariants|} ->
  prin:principal -> sid:state_id -> leaf_pk:bytes ->
  tr:trace ->
  Lemma
  (requires
    trace_invariant tr /\
    has_bootstrap_init_key_state_invariant
  )
  (ensures (
    let (opt_init_pk, tr_out) = get_init_key_pk prin sid leaf_pk tr in
    tr_out == tr /\ (
      match opt_init_pk with
      | None -> True
      | Some init_pk -> is_init_key_pk tr prin leaf_pk init_pk
    )
  ))
let get_init_key_pk_invariant #invs prin sid leaf_pk tr = ()
