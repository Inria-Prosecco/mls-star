module MLS.Bootstrap.Symbolic.State.KeyPackageStore

open FStar.List.Tot { for_allP }
open Comparse
open DY.Core
open DY.Lib
open MLS.Crypto
open MLS.Symbolic
open MLS.Bootstrap.NetworkTypes
open MLS.TreeKEM.NetworkTypes
open MLS.Bootstrap.Symbolic.State.InitKey
open MLS.Bootstrap.KeyPackageRef
open MLS.Bootstrap.Symbolic.KeyPackageRef
open MLS.Bootstrap.Symbolic.Welcome
open MLS.TreeSync.Symbolic.AuthService.CredentialInterpretation

#set-options "--fuel 0 --ifuel 0  --z3cliopt 'smt.qi.eager_threshold=100'"

[@@ with_bytes bytes]
type key_package_store_key = {
  key_package_ref: bytes;
}

%splice [ps_key_package_store_key] (gen_parser (`key_package_store_key))
%splice [ps_key_package_store_key_is_well_formed] (gen_is_well_formed_lemma (`key_package_store_key))

[@@ with_bytes bytes]
type key_package_store_value_pre = {
  key_package: key_package_nt bytes tkt;
  signature_key_sid: state_id;
  leaf_node_key_sid: state_id;
  init_key_sid: state_id;
}

%splice [ps_key_package_store_value_pre] (gen_parser (`key_package_store_value_pre))
%splice [ps_key_package_store_value_pre_is_well_formed] (gen_is_well_formed_lemma (`key_package_store_value_pre))

[@@ with_bytes bytes]
type key_package_store_elem_pre = {
  key: key_package_store_key;
  value: key_package_store_value_pre;
}

%splice [ps_key_package_store_elem_pre] (gen_parser (`key_package_store_elem_pre))
%splice [ps_key_package_store_elem_pre_is_well_formed] (gen_is_well_formed_lemma (`key_package_store_elem_pre))

[@@ with_bytes bytes]
type key_package_store_pre = {
  [@@@ with_parser #bytes (ps_list (ps_key_package_store_elem_pre))]
  elems: list (key_package_store_elem_pre);
}

%splice [ps_key_package_store_pre] (gen_parser (`key_package_store_pre))
%splice [ps_key_package_store_pre_is_well_formed] (gen_is_well_formed_lemma (`key_package_store_pre))

instance local_state_bootstrap_key_package_store_state: local_state key_package_store_pre = {
  tag = "MLS.Bootstrap.KeyPackageStore";
  format = mk_parseable_serializeable ps_key_package_store_pre;
}

val key_package_store_elem_is_mine:
  principal -> key_package_store_elem_pre ->
  prop
let key_package_store_elem_is_mine me x =
  credential_to_principal x.value.key_package.tbs.leaf_node.data.credential == Some me

val bootstrap_key_package_store_state_pred: {|crypto_invariants|} -> local_state_predicate key_package_store_pre
let bootstrap_key_package_store_state_pred #cinvs = {
  pred = (fun tr prin sid (content:key_package_store_pre) ->
    is_well_formed _ (is_publishable tr) content /\
    for_allP (key_package_store_elem_is_mine prin) content.elems
  );
  pred_later = (fun tr1 tr2 prin sid content -> ());
  pred_knowable = (fun tr prin sid content -> ());
}

val has_bootstrap_key_package_store_state_invariant: {|protocol_invariants|} -> prop
let has_bootstrap_key_package_store_state_invariant #invs =
  has_local_state_predicate bootstrap_key_package_store_state_pred

val bootstrap_key_package_store_state_tag_and_invariant: {|crypto_invariants|} -> dtuple2 string local_bytes_state_predicate
let bootstrap_key_package_store_state_tag_and_invariant #ci = (|local_state_bootstrap_key_package_store_state.tag, local_state_predicate_to_local_bytes_state_predicate bootstrap_key_package_store_state_pred|)

[@@ with_bytes bytes]
type key_package_store_value_post = {
  key_package: key_package_nt bytes tkt;
  signature_key_sid: state_id;
  leaf_node_key_sid: state_id;
  init_key: bytes;
}

%splice [ps_key_package_store_value_post] (gen_parser (`key_package_store_value_post))
%splice [ps_key_package_store_value_post_is_well_formed] (gen_is_well_formed_lemma (`key_package_store_value_post))

[@@ with_bytes bytes]
type key_package_store_elem_post = {
  key: key_package_store_key;
  value: key_package_store_value_post;
}

%splice [ps_key_package_store_elem_post] (gen_parser (`key_package_store_elem_post))
%splice [ps_key_package_store_elem_post_is_well_formed] (gen_is_well_formed_lemma (`key_package_store_elem_post))

val key_package_store_value_pre_to_post:
  principal ->
  key_package_store_value_pre ->
  traceful (option key_package_store_value_post)
let key_package_store_value_pre_to_post me value =
  let*? init_key = get_init_key_sk me value.init_key_sid value.key_package.tbs.leaf_node.data.content in
  return (Some {
    key_package = value.key_package;
    signature_key_sid = value.signature_key_sid;
    leaf_node_key_sid = value.leaf_node_key_sid;
    init_key;
  })

#push-options "--fuel 1 --ifuel 1"
val key_package_store_pre_to_post:
  principal ->
  list (key_package_store_elem_pre) ->
  traceful (option (list (key_package_store_elem_post)))
let rec key_package_store_pre_to_post me l =
  match l with
  | [] -> return (Some [])
  | h::t ->
    let*? h_value_post = key_package_store_value_pre_to_post me h.value in
    let h_post = {
      key = h.key;
      value = h_value_post;
    } in
    let*? t_post = key_package_store_pre_to_post me t in
    return (Some (h_post::t_post))
#pop-options

#push-options "--fuel 1 --ifuel 1"
val lookup_key_package_store:
  list (key_package_store_elem_post) -> bytes ->
  option key_package_store_value_post
let rec lookup_key_package_store l key_package_ref =
  match l with
  | [] -> None
  | h::t ->
    if h.key.key_package_ref = key_package_ref then
      Some h.value
    else
      lookup_key_package_store t key_package_ref
#pop-options

[@"opaque_to_smt"]
val initialize_key_package_store:
  principal ->
  traceful state_id
let initialize_key_package_store me =
  let* sid = new_session_id me in
  let store: key_package_store_pre = { elems = [] } in
  set_state me sid store;*
  return sid

[@"opaque_to_smt"]
val extend_key_package_store:
  principal ->
  state_id -> key_package_store_value_pre ->
  traceful (option unit)
let extend_key_package_store me sid value =
  let*? key_package_ref = extract_result (compute_key_package_ref value.key_package) in
  let elem: key_package_store_elem_pre = {
    key = {key_package_ref};
    value;
  } in
  let*? store: key_package_store_pre = get_state me sid in
  let new_store: key_package_store_pre = { elems = elem::store.elems } in
  set_state me sid new_store;*
  return (Some ())

[@"opaque_to_smt"]
val get_store_lookup_function:
  principal -> state_id ->
  traceful (option (bytes -> option key_package_store_value_post))
let get_store_lookup_function me sid =
  let*? store_pre: key_package_store_pre = get_state me sid in
  let*? store_post = key_package_store_pre_to_post me store_pre.elems in
  return (Some (lookup_key_package_store store_post))

#push-options "--fuel 1 --ifuel 1"
val initialize_key_package_store_proof:
  {|protocol_invariants|} ->
  tr:trace ->
  me:principal ->
  Lemma
  (requires
    trace_invariant tr /\
    has_bootstrap_key_package_store_state_invariant
  )
  (ensures (
    let (_, tr_out) = initialize_key_package_store me tr in
    trace_invariant tr_out
  ))
let initialize_key_package_store_proof #invs tr me =
  reveal_opaque (`%initialize_key_package_store) (initialize_key_package_store);
  let (sid, tr) = new_session_id me tr in
  let store: key_package_store_pre = { elems = [] } in
  assert(for_allP (is_well_formed_prefix ps_key_package_store_elem_pre (is_publishable tr)) []);
  assert(is_well_formed _ (is_publishable tr) store)
#pop-options

#push-options "--fuel 1 --ifuel 1 --z3rlimit 50"
val extend_key_package_store_proof:
  {|protocol_invariants|} ->
  tr:trace ->
  me:principal ->
  sid:state_id -> value:key_package_store_value_pre ->
  Lemma
  (requires
    credential_to_principal value.key_package.tbs.leaf_node.data.credential == Some me /\
    is_well_formed _ (is_publishable tr) value.key_package /\
    trace_invariant tr /\
    has_bootstrap_key_package_store_state_invariant
  )
  (ensures (
    let (_, tr_out) = extend_key_package_store me sid value tr in
    trace_invariant tr_out
  ))
let extend_key_package_store_proof #invs tr me sid value =
  reveal_opaque (`%extend_key_package_store) (extend_key_package_store);
  match compute_key_package_ref value.key_package with
  | MLS.Result.Success key_package_ref -> (
    compute_key_package_ref_is_knowable_by tr public value.key_package;
    let elem: key_package_store_elem_pre = {
      key = {key_package_ref};
      value;
    } in
    assert((is_well_formed_prefix ps_key_package_store_elem_pre (is_publishable tr)) elem);
    let (opt_store, tr) = get_state me sid tr in
    match opt_store with
    | None -> ()
    | Some store -> (
      let new_store: key_package_store_pre = { elems = elem::store.elems } in
      assert(for_allP (is_well_formed_prefix ps_key_package_store_elem_pre (is_publishable tr)) new_store.elems);
      ()
    )
  )
  | _ -> ()
#pop-options

val key_package_store_value_to_hpke_sk:
  key_package_store_value_post ->
  MLS.Result.result (hpke_private_key bytes)
let key_package_store_value_to_hpke_sk value =
  let res = value.init_key in
  if not (length res = hpke_private_key_length #bytes) then
    MLS.Result.error ""
  else
    MLS.Result.return res

val key_package_store_value_to_key_package:
  key_package_store_value_post ->
  key_package_nt bytes tkt
let key_package_store_value_to_key_package value =
  value.key_package

val key_package_store_value_pre_to_post_proof:
  {|protocol_invariants|} ->
  tr:trace -> me:principal ->
  value_pre:key_package_store_value_pre ->
  Lemma
  (requires
    credential_to_principal value_pre.key_package.tbs.leaf_node.data.credential == Some me /\
    trace_invariant tr /\
    has_bootstrap_key_package_store_state_invariant /\
    has_bootstrap_init_key_state_invariant
  )
  (ensures (
    let (opt_value_post, tr_out) = key_package_store_value_pre_to_post me value_pre tr in
    tr_out == tr /\ (
      match opt_value_post with
      | None -> True
      | Some value_post ->
        one_kp_secrets_good tr me key_package_store_value_to_hpke_sk key_package_store_value_to_key_package value_post
    )
  ))
let key_package_store_value_pre_to_post_proof #invs tr me value_pre = ()

#push-options "--fuel 1 --ifuel 1 --z3rlimit 25"
val lookup_key_package_store_key_package_store_pre_to_post_proof:
  {|protocol_invariants|} ->
  tr:trace -> me:principal ->
  l:list (key_package_store_elem_pre) -> key_package_ref:bytes ->
  Lemma
  (requires
    for_allP (key_package_store_elem_is_mine me) l /\
    trace_invariant tr /\
    has_bootstrap_key_package_store_state_invariant /\
    has_bootstrap_init_key_state_invariant
  )
  (ensures (
    let (opt_l_post, tr_out) = key_package_store_pre_to_post me l tr in
    tr == tr_out /\ (
      match opt_l_post with
      | None -> True
      | Some l_post -> (
        match lookup_key_package_store l_post key_package_ref with
        | None -> True
        | Some kp_secrets ->
          one_kp_secrets_good tr me key_package_store_value_to_hpke_sk key_package_store_value_to_key_package kp_secrets
      )
    )
  ))
let rec lookup_key_package_store_key_package_store_pre_to_post_proof #invs tr me l key_package_ref =
  match l with
  | [] -> ()
  | h::t -> (
    key_package_store_value_pre_to_post_proof tr me h.value;
    lookup_key_package_store_key_package_store_pre_to_post_proof tr me t key_package_ref
  )
#pop-options

val get_store_lookup_function_proof:
  {|protocol_invariants|} ->
  tr:trace ->
  me:principal -> sid:state_id ->
  Lemma
  (requires
    trace_invariant tr /\
    has_bootstrap_key_package_store_state_invariant /\
    has_bootstrap_init_key_state_invariant
  )
  (ensures (
    let (opt_kp_ref_to_kp_secrets, tr_out) = get_store_lookup_function me sid tr in
    tr == tr_out /\ (
      match opt_kp_ref_to_kp_secrets with
      | None -> True
      | Some kp_ref_to_kp_secrets ->
        kp_secrets_good tr me key_package_store_value_to_hpke_sk key_package_store_value_to_key_package kp_ref_to_kp_secrets
    )
  ))
let get_store_lookup_function_proof #invs tr me sid =
  reveal_opaque (`%get_store_lookup_function) (get_store_lookup_function);
  let opt_store_pre, tr = get_state me sid tr in
  match opt_store_pre with
  | None -> ()
  | Some store_pre -> (
    FStar.Classical.forall_intro (FStar.Classical.move_requires (lookup_key_package_store_key_package_store_pre_to_post_proof tr me store_pre.elems))
  )
