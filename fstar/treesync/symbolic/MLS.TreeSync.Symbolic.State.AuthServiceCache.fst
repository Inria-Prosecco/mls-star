module MLS.TreeSync.Symbolic.State.AuthServiceCache

open Comparse
open DY.Core
open DY.Lib
open MLS.NetworkTypes
open MLS.Crypto.Derived
open MLS.TreeSync.NetworkTypes
open MLS.TreeSync.Symbolic.AuthService
open MLS.Symbolic
open MLS.TreeSync.Symbolic.State.SignatureKey
open MLS.TreeSync.Symbolic.AuthService.CredentialInterpretation

#set-options "--fuel 0 --ifuel 0"

(*** AS cache types & invariants ***)

[@@ with_bytes bytes]
type as_cache_key = {
  verification_key: signature_public_key_nt bytes;
  credential: credential_nt bytes;
}

%splice [ps_as_cache_key] (gen_parser (`as_cache_key))
%splice [ps_as_cache_key_is_well_formed] (gen_is_well_formed_lemma (`as_cache_key))

[@@ with_bytes bytes]
type as_cache_value = {
  token: dy_as_token;
}

%splice [ps_as_cache_value] (gen_parser (`as_cache_value))
%splice [ps_as_cache_value_is_well_formed] (gen_is_well_formed_lemma (`as_cache_value))

instance as_cache_types: map_types as_cache_key as_cache_value = {
  tag = "MLS.TreeSync.AuthServiceCache";
  ps_key_t = ps_as_cache_key;
  ps_value_t = ps_as_cache_value;
}

val as_cache_pred: {|crypto_invariants|} -> map_predicate as_cache_key as_cache_value #_
let as_cache_pred #ci = {
  pred = (fun tr prin state_id key value ->
    (dy_asp tr).credential_ok (key.verification_key, key.credential) value.token /\
    is_publishable tr key.verification_key /\
    is_well_formed_whole (ps_prefix_to_ps_whole ps_credential_nt) (is_publishable tr) key.credential
  );
  pred_later = (fun tr1 tr2 prin state_id key value -> ());
  pred_knowable = (fun tr prin state_id key value ->
    assert(is_well_formed_whole (ps_prefix_to_ps_whole ps_credential_nt) (is_knowable_by (principal_tag_state_label prin as_cache_types.tag state_id) tr) key.credential)
  );
}

val has_as_cache_invariant: {|protocol_invariants|} -> prop
let has_as_cache_invariant #invs =
  has_map_session_invariant as_cache_pred

val as_cache_tag_and_invariant: {|crypto_invariants|} -> dtuple2 string local_bytes_state_predicate
let as_cache_tag_and_invariant #ci = (|as_cache_types.tag, local_state_predicate_to_local_bytes_state_predicate (map_session_invariant as_cache_pred)|)

(*** AS cache API ***)

let initialize_as_cache = initialize_map as_cache_key as_cache_value
let add_verified_credential = add_key_value #as_cache_key #as_cache_value
let find_verified_credential = find_value #as_cache_key #as_cache_value

val verify_credential: principal -> state_id -> principal -> state_id -> traceful (option unit)
let verify_credential me as_cache_sid who who_sig_sid =
  let*? verification_key = get_signature_key_vk who who_sig_sid in
  let*? verification_key = extract_result (mk_mls_bytes verification_key "verify_credential" "verification_key") in
  let*? credential = return (principal_to_credential who) in
  let* time = get_time in
  add_verified_credential me as_cache_sid { verification_key; credential; } { token = { time } }

val initialize_as_cache_proof:
  {|protocol_invariants|} ->
  tr:trace ->
  me:principal ->
  Lemma
  (requires
    trace_invariant tr /\
    has_as_cache_invariant
  )
  (ensures (
    let (_, tr_out) = initialize_as_cache me tr in
    trace_invariant tr_out
  ))
let initialize_as_cache_proof #invs tr me =
  initialize_map_invariant as_cache_pred me tr

val verify_credential_proof:
  {|protocol_invariants|} ->
  tr:trace ->
  me:principal -> as_cache_sid:state_id ->
  who:principal -> who_sig_sid:state_id ->
  Lemma
  (requires
    trace_invariant tr /\
    has_treesync_signature_key_state_invariant /\
    has_as_cache_invariant
  )
  (ensures (
    let (_, tr_out) = verify_credential me as_cache_sid who who_sig_sid tr in
    trace_invariant tr_out
  ))
let verify_credential_proof #invs tr me as_cache_sid who who_sig_sid =
  let (opt_verification_key, tr) = get_signature_key_vk who who_sig_sid tr in
  match opt_verification_key with
  | None -> ()
  | Some verification_key -> (
    let (opt_verification_key, tr) = extract_result (mk_mls_bytes verification_key "verify_credential" "verification_key") tr in
    match opt_verification_key with
    | None -> ()
    | Some verification_key -> (
      match principal_to_credential who with
      | None -> ()
      | Some credential -> (
        principal_to_credential_to_principal who;
        is_publishable_principal_to_credential tr who;
        let key = { verification_key; credential; } in
        let value = { token = { time = trace_length tr } } in
        add_key_value_invariant as_cache_pred me as_cache_sid key value tr
      )
    )
    | _ -> ()
  )
