module MLS.TreeKEM.Symbolic.State.UpdateCache

open Comparse
open DY.Core
open DY.Lib
open MLS.Symbolic
open MLS.TreeSync.NetworkTypes
open MLS.TreeKEM.NetworkTypes
open MLS.TreeSync.Symbolic.AuthService.CredentialInterpretation

#set-options "--fuel 0 --ifuel 0  --z3cliopt 'smt.qi.eager_threshold=100'"

[@@ with_bytes bytes]
type update_cache_key  = {
  leaf_node: leaf_node_nt bytes tkt;
}

%splice [ps_update_cache_key] (gen_parser (`update_cache_key))
%splice [ps_update_cache_key_is_well_formed] (gen_is_well_formed_lemma (`update_cache_key))

[@@ with_bytes bytes]
type update_cache_value  = {
  leaf_sk_sid: state_id;
}

%splice [ps_update_cache_value] (gen_parser (`update_cache_value))
%splice [ps_update_cache_value_is_well_formed] (gen_is_well_formed_lemma (`update_cache_value))

instance update_cache_types: map_types update_cache_key update_cache_value = {
  tag = "MLS.TreeKEM.UpdateCache";
  ps_key_t = ps_update_cache_key;
  ps_value_t = ps_update_cache_value;
}

val update_cache_pred: {|crypto_invariants|} -> map_predicate update_cache_key update_cache_value
let update_cache_pred #ci = {
  pred = (fun tr me sid key value ->
    is_well_formed _ (is_publishable tr) key.leaf_node /\
    credential_to_principal key.leaf_node.data.credential == Some me
  );
  pred_later = (fun tr1 tr2 me sid key value -> ());
  pred_knowable = (fun tr me sid key value ->
    is_well_formed_prefix_weaken ps_update_cache_key (is_publishable tr) (is_knowable_by (principal_tag_state_label me update_cache_types.tag sid) tr) key;
    assert(is_well_formed_prefix ps_state_id (is_knowable_by (principal_tag_state_label me update_cache_types.tag sid) tr) value.leaf_sk_sid)
  );
}

val has_update_cache_invariant: {|protocol_invariants|} -> prop
let has_update_cache_invariant #invs =
  has_map_session_invariant update_cache_pred

val update_cache_tag_and_invariant: {|crypto_invariants|} -> dtuple2 string local_bytes_state_predicate
let update_cache_tag_and_invariant #ci = (|update_cache_types.tag, local_state_predicate_to_local_bytes_state_predicate (map_session_invariant update_cache_pred)|)

(*** update cache API ***)

let initialize_update_cache = initialize_map update_cache_key update_cache_value

[@"opaque_to_smt"]
val find_update_leaf_sk:
  principal -> state_id ->
  leaf_node_nt bytes tkt ->
  traceful (option state_id)
let find_update_leaf_sk me sid leaf_node =
  let*? v = find_value me sid { leaf_node } in
  return (Some v.leaf_sk_sid)

val find_update_leaf_sk_proof:
  {|protocol_invariants|} ->
  me:principal -> sid:state_id ->
  leaf_node:leaf_node_nt bytes tkt ->
  tr:trace ->
  Lemma
  (requires
    trace_invariant tr /\
    has_update_cache_invariant
  )
  (ensures (
    let (opt_leaf_sk_sid, tr_out) = find_update_leaf_sk me sid leaf_node tr in
    tr_out == tr /\ (
      match opt_leaf_sk_sid with
      | None -> True
      | Some leaf_sk_sid ->
        credential_to_principal leaf_node.data.credential == Some me
    )
  ))
let find_update_leaf_sk_proof #invs me sid leaf_node tr =
  reveal_opaque (`%find_update_leaf_sk) (find_update_leaf_sk me sid leaf_node)

[@"opaque_to_smt"]
val remember_update_leaf_sk:
  principal -> state_id ->
  leaf_node_nt bytes tkt -> state_id ->
  traceful (option unit)
let remember_update_leaf_sk me sid leaf_node leaf_sk_sid =
  add_key_value me sid {leaf_node} {leaf_sk_sid}

val remember_update_leaf_sk_proof:
  {|protocol_invariants|} ->
  me:principal -> sid:state_id ->
  leaf_node:leaf_node_nt bytes tkt -> leaf_sk_sid:state_id ->
  tr:trace ->
  Lemma
  (requires
    is_well_formed _ (is_publishable tr) leaf_node /\
    credential_to_principal leaf_node.data.credential == Some me /\
    trace_invariant tr /\
    has_update_cache_invariant
  )
  (ensures (
    let (_, tr_out) = remember_update_leaf_sk me sid leaf_node leaf_sk_sid tr in
    trace_invariant tr_out
  ))
let remember_update_leaf_sk_proof #invs me sid leaf_node leaf_sk_sid tr =
  reveal_opaque (`%remember_update_leaf_sk) (remember_update_leaf_sk me sid leaf_node leaf_sk_sid)
