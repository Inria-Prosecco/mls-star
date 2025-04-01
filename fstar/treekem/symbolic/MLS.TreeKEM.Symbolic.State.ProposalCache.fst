module MLS.TreeKEM.Symbolic.State.ProposalCache

open Comparse
open DY.Core
open DY.Lib
open MLS.Crypto
open MLS.Symbolic
open MLS.TreeDEM.NetworkTypes
open MLS.TreeKEM.Symbolic.KeySchedule
open MLS.Crypto.Derived.Symbolic.RefHash

#set-options "--fuel 0 --ifuel 0  --z3cliopt 'smt.qi.eager_threshold=100'"

[@@ with_bytes bytes]
type proposal_cache_key  = {
  proposal_ref: bytes;
}

%splice [ps_proposal_cache_key] (gen_parser (`proposal_cache_key))
%splice [ps_proposal_cache_key_is_well_formed] (gen_is_well_formed_lemma (`proposal_cache_key))

[@@ with_bytes bytes]
type proposal_and_sender  = {
  proposal: proposal_nt bytes;
  sender:nat;
}

%splice [ps_proposal_and_sender] (gen_parser (`proposal_and_sender))
%splice [ps_proposal_and_sender_is_well_formed] (gen_is_well_formed_lemma (`proposal_and_sender))

instance proposal_cache_types: map_types proposal_cache_key proposal_and_sender = {
  tag = "MLS.TreeKEM.ProposalCache";
  ps_key_t = ps_proposal_cache_key;
  ps_value_t = ps_proposal_and_sender;
}

val proposal_cache_pred: {|crypto_invariants|} -> map_predicate proposal_cache_key proposal_and_sender #_
let proposal_cache_pred #ci = {
  pred = (fun tr prin state_id key value ->
    is_publishable tr key.proposal_ref /\
    is_well_formed _ (is_publishable tr) value.proposal /\
    MLS.Result.Success key.proposal_ref == make_proposal_ref (serialize _ value.proposal)
  );
  pred_later = (fun tr1 tr2 prin state_id key value -> ());
  pred_knowable = (fun tr prin state_id key value ->
    assert(is_well_formed_prefix ps_nat (is_publishable tr) value.sender);
    is_well_formed_prefix_weaken ps_proposal_and_sender (is_publishable tr) (is_knowable_by (principal_tag_state_label prin proposal_cache_types.tag state_id) tr) value
  );
}

val has_proposal_cache_invariant: {|protocol_invariants|} -> prop
let has_proposal_cache_invariant #invs =
  has_map_session_invariant proposal_cache_pred

val proposal_cache_tag_and_invariant: {|crypto_invariants|} -> dtuple2 string local_bytes_state_predicate
let proposal_cache_tag_and_invariant #ci = (|proposal_cache_types.tag, local_state_predicate_to_local_bytes_state_predicate (map_session_invariant proposal_cache_pred)|)

(*** Proposal cache API ***)

let initialize_proposal_cache = initialize_map proposal_cache_key proposal_and_sender

#push-options "--fuel 1 --ifuel 1"
val _retrieve_one_proposal:
  principal ->
  state_id -> nat -> proposal_or_ref_nt bytes ->
  traceful (option (proposal_and_sender))
let _retrieve_one_proposal me sid my_index proposal_or_ref =
  match proposal_or_ref with
  | POR_proposal proposal ->
    return (Some {proposal; sender = my_index})
  | POR_reference proposal_ref ->
    find_value me sid { proposal_ref }
#pop-options

#push-options "--fuel 1 --ifuel 1"
val _retrieve_one_proposal_proof:
  {|protocol_invariants|} ->
  tr:trace -> me:principal ->
  sid:state_id -> my_index:nat -> proposal_or_ref:proposal_or_ref_nt bytes ->
  Lemma
  (requires
    trace_invariant tr /\
    has_proposal_cache_invariant
  )
  (ensures (
    let (opt_res, tr_out) = _retrieve_one_proposal me sid my_index proposal_or_ref tr in
    tr_out == tr /\ (
      match opt_res with
      | None -> True
      | Some res ->
        proposal_or_ref_rel proposal_or_ref res.proposal
    )
  ))
let _retrieve_one_proposal_proof #invs tr me sid my_index proposal_or_ref = ()
#pop-options

#push-options "--fuel 1 --ifuel 1"
val retrieve_proposals:
  principal ->
  state_id -> nat -> list (proposal_or_ref_nt bytes) ->
  traceful (option (list (proposal_and_sender)))
let rec retrieve_proposals me sid my_index proposal_or_refs =
  match proposal_or_refs with
  | [] -> return (Some [])
  | h::t ->
    let*? res_h = _retrieve_one_proposal me sid my_index h in
    let*? res_t = retrieve_proposals me sid my_index t in
    return (Some (res_h::res_t))
#pop-options

#push-options "--fuel 1 --ifuel 1"
val retrieve_proposals_proof:
  {|protocol_invariants|} ->
  tr:trace -> me:principal ->
  sid:state_id -> my_index:nat -> proposal_or_refs:list (proposal_or_ref_nt bytes) ->
  Lemma
  (requires
    for_allP (is_well_formed_prefix ps_proposal_or_ref_nt (is_publishable tr)) proposal_or_refs /\
    trace_invariant tr /\
    has_proposal_cache_invariant
  )
  (ensures (
    let (opt_res, tr_out) = retrieve_proposals me sid my_index proposal_or_refs tr in
    tr_out == tr /\ (
      match opt_res with
      | None -> True
      | Some res -> (
        proposal_or_refs_rel proposal_or_refs (List.Tot.map (Mkproposal_and_sender?.proposal) res) /\
        for_allP (is_well_formed_prefix ps_proposal_nt (is_publishable tr)) (List.Tot.map Mkproposal_and_sender?.proposal res)
      )
    )
  ))
let rec retrieve_proposals_proof #invs tr me sid my_index proposal_or_refs =
  match proposal_or_refs with
  | [] -> ()
  | h::t -> (
    _retrieve_one_proposal_proof tr me sid my_index h;
    let opt_res_h, tr = _retrieve_one_proposal me sid my_index h tr in
    match opt_res_h with
    | None -> ()
    | Some res_h -> (
      retrieve_proposals_proof tr me sid my_index t
    )
  )
#pop-options

val remember_proposal:
  principal -> state_id ->
  proposal_nt bytes -> nat ->
  traceful (option unit)
let remember_proposal me sid proposal sender =
  let*? proposal_ref = extract_result (make_proposal_ref (serialize _ proposal)) in
  let key = { proposal_ref } in
  let value = { proposal; sender; } in
  add_key_value me sid key value

val remember_proposal_proof:
  {|protocol_invariants|} ->
  tr:trace ->
  me:principal -> sid:state_id ->
  proposal:proposal_nt bytes -> sender:nat ->
  Lemma
  (requires
    is_well_formed _ (is_publishable tr) proposal /\
    trace_invariant tr /\
    has_proposal_cache_invariant
  )
  (ensures (
    let (_, tr_out) = remember_proposal me sid proposal sender tr in
    trace_invariant tr_out
  ))
let remember_proposal_proof #invs tr me sid proposal sender =
  make_proposal_ref_is_knowable_by tr public (serialize _ proposal)
