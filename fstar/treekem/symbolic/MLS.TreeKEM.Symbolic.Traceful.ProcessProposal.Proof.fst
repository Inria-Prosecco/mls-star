module MLS.TreeKEM.Symbolic.Traceful.ProcessProposal.Proof

open Comparse
open DY.Core
open DY.Lib
open MLS.TreeDEM.NetworkTypes
open MLS.TreeKEM.Symbolic.State.ProposalCache
open MLS.TreeKEM.Symbolic.Traceful.AllInvariants
open MLS.TreeKEM.Symbolic.Traceful.ProcessProposal

(*** Process a Proposal, proof ***)

val process_proposal_proof:
  {|protocol_invariants|} ->
  me:principal -> proposal_cache_sid:state_id ->
  proposal_ts:timestamp -> sender:nat ->
  tr:trace ->
  Lemma
  (requires
    trace_invariant tr /\
    has_treesync_and_treekem_invariants
  )
  (ensures(
    let _, tr_out = process_proposal me proposal_cache_sid proposal_ts sender tr in
    trace_invariant tr_out
  ))
let process_proposal_proof me proposal_cache_sid proposal_ts sender tr =
  let opt_proposal_bytes, tr = recv_msg proposal_ts tr in
  match opt_proposal_bytes with
  | None -> ()
  | Some proposal_bytes -> (
    parse_wf_lemma (proposal_nt bytes) (is_publishable tr) proposal_bytes;
    match parse _ proposal_bytes with
    | None -> ()
    | Some proposal -> (
      remember_proposal_proof tr me proposal_cache_sid proposal sender
    )
  )
