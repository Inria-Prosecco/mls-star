module MLS.TreeKEM.Symbolic.Traceful.ProcessProposal

open Comparse
open DY.Core
open DY.Lib
open MLS.TreeDEM.NetworkTypes
open MLS.TreeKEM.Symbolic.State.ProposalCache

(*** Process a Proposal ***)

/// Obtain a proposal from the network,
/// and store it in our proposal cache.

val process_proposal:
  me:principal -> proposal_cache_sid:state_id ->
  proposal_ts:timestamp -> sender:nat ->
  traceful (option unit)
let process_proposal me proposal_cache_sid proposal_ts sender =
  let*? proposal_bytes = recv_msg proposal_ts in
  let*? proposal: proposal_nt bytes = return (parse _ proposal_bytes) in
  remember_proposal me proposal_cache_sid proposal sender
