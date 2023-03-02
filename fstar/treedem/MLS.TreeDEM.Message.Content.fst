module MLS.TreeDEM.Message.Content

open Comparse
open MLS.NetworkTypes
open MLS.TreeSync.NetworkTypes
open MLS.TreeKEM.NetworkTypes
open MLS.TreeDEM.NetworkTypes
open MLS.Result

type proposal (bytes:Type0) {|bytes_like bytes|} =
  | Add: key_package_nt bytes tkt -> proposal bytes
  | Update: leaf_node_nt bytes tkt -> proposal bytes
  | Remove: nat -> proposal bytes
  | PreSharedKey: pre_shared_key_id_nt bytes -> proposal bytes
  | ReInit: reinit_nt bytes -> proposal bytes
  | ExternalInit: external_init_nt bytes -> proposal bytes
  | GroupContextExtensions: group_context_extensions_nt bytes -> proposal bytes

type proposal_or_ref (bytes:Type0) {|bytes_like bytes|} =
  | Proposal: proposal bytes -> proposal_or_ref bytes
  | Reference: proposal_ref_nt bytes -> proposal_or_ref bytes

type commit (bytes:Type0) {|bytes_like bytes|} = {
  c_proposals: list (proposal_or_ref bytes);
  c_path: option (update_path_nt bytes);
}

val message_bare_content:
  bytes:Type0 -> {|bytes_like bytes|} ->
  content_type_nt ->
  Type0
let message_bare_content bytes #bl content_type =
  match content_type with
  | CT_application -> bytes
  | CT_proposal -> proposal bytes
  | CT_commit -> commit bytes

val network_to_proposal:
  #bytes:Type0 -> {|bytes_like bytes|} ->
  proposal_nt bytes ->
  result (proposal bytes)
let network_to_proposal #bytes #bl p =
  match p with
  | P_add add ->
    return (Add add.key_package)
  | P_update update ->
    return (Update update.leaf_node)
  | P_remove remove ->
    return (Remove remove.removed)
  | P_psk psk ->
    return (PreSharedKey psk.psk)
  | P_reinit reinit ->
    return (ReInit reinit)
  | P_external_init external_init ->
    return (ExternalInit external_init)
  | P_group_context_extensions group_context_extensions ->
    return (GroupContextExtensions group_context_extensions)
  | _ -> error "network_to_proposal: invalid proposal"

val network_to_proposal_or_ref:
  #bytes:Type0 -> {|bytes_like bytes|} ->
  proposal_or_ref_nt bytes ->
  result (proposal_or_ref bytes)
let network_to_proposal_or_ref #bytes #bl por =
  match por with
  | POR_proposal p ->
    let? res = network_to_proposal p in
    return (Proposal res)
  | POR_reference r ->
    return (Reference r)
  | _ -> error "network_to_proposal_or_ref: invalid proposal or ref"

val network_to_commit:
  #bytes:Type0 -> {|bytes_like bytes|} ->
  commit_nt bytes ->
  result (commit bytes)
let network_to_commit #bytes #bl c =
  let? proposals = mapM network_to_proposal_or_ref c.proposals in
  return ({
    c_proposals = proposals;
    c_path = c.path;
  })

val network_to_message_bare_content:
  #bytes:Type0 -> {|bytes_like bytes|} ->
  #content_type: content_type_nt ->
  mls_untagged_content_nt bytes content_type ->
  result (message_bare_content bytes content_type)
let network_to_message_bare_content #bytes #bl #content_type content =
  match content_type with
  | CT_application ->
    return content
  | CT_proposal ->
    network_to_proposal (content <: proposal_nt bytes)
  | CT_commit ->
    network_to_commit (content <: commit_nt bytes)

let message_content_pair (bytes:Type0) {|bytes_like bytes|}: Type0 = content_type:content_type_nt & message_bare_content bytes content_type

val network_to_message_content_pair:
  #bytes:Type0 -> {|bytes_like bytes|} ->
  mls_tagged_content_nt bytes ->
  result (message_content_pair bytes)
let network_to_message_content_pair #bytes #bl content =
  let make_message_content_pair #bytes #bl (#content_type:content_type_nt) (msg:message_bare_content bytes content_type): message_content_pair bytes =
    (|content_type, msg|)
  in
  match content.content_type with
  | CT_application
  | CT_proposal
  | CT_commit -> (
    let? res = network_to_message_bare_content content.content in
    return (make_message_content_pair res)
  )
  | _ -> error "network_to_message_content_pair: invalid content type"

val proposal_to_network:
  #bytes:Type0 -> {|bytes_like bytes|} ->
  proposal bytes ->
  result (proposal_nt bytes)
let proposal_to_network #bytes #bl p =
  match p with
  | Add kp ->
    return (P_add ({key_package = kp}))
  | Update lp ->
    return (P_update ({leaf_node = lp}))
  | Remove id ->
    if not (id < pow2 32) then
      internal_failure "proposal_to_network: invalid id"
    else
      return (P_remove ({removed = id}))
  | PreSharedKey x -> return (P_psk ({psk = x}))
  | ReInit x -> return (P_reinit x)
  | ExternalInit x -> return (P_external_init x)
  | GroupContextExtensions x -> return (P_group_context_extensions x)

val proposal_or_ref_to_network:
  #bytes:Type0 -> {|bytes_like bytes|} ->
  proposal_or_ref bytes ->
  result (proposal_or_ref_nt bytes)
let proposal_or_ref_to_network #bytes #bl por =
  match por with
  | Proposal p ->
    let? res = proposal_to_network p in
    return (POR_proposal res)
  | Reference ref ->
    if not (length (ref <: bytes) < pow2 30) then
      internal_failure "proposal_or_ref_to_network: reference too long"
    else
      return (POR_reference ref)

val commit_to_network:
  #bytes:Type0 -> {|bytes_like bytes|} ->
  commit bytes ->
  result (commit_nt bytes)
let commit_to_network #bytes #bl c =
  let? proposals = mapM (proposal_or_ref_to_network) c.c_proposals in
  if not (Comparse.bytes_length ps_proposal_or_ref_nt proposals < pow2 30) then
    internal_failure "commit_to_network: proposals too long"
  else (
    return ({
      proposals = proposals;
      path = c.c_path;
    })
  )

val message_bare_content_to_network:
  #bytes:Type0 -> {|bytes_like bytes|} ->
  #content_type:content_type_nt ->
  message_bare_content bytes content_type ->
  result (mls_untagged_content_nt bytes content_type)
let message_bare_content_to_network #bytes #bl #content_type content =
  match content_type with
  | CT_application ->
    if not (length (content <: bytes) < pow2 30) then
      error "message_bare_content_to_network: application content is too long"
    else
      return content
  | CT_proposal ->
    proposal_to_network (content <: proposal bytes)
  | CT_commit ->
    commit_to_network (content <: commit bytes)

val message_content_pair_to_network:
  #bytes:Type0 -> {|bytes_like bytes|} ->
  #content_type:content_type_nt ->
  message_bare_content bytes content_type ->
  result (mls_tagged_content_nt bytes)
let message_content_pair_to_network #bytes #cb #content_type msg =
  let? network_content = message_bare_content_to_network msg in
  match content_type with
  | CT_application -> return ({content_type = content_type; content = network_content;} <: mls_tagged_content_nt bytes)
  | CT_proposal -> return ({content_type = content_type; content = network_content;} <: mls_tagged_content_nt bytes)
  | CT_commit -> return ({content_type = content_type; content = network_content;} <: mls_tagged_content_nt bytes)
