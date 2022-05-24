module MLS.TreeDEM.Message.Content

open Comparse
open MLS.NetworkTypes
open MLS.NetworkBinder
open MLS.Result

module NT = MLS.NetworkTypes

type message_content_type =
  | CT_application
  | CT_proposal
  | CT_commit

val network_to_message_content_type: content_type:content_type_nt -> message_content_type
let network_to_message_content_type content_type =
  match content_type with
  | NT.CT_application () -> CT_application
  | NT.CT_proposal () -> CT_proposal
  | NT.CT_commit () -> CT_commit

val message_content_type_to_network: message_content_type -> content_type_nt
let message_content_type_to_network content_type =
  match content_type with
  | CT_application -> NT.CT_application ()
  | CT_proposal -> NT.CT_proposal ()
  | CT_commit -> NT.CT_commit ()

noeq type proposal (bytes:Type0) {|bytes_like bytes|} =
  | Add: MLS.TreeSync.Types.leaf_package_t bytes -> proposal bytes
  | Update: MLS.TreeSync.Types.leaf_package_t bytes -> proposal bytes
  | Remove: key_package_ref_nt bytes -> proposal bytes
  | PreSharedKey: pre_shared_key_id_nt bytes -> proposal bytes
  | ReInit: reinit_nt bytes -> proposal bytes
  | ExternalInit: external_init_nt bytes -> proposal bytes
  | AppAck: app_ack_nt bytes -> proposal bytes
  | GroupContextExtensions: group_context_extensions_nt bytes -> proposal bytes

noeq type proposal_or_ref (bytes:Type0) {|bytes_like bytes|} =
  | Proposal: proposal bytes -> proposal_or_ref bytes
  | Reference: proposal_ref_nt bytes -> proposal_or_ref bytes

noeq type commit (bytes:Type0) {|bytes_like bytes|} = {
  c_proposals: list (proposal_or_ref bytes);
  c_path: option (update_path_nt bytes);
}

val message_content: bytes:Type0 -> {|bytes_like bytes|} -> message_content_type -> Type0
let message_content bytes #bl content_type =
  match content_type with
  | CT_application -> bytes
  | CT_proposal -> proposal bytes
  | CT_commit -> commit bytes

val network_to_proposal: #bytes:Type0 -> {|bytes_like bytes|} -> proposal_nt bytes -> result (proposal bytes)
let network_to_proposal #bytes #bl p =
  match p with
  | P_add add ->
    kp <-- key_package_to_treesync add.key_package;
    return (Add kp)
  | P_update update ->
    kp <-- key_package_to_treesync update.key_package;
    return (Update kp)
  | P_remove remove ->
    return (Remove remove.removed)
  | P_psk psk ->
    return (PreSharedKey psk.psk)
  | P_reinit reinit ->
    return (ReInit reinit)
  | P_external_init external_init ->
    return (ExternalInit external_init)
  | P_app_ack app_ack ->
    return (AppAck app_ack)
  | P_group_context_extensions group_context_extensions ->
    return (GroupContextExtensions group_context_extensions)
  | _ -> error "network_to_proposal: invalid proposal"

val network_to_proposal_or_ref: #bytes:Type0 -> {|bytes_like bytes|} -> proposal_or_ref_nt bytes -> result (proposal_or_ref bytes)
let network_to_proposal_or_ref #bytes #bl por =
  match por with
  | POR_proposal p ->
    res <-- network_to_proposal p;
    return (Proposal res)
  | POR_reference r ->
    return (Reference r)
  | _ -> error "network_to_proposal_or_ref: invalid proposal or ref"

val network_to_commit: #bytes:Type0 -> {|bytes_like bytes|} -> commit_nt bytes -> result (commit bytes)
let network_to_commit #bytes #bl c =
  proposals <-- mapM network_to_proposal_or_ref (Seq.seq_to_list c.proposals);
  return ({
    c_proposals = proposals;
    c_path = c.path;
  })

val network_to_message_content: #bytes:Type0 -> {|bytes_like bytes|} -> #content_type: content_type_nt -> mls_message_content_nt bytes content_type -> result (message_content bytes (network_to_message_content_type content_type))
let network_to_message_content #bytes #bl #content_type content =
  match content_type with
  | NT.CT_application () ->
    return content
  | NT.CT_proposal () ->
    network_to_proposal (content <: proposal_nt bytes)
  | NT.CT_commit () ->
    network_to_commit (content <: commit_nt bytes)

let message_content_pair (bytes:Type0) {|bytes_like bytes|}: Type0 = content_type:message_content_type & message_content bytes content_type

val network_to_message_content_pair: #bytes:Type0 -> {|bytes_like bytes|} -> mls_content_nt bytes -> result (message_content_pair bytes)
let network_to_message_content_pair #bytes #bl content =
  let make_message_content_pair #bytes #bl (#content_type:message_content_type) (msg:message_content bytes content_type): message_content_pair bytes =
    (|content_type, msg|)
  in
  match content with
  | MC_application msg
  | MC_proposal msg
  | MC_commit msg ->
    res <-- network_to_message_content msg;
    return (make_message_content_pair res)
  | _ -> error "network_to_message_content_pair: invalid content type"

//TODO: not a crypto_bytes in latest draft (14)?
val proposal_to_network: #bytes:Type0 -> {|MLS.Crypto.crypto_bytes bytes|} -> proposal bytes -> result (proposal_nt bytes)
let proposal_to_network #bytes #cb p =
  match p with
  | Add lp ->
    kp <-- treesync_to_keypackage lp;
    return (P_add ({key_package = kp}))
  | Update lp ->
    kp <-- treesync_to_keypackage lp;
    return (P_update ({key_package = kp}))
  | Remove id ->
      return (P_remove ({removed = id}))
  | PreSharedKey x -> return (P_psk ({psk = x}))
  | ReInit x -> return (P_reinit x)
  | ExternalInit x -> return (P_external_init x)
  | AppAck x -> return (P_app_ack x)
  | GroupContextExtensions x -> return (P_group_context_extensions x)

//TODO: not a crypto_bytes in latest draft (14)?
val proposal_or_ref_to_network: #bytes:Type0 -> {|MLS.Crypto.crypto_bytes bytes|} -> proposal_or_ref bytes -> result (proposal_or_ref_nt bytes)
let proposal_or_ref_to_network #bytes #bl por =
  match por with
  | Proposal p ->
    res <-- proposal_to_network p;
    return (POR_proposal res)
  | Reference ref ->
    if not (length (ref <: bytes) < 256) then
      internal_failure "proposal_or_ref_to_network: reference too long"
    else
      return (POR_reference ref)

val commit_to_network: #bytes:Type0 -> {|MLS.Crypto.crypto_bytes bytes|} -> commit bytes -> result (commit_nt bytes)
let commit_to_network #bytes #cb c =
  proposals <-- mapM (proposal_or_ref_to_network) c.c_proposals;
  Seq.lemma_list_seq_bij proposals;
  if not (Comparse.bytes_length ps_proposal_or_ref_nt proposals < pow2 32) then
    internal_failure "commit_to_network: proposals too long"
  else (
    return ({
      proposals = Seq.seq_of_list proposals;
      path = c.c_path;
    })
  )

val message_content_to_network: #bytes:Type0 -> {|MLS.Crypto.crypto_bytes bytes|} -> #content_type:message_content_type -> message_content bytes content_type -> result (mls_message_content_nt bytes (message_content_type_to_network content_type))
let message_content_to_network #bytes #bl #content_type content =
  match content_type with
  | CT_application ->
    if not (length (content <: bytes) < pow2 32) then
      error "message_content_to_network: application content is too long"
    else
      return content
  | CT_proposal ->
    proposal_to_network (content <: proposal bytes)
  | CT_commit ->
    commit_to_network (content <: commit bytes)

val message_content_pair_to_network: #bytes:Type0 -> {|MLS.Crypto.crypto_bytes bytes|} -> #content_type:message_content_type -> message_content bytes content_type -> result (mls_content_nt bytes)
let message_content_pair_to_network #bytes #cb #content_type msg =
  content <-- message_content_to_network msg;
  match content_type with
  | CT_application -> return (MC_application content)
  | CT_proposal -> return (MC_proposal content)
  | CT_commit -> return (MC_commit content)
