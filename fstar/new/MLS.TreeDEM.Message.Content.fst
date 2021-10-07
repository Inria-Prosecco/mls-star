module MLS.TreeDEM.Message.Content

open Lib.ByteSequence
open Lib.IntTypes
open MLS.NetworkTypes
open MLS.NetworkBinder
open MLS.Result

module NT = MLS.NetworkTypes

type message_content_type =
  | CT_application
  | CT_proposal
  | CT_commit

val valid_network_message_content_type: content_type_nt -> bool
let valid_network_message_content_type content_type =
  match content_type with
  | NT.CT_application -> true
  | NT.CT_proposal -> true
  | NT.CT_commit -> true
  | _ -> false

val network_to_message_content_type_tot: content_type:content_type_nt{valid_network_message_content_type content_type} -> message_content_type
let network_to_message_content_type_tot content_type =
  match content_type with
  | NT.CT_application -> CT_application
  | NT.CT_proposal -> CT_proposal
  | NT.CT_commit -> CT_commit

val network_to_message_content_type: content_type_nt -> result message_content_type
let network_to_message_content_type content_type =
  if valid_network_message_content_type content_type then
    return (network_to_message_content_type_tot content_type)
  else
    error "network_to_message_content_type: invalid content type"

val message_content_type_to_network: message_content_type -> content_type_nt
let message_content_type_to_network content_type =
  match content_type with
  | CT_application -> NT.CT_application
  | CT_proposal -> NT.CT_proposal
  | CT_commit -> NT.CT_commit

noeq type proposal =
  | Add: MLS.TreeSync.Types.leaf_package_t -> proposal
  | Update: MLS.TreeSync.Types.leaf_package_t -> proposal
  | Remove: nat -> proposal
  | PreSharedKey: pre_shared_key_id_nt -> proposal
  | ReInit: reinit_nt -> proposal
  | ExternalInit: external_init_nt -> proposal
  | AppAck: app_ack_nt -> proposal

noeq type proposal_or_ref =
  | Proposal: proposal -> proposal_or_ref
  | Reference: bytes -> proposal_or_ref

noeq type commit = {
  c_proposals: list proposal_or_ref;
  c_path: option (update_path_nt);
}

val message_content: message_content_type -> Type0
let message_content content_type =
  match content_type with
  | CT_application -> bytes
  | CT_proposal -> proposal
  | CT_commit -> commit

val network_to_proposal: proposal_nt -> result proposal
let network_to_proposal p =
  match p with
  | P_add add ->
    kp <-- key_package_to_treesync add.key_package;
    return (Add kp)
  | P_update update ->
    kp <-- key_package_to_treesync update.key_package;
    return (Update kp)
  | P_remove remove ->
    return (Remove (Lib.IntTypes.v remove.removed))
  | P_psk psk ->
    return (PreSharedKey psk.psk)
  | P_reinit reinit ->
    return (ReInit reinit)
  | P_external_init external_init ->
    return (ExternalInit external_init)
  | P_app_ack app_ack ->
    return (AppAck app_ack)
  | _ -> error "network_to_proposal: invalid proposal"

val network_to_proposal_or_ref: proposal_or_ref_nt -> result proposal_or_ref
let network_to_proposal_or_ref por =
  match por with
  | POR_proposal p ->
    res <-- network_to_proposal p;
    return (Proposal res)
  | POR_reference r ->
    return (Reference r)
  | _ -> error "network_to_proposal_or_ref: invalid proposal or ref"

val network_to_commit: commit_nt -> result commit
let network_to_commit c =
  proposals <-- mapM network_to_proposal_or_ref (Seq.seq_to_list c.proposals);
  path <-- network_to_option c.path;
  return ({
    c_proposals = proposals;
    c_path = path;
  })

val network_to_message_content: #content_type: content_type_nt{valid_network_message_content_type content_type} -> get_content_type content_type -> result (message_content (network_to_message_content_type_tot content_type))
let network_to_message_content #content_type content =
  match content_type with
  | NT.CT_application ->
    return content
  | NT.CT_proposal ->
    network_to_proposal content
  | NT.CT_commit ->
    network_to_commit content

let message_content_pair: Type0 = content_type:message_content_type & message_content content_type

val network_to_message_content_pair: mls_content_nt -> result message_content_pair
let network_to_message_content_pair content =
  let make_message_content_pair (#content_type:message_content_type) (msg:message_content content_type): message_content_pair =
    (|content_type, msg|)
  in
  match content with
  | MC_application msg
  | MC_proposal msg
  | MC_commit msg ->
    res <-- network_to_message_content msg;
    return (make_message_content_pair res)
  | _ -> error "network_to_message_content_pair: invalid content type"

val proposal_to_network: MLS.Crypto.ciphersuite -> proposal -> result proposal_nt
let proposal_to_network cs p =
  match p with
  | Add lp ->
    kp <-- treesync_to_keypackage cs lp;
    return (P_add ({key_package = kp}))
  | Update lp ->
    kp <-- treesync_to_keypackage cs lp;
    return (P_update ({key_package = kp}))
  | Remove id ->
    if not (id < pow2 32) then
      internal_failure "proposal_to_network: remove id too big"
    else
      return (P_remove ({removed = u32 id}))
  | PreSharedKey x -> return (P_psk ({psk = x}))
  | ReInit x -> return (P_reinit x)
  | ExternalInit x -> return (P_external_init x)
  | AppAck x -> return (P_app_ack x)

val proposal_or_ref_to_network: MLS.Crypto.ciphersuite -> proposal_or_ref -> result proposal_or_ref_nt
let proposal_or_ref_to_network cs por =
  match por with
  | Proposal p ->
    res <-- proposal_to_network cs p;
    return (POR_proposal res)
  | Reference ref ->
    if not (Seq.length ref < 256) then
      internal_failure "proposal_or_ref_to_network: reference too long"
    else
      return (POR_reference ref)

val commit_to_network: MLS.Crypto.ciphersuite -> commit -> result commit_nt
let commit_to_network cs c =
  proposals <-- mapM (proposal_or_ref_to_network cs) c.c_proposals;
  Seq.lemma_list_seq_bij proposals;
  if not (MLS.Parser.byte_length ps_proposal_or_ref proposals < pow2 32) then
    internal_failure "commit_to_network: proposals too long"
  else (
    return ({
      proposals = Seq.seq_of_list proposals;
      path = option_to_network c.c_path;
    })
  )

val message_content_to_network: #content_type:message_content_type -> MLS.Crypto.ciphersuite -> message_content content_type -> result mls_content_nt
let message_content_to_network #content_type cs msg =
  match content_type with
  | CT_application -> begin
    let msg: bytes = msg in
    if not (Seq.length msg < pow2 32) then
      internal_failure "message_content_to_network: application message too long"
    else
      return (MC_application msg)
  end
  | CT_proposal ->
    proposal <-- proposal_to_network cs msg;
    return (MC_proposal proposal)
  | CT_commit ->
    commit <-- commit_to_network cs msg;
    return (MC_commit commit)
