module TreeDEM.Message.Content

open Lib.ByteSequence
open NetworkTypes
open NetworkBinder
open Lib.Result

type message_content_type =
  | CT_application
  | CT_proposal
  | CT_commit

val valid_network_message_content_type: content_type_nt -> bool
let valid_network_message_content_type content_type =
  match content_type with
  | NetworkTypes.CT_application -> true
  | NetworkTypes.CT_proposal -> true
  | NetworkTypes.CT_commit -> true
  | _ -> false

val network_to_message_content_type_tot: content_type:content_type_nt{valid_network_message_content_type content_type} -> message_content_type
let network_to_message_content_type_tot content_type =
  match content_type with
  | NetworkTypes.CT_application -> CT_application
  | NetworkTypes.CT_proposal -> CT_proposal
  | NetworkTypes.CT_commit -> CT_commit

val network_to_message_content_type: content_type_nt -> result message_content_type
let network_to_message_content_type content_type =
  if valid_network_message_content_type content_type then
    return (network_to_message_content_type_tot content_type)
  else
    fail "network_to_message_content_type: invalid content type"

val message_content_type_to_network: message_content_type -> content_type_nt
let message_content_type_to_network content_type =
  match content_type with
  | CT_application -> NetworkTypes.CT_application
  | CT_proposal -> NetworkTypes.CT_proposal
  | CT_commit -> NetworkTypes.CT_commit

noeq type proposal =
  | Add: TreeSync.leaf_package_t -> proposal
  | Update: TreeSync.leaf_package_t -> proposal
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
    kp <-- TreeSyncTreeKEMBinder.key_package_to_treesync add.an_key_package;
    return (Add kp)
  | P_update update ->
    kp <-- TreeSyncTreeKEMBinder.key_package_to_treesync update.un_key_package;
    return (Update kp)
  | P_remove remove ->
    return (Remove (Lib.IntTypes.v remove.rn_removed))
  | P_psk psk ->
    return (PreSharedKey psk.pskn_psk)
  | P_reinit reinit ->
    return (ReInit reinit)
  | P_external_init external_init ->
    return (ExternalInit external_init)
  | P_app_ack app_ack ->
    return (AppAck app_ack)
  | _ -> fail "network_to_proposal: invalid proposal"

val network_to_proposal_or_ref: proposal_or_ref_nt -> result proposal_or_ref
let network_to_proposal_or_ref por =
  match por with
  | POR_proposal p ->
    res <-- network_to_proposal p;
    return (Proposal res)
  | POR_reference r ->
    return (Reference r)
  | _ -> fail "network_to_proposal_or_ref: invalid proposal or ref"

val network_to_commit: commit_nt -> result commit
let network_to_commit c =
  proposals <-- mapM network_to_proposal_or_ref (Seq.seq_to_list c.cn_proposals);
  path <-- network_to_option c.cn_path;
  return ({
    c_proposals = proposals;
    c_path = path;
  })

val network_to_message_content: #content_type: content_type_nt{valid_network_message_content_type content_type} -> get_content_type content_type -> result (message_content (network_to_message_content_type_tot content_type))
let network_to_message_content #content_type content =
  match content_type with
  | NetworkTypes.CT_application ->
    return content
  | NetworkTypes.CT_proposal ->
    network_to_proposal content
  | NetworkTypes.CT_commit ->
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
  | _ -> fail "network_to_message_content_pair: invalid content type"

