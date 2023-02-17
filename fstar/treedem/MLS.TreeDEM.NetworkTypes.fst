module MLS.TreeDEM.NetworkTypes

open Comparse
open MLS.NetworkTypes
open MLS.TreeSync.NetworkTypes
open MLS.TreeKEM.NetworkTypes

(*** PSKs ***)

type psk_type_nt =
  | [@@@ with_num_tag 1 1] PSKT_external: psk_type_nt
  | [@@@ with_num_tag 1 2] PSKT_resumption: psk_type_nt

%splice [ps_psk_type_nt] (gen_parser (`psk_type_nt))

type resumption_psk_usage_nt =
  | [@@@ with_num_tag 1 1] RPSKU_application: resumption_psk_usage_nt
  | [@@@ with_num_tag 1 2] RPSKU_reinit: resumption_psk_usage_nt
  | [@@@ with_num_tag 1 3] RPSKU_branch: resumption_psk_usage_nt

%splice [ps_resumption_psk_usage_nt] (gen_parser (`resumption_psk_usage_nt))

type pre_shared_key_id_nt (bytes:Type0) {|bytes_like bytes|} =
  | [@@@ with_tag PSKT_external] PSKI_external: psk_id:mls_bytes bytes -> psk_nonce:mls_bytes bytes -> pre_shared_key_id_nt bytes
  | [@@@ with_tag PSKT_resumption] PSKI_resumption: usage: resumption_psk_usage_nt -> psk_group_id:mls_bytes bytes -> psk_epoch:nat_lbytes 8 -> psk_nonce:mls_bytes bytes -> pre_shared_key_id_nt bytes

%splice [ps_pre_shared_key_id_nt] (gen_parser (`pre_shared_key_id_nt))

type psk_label_nt (bytes:Type0) {|bytes_like bytes|} = {
  id: pre_shared_key_id_nt bytes;
  index: nat_lbytes 2;
  count: nat_lbytes 2;
}

%splice [ps_psk_label_nt] (gen_parser (`psk_label_nt))

instance parseable_serializeable_psk_label_nt (bytes:Type0) {|bytes_like bytes|}: parseable_serializeable bytes (psk_label_nt bytes) = mk_parseable_serializeable ps_psk_label_nt

(*** Proposals ***)

type add_nt (bytes:Type0) {|bytes_like bytes|} = {
  key_package: key_package_nt bytes tkt;
}

%splice [ps_add_nt] (gen_parser (`add_nt))

type update_nt (bytes:Type0) {|bytes_like bytes|} = {
  leaf_node: leaf_node_nt bytes tkt;
}

%splice [ps_update_nt] (gen_parser (`update_nt))

type remove_nt (bytes:Type0) {|bytes_like bytes|} = {
  removed: nat_lbytes 4;
}

%splice [ps_remove_nt] (gen_parser (`remove_nt))

type pre_shared_key_nt (bytes:Type0) {|bytes_like bytes|} = {
  psk: pre_shared_key_id_nt bytes;
}

%splice [ps_pre_shared_key_nt] (gen_parser (`pre_shared_key_nt))

type reinit_nt (bytes:Type0) {|bytes_like bytes|} = {
  group_id: mls_bytes bytes;
  version: protocol_version_nt;
  cipher_suite: cipher_suite_nt;
  extensions: mls_list bytes ps_extension_nt
}

%splice [ps_reinit_nt] (gen_parser (`reinit_nt))

type external_init_nt (bytes:Type0) {|bytes_like bytes|} = {
  kem_output: mls_bytes bytes
}

%splice [ps_external_init_nt] (gen_parser (`external_init_nt))

type group_context_extensions_nt (bytes:Type0) {|bytes_like bytes|} = {
  extensions: mls_list bytes ps_extension_nt;
}

%splice [ps_group_context_extensions_nt] (gen_parser (`group_context_extensions_nt))

(*** Refs ***)

type key_package_ref_nt (bytes:Type0) {|bytes_like bytes|} = mls_bytes bytes
%splice [ps_key_package_ref_nt] (gen_parser (`key_package_ref_nt))

type proposal_ref_nt (bytes:Type0) {|bytes_like bytes|} = mls_bytes bytes
%splice [ps_proposal_ref_nt] (gen_parser (`proposal_ref_nt))

(*** Message framing ***)

type proposal_nt (bytes:Type0) {|bytes_like bytes|} =
  | [@@@ with_tag PT_add] P_add: add_nt bytes -> proposal_nt bytes
  | [@@@ with_tag PT_update] P_update: update_nt bytes -> proposal_nt bytes
  | [@@@ with_tag PT_remove] P_remove: remove_nt bytes -> proposal_nt bytes
  | [@@@ with_tag PT_psk] P_psk: pre_shared_key_nt bytes -> proposal_nt bytes
  | [@@@ with_tag PT_reinit] P_reinit: reinit_nt bytes -> proposal_nt bytes
  | [@@@ with_tag PT_external_init] P_external_init: external_init_nt bytes -> proposal_nt bytes
  | [@@@ with_tag PT_group_context_extensions] P_group_context_extensions: group_context_extensions_nt bytes -> proposal_nt bytes

%splice [ps_proposal_nt] (gen_parser (`proposal_nt))

type proposal_or_ref_nt (bytes:Type0) {|bytes_like bytes|} =
  | [@@@ with_num_tag 1 1] POR_proposal: proposal_nt bytes -> proposal_or_ref_nt bytes
  | [@@@ with_num_tag 1 2] POR_reference: proposal_ref_nt bytes -> proposal_or_ref_nt bytes

%splice [ps_proposal_or_ref_nt] (gen_parser (`proposal_or_ref_nt))

type commit_nt (bytes:Type0) {|bytes_like bytes|} = {
  proposals: mls_list bytes ps_proposal_or_ref_nt;
  [@@@ with_parser #bytes (ps_option ps_update_path_nt)]
  path: option (update_path_nt bytes);
}

%splice [ps_commit_nt] (gen_parser (`commit_nt))

type sender_type_nt =
  | [@@@ with_num_tag 1 1] ST_member: sender_type_nt
  | [@@@ with_num_tag 1 2] ST_external: sender_type_nt
  | [@@@ with_num_tag 1 3] ST_new_member_proposal: sender_type_nt
  | [@@@ with_num_tag 1 4] ST_new_member_commit: sender_type_nt

%splice [ps_sender_type_nt] (gen_parser (`sender_type_nt))

type sender_nt (bytes:Type0) {|bytes_like bytes|} =
  | [@@@ with_tag ST_member] S_member: leaf_index:nat_lbytes 4 -> sender_nt bytes
  | [@@@ with_tag ST_external] S_external: sender_index:nat_lbytes 4 -> sender_nt bytes
  | [@@@ with_tag ST_new_member_proposal] S_new_member_proposal: sender_nt bytes
  | [@@@ with_tag ST_new_member_commit] S_new_member_commit: sender_nt bytes

%splice [ps_sender_nt] (gen_parser (`sender_nt))

type wire_format_nt =
  | [@@@ with_num_tag 2 0] WF_reserved: wire_format_nt
  | [@@@ with_num_tag 2 1] WF_mls_public_message: wire_format_nt
  | [@@@ with_num_tag 2 2] WF_mls_private_message: wire_format_nt
  | [@@@ with_num_tag 2 3] WF_mls_welcome: wire_format_nt
  | [@@@ with_num_tag 2 4] WF_mls_group_info: wire_format_nt
  | [@@@ with_num_tag 2 5] WF_mls_key_package: wire_format_nt
  | [@@@ open_tag] WF_unknown: n:nat_lbytes 2{~(n <= 5)} -> wire_format_nt

%splice [ps_wire_format_nt] (gen_parser (`wire_format_nt))

type mac_nt (bytes:Type0) {|bytes_like bytes|} = mls_bytes bytes
%splice [ps_mac_nt] (gen_parser (`mac_nt))

type content_type_nt =
  | [@@@ with_num_tag 1 1] CT_application: content_type_nt
  | [@@@ with_num_tag 1 2] CT_proposal: content_type_nt
  | [@@@ with_num_tag 1 3] CT_commit: content_type_nt

%splice [ps_content_type_nt] (gen_parser (`content_type_nt))

val mls_untagged_content_nt: bytes:Type0 -> {|bytes_like bytes|} -> content_type_nt -> Type0
let mls_untagged_content_nt bytes #bl content_type =
  match content_type with
  | CT_application -> mls_bytes bytes
  | CT_proposal -> proposal_nt bytes
  | CT_commit -> commit_nt bytes

%splice [ps_mls_untagged_content_nt] (gen_parser (`mls_untagged_content_nt))

type mls_tagged_content_nt (bytes:Type0) {|bytes_like bytes|} = {
  content_type: content_type_nt;
  content: mls_untagged_content_nt bytes content_type;
}

%splice [ps_mls_tagged_content_nt] (gen_parser (`mls_tagged_content_nt))

type framed_content_nt (bytes:Type0) {|bytes_like bytes|} = {
  group_id: mls_bytes bytes;
  epoch: nat_lbytes 8;
  sender: sender_nt bytes;
  authenticated_data: mls_bytes bytes;
  content: mls_tagged_content_nt bytes;
}

%splice [ps_framed_content_nt] (gen_parser (`framed_content_nt))

let framed_content_tbs_group_context_nt (bytes:Type0) {|bytes_like bytes|} (s:sender_nt bytes) =
  match s with
  | S_member _
  | S_new_member_commit -> group_context_nt bytes
  | S_external _
  | S_new_member_proposal -> unit

%splice [ps_framed_content_tbs_group_context_nt] (gen_parser_prefix (`framed_content_tbs_group_context_nt))

type framed_content_tbs_nt (bytes:Type0) {|bytes_like bytes|} = {
  wire_format: wire_format_nt;
  content: framed_content_nt bytes;
  group_context: framed_content_tbs_group_context_nt bytes (content.sender);
}

%splice [ps_framed_content_tbs_nt] (gen_parser (`framed_content_tbs_nt))

instance parseable_serializeable_framed_content_tbs_nt (bytes:Type0) {|bytes_like bytes|}: parseable_serializeable bytes (framed_content_tbs_nt bytes) = mk_parseable_serializeable ps_framed_content_tbs_nt

val confirmation_tag_nt: bytes:Type0 -> {|bytes_like bytes|} -> content_type_nt -> Type0
let confirmation_tag_nt bytes #bl content =
  match content with
  | CT_commit -> mac_nt bytes
  | _ -> unit

%splice [ps_confirmation_tag_nt] (gen_parser_prefix (`confirmation_tag_nt))

type framed_content_auth_data_nt (bytes:Type0) {|bl:bytes_like bytes|} (content_type:content_type_nt) = {
  signature: mls_bytes bytes;
  confirmation_tag: confirmation_tag_nt bytes #bl content_type;
}

%splice [ps_framed_content_auth_data_nt] (gen_parser (`framed_content_auth_data_nt))

type authenticated_content_nt (bytes:Type0) {|bytes_like bytes|} = {
  wire_format: wire_format_nt;
  content: framed_content_nt bytes;
  auth: framed_content_auth_data_nt bytes content.content.content_type;
}

%splice [ps_authenticated_content_nt] (gen_parser (`authenticated_content_nt))

type authenticated_content_tbm_nt (bytes:Type0) {|bytes_like bytes|} = {
  content_tbs: framed_content_tbs_nt bytes;
  auth: framed_content_auth_data_nt bytes content_tbs.content.content.content_type;
}

%splice [ps_authenticated_content_tbm_nt] (gen_parser (`authenticated_content_tbm_nt))

instance parseable_serializeable_authenticated_content_tbm_nt (bytes:Type0) {|bytes_like bytes|}: parseable_serializeable bytes (authenticated_content_tbm_nt bytes) = mk_parseable_serializeable ps_authenticated_content_tbm_nt

let membership_tag_nt (bytes:Type0) {|bytes_like bytes|} (s:sender_nt bytes) =
  match s with
  | S_member _ -> mac_nt bytes
  | _ -> unit

%splice [ps_membership_tag_nt] (gen_parser_prefix (`membership_tag_nt))

type public_message_nt (bytes:Type0) {|bytes_like bytes|} = {
  content: framed_content_nt bytes;
  auth: framed_content_auth_data_nt bytes content.content.content_type;
  membership_tag: membership_tag_nt bytes content.sender;
}

%splice [ps_public_message_nt] (gen_parser (`public_message_nt))

type private_message_nt (bytes:Type0) {|bytes_like bytes|} = {
  group_id: mls_bytes bytes;
  epoch: nat_lbytes 8;
  content_type: content_type_nt;
  authenticated_data: mls_bytes bytes;
  encrypted_sender_data: mls_bytes bytes;
  ciphertext: mls_bytes bytes;
}

%splice [ps_private_message_nt] (gen_parser (`private_message_nt))

type private_content_tbe_data_nt (bytes:Type0) {|bytes_like bytes|} (content_type: content_type_nt) = {
  content: mls_untagged_content_nt bytes content_type;
  auth: framed_content_auth_data_nt bytes content_type;
}

%splice [ps_private_content_tbe_data_nt] (gen_parser (`private_content_tbe_data_nt))

let is_nat_zero (n:nat_lbytes 1) = n = 0
let zero_byte = refined (nat_lbytes 1) is_nat_zero
let ps_zero_byte (#bytes:Type0) {|bytes_like bytes|} = refine #bytes (ps_nat_lbytes 1) is_nat_zero

type private_content_tbe_nt (bytes:Type0) {|bytes_like bytes|} (content_type: content_type_nt) = {
  data: private_content_tbe_data_nt bytes content_type;
  padding: list zero_byte;
}

val pse_private_content_tbe_nt: #bytes:Type0 -> {|bytes_like bytes|} -> content_type:content_type_nt -> parser_serializer_whole bytes (private_content_tbe_nt bytes content_type)
let pse_private_content_tbe_nt #bytes #bl content_type =
  let iso = mk_isomorphism_between
    (fun (|data, padding|) -> {data; padding})
    (fun {data; padding} -> (|data, padding|))
  in
  isomorphism_whole
    (bind_whole (ps_private_content_tbe_data_nt content_type) (fun _ -> ps_whole_list ps_zero_byte))
    iso

instance parseable_serializeable_private_content_tbe_nt (bytes:Type0) {|bytes_like bytes|} (content_type:content_type_nt): parseable_serializeable bytes (private_content_tbe_nt bytes content_type) = mk_parseable_serializeable_from_whole (pse_private_content_tbe_nt content_type)

type private_content_aad_nt (bytes:Type0) {|bytes_like bytes|} = {
  group_id: mls_bytes bytes;
  epoch: nat_lbytes 8;
  content_type: content_type_nt;
  authenticated_data: mls_bytes bytes;
}

%splice [ps_private_content_aad_nt] (gen_parser (`private_content_aad_nt))

instance parseable_serializeable_private_content_aad_nt (bytes:Type0) {|bytes_like bytes|}: parseable_serializeable bytes (private_content_aad_nt bytes) = mk_parseable_serializeable ps_private_content_aad_nt

type sender_data_nt (bytes:Type0) {|bytes_like bytes|} = {
  leaf_index: nat_lbytes 4;
  generation: nat_lbytes 4;
  reuse_guard: lbytes bytes 4;
}

%splice [ps_sender_data_nt] (gen_parser (`sender_data_nt))

instance parseable_serializeable_sender_data_nt (bytes:Type0) {|bytes_like bytes|}: parseable_serializeable bytes (sender_data_nt bytes) = mk_parseable_serializeable ps_sender_data_nt

type sender_data_aad_nt (bytes:Type0) {|bytes_like bytes|} = {
  group_id: mls_bytes bytes;
  epoch: nat_lbytes 8;
  content_type: content_type_nt;
}

%splice [ps_sender_data_aad_nt] (gen_parser (`sender_data_aad_nt))

instance parseable_serializeable_sender_data_aad_nt (bytes:Type0) {|bytes_like bytes|}: parseable_serializeable bytes (sender_data_aad_nt bytes) = mk_parseable_serializeable ps_sender_data_aad_nt

type confirmed_transcript_hash_input_nt (bytes:Type0) {|bytes_like bytes|} = {
  wire_format: wire_format_nt;
  content: framed_content_nt bytes;
  signature: mls_bytes bytes;
}

%splice [ps_confirmed_transcript_hash_input_nt] (gen_parser (`confirmed_transcript_hash_input_nt))

instance parseable_serializeable_confirmed_transcript_hash_input_nt (bytes:Type0) {|bytes_like bytes|}: parseable_serializeable bytes (confirmed_transcript_hash_input_nt bytes) = mk_parseable_serializeable ps_confirmed_transcript_hash_input_nt

type interim_transcript_hash_input_nt (bytes:Type0) {|bytes_like bytes|} = {
  confirmation_tag: mac_nt bytes;
}

%splice [ps_interim_transcript_hash_input_nt] (gen_parser (`interim_transcript_hash_input_nt))

instance parseable_serializeable_interim_transcript_hash_input_nt (bytes:Type0) {|bytes_like bytes|}: parseable_serializeable bytes (interim_transcript_hash_input_nt bytes) = mk_parseable_serializeable ps_interim_transcript_hash_input_nt

type group_info_tbs_nt (bytes:Type0) {|bytes_like bytes|} = {
  group_context: group_context_nt bytes;
  extensions: mls_bytes bytes;
  confirmation_tag: mac_nt bytes;
  signer: nat_lbytes 4;
}

%splice [ps_group_info_tbs_nt] (gen_parser (`group_info_tbs_nt))

instance parseable_serializeable_group_info_tbs_nt (bytes:Type0) {|bytes_like bytes|}: parseable_serializeable bytes (group_info_tbs_nt bytes) = mk_parseable_serializeable ps_group_info_tbs_nt

type group_info_nt (bytes:Type0) {|bytes_like bytes|} = {
  tbs: group_info_tbs_nt bytes;
  signature: mls_bytes bytes;
}

%splice [ps_group_info_nt] (gen_parser (`group_info_nt))


instance parseable_serializeable_group_info_nt (bytes:Type0) {|bytes_like bytes|}: parseable_serializeable bytes (group_info_nt bytes) = mk_parseable_serializeable ps_group_info_nt

type path_secret_nt (bytes:Type0) {|bytes_like bytes|} = {
  path_secret: mls_bytes bytes;
}

%splice [ps_path_secret_nt] (gen_parser (`path_secret_nt))

type group_secrets_nt (bytes:Type0) {|bytes_like bytes|} = {
  joiner_secret: mls_bytes bytes;
  [@@@ with_parser #bytes (ps_option ps_path_secret_nt)]
  path_secret: option (path_secret_nt bytes);
  psks: mls_list bytes (ps_pre_shared_key_nt);
}

%splice [ps_group_secrets_nt] (gen_parser (`group_secrets_nt))

instance parseable_serializeable_group_secrets_nt (bytes:Type0) {|bytes_like bytes|}: parseable_serializeable bytes (group_secrets_nt bytes) = mk_parseable_serializeable ps_group_secrets_nt

type encrypted_group_secrets_nt (bytes:Type0) {|bytes_like bytes|} = {
  new_member: key_package_ref_nt bytes;
  encrypted_group_secrets: hpke_ciphertext_nt bytes;
}

%splice [ps_encrypted_group_secrets_nt] (gen_parser (`encrypted_group_secrets_nt))

type welcome_nt (bytes:Type0) {|bytes_like bytes|} = {
  cipher_suite: cipher_suite_nt;
  secrets: mls_list bytes ps_encrypted_group_secrets_nt;
  encrypted_group_info: mls_bytes bytes;
}

%splice [ps_welcome_nt] (gen_parser (`welcome_nt))

type mls_10_message_nt (bytes:Type0) {|bytes_like bytes|} =
  | [@@@ with_tag WF_mls_public_message] M_public_message: public_message_nt bytes -> mls_10_message_nt bytes
  | [@@@ with_tag WF_mls_private_message] M_private_message: private_message_nt bytes -> mls_10_message_nt bytes
  | [@@@ with_tag WF_mls_welcome] M_welcome: welcome_nt bytes -> mls_10_message_nt bytes
  | [@@@ with_tag WF_mls_group_info] M_group_info: group_info_nt bytes -> mls_10_message_nt bytes
  | [@@@ with_tag WF_mls_key_package] M_key_package: key_package_nt bytes tkt -> mls_10_message_nt bytes

%splice [ps_mls_10_message_nt] (gen_parser (`mls_10_message_nt))

type mls_message_nt (bytes:Type0) {|bytes_like bytes|} =
  | [@@@ with_tag PV_mls10] M_mls10: mls_10_message_nt bytes -> mls_message_nt bytes

%splice [ps_mls_message_nt] (gen_parser (`mls_message_nt))

instance parseable_serializeable_mls_message_nt (bytes:Type0) {|bytes_like bytes|}: parseable_serializeable bytes (mls_message_nt bytes) = mk_parseable_serializeable ps_mls_message_nt
