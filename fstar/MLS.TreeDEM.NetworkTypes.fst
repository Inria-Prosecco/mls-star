module MLS.TreeDEM.NetworkTypes

open Comparse
open MLS.NetworkTypes
open MLS.TreeSync.NetworkTypes

(*** PSKs ***)

type psk_type_nt =
  | PSKT_external: [@@@ with_num_tag 1 1] unit -> psk_type_nt
  | PSKT_resumption: [@@@ with_num_tag 1 2] unit -> psk_type_nt

%splice [ps_psk_type_nt] (gen_parser (`psk_type_nt))

type resumption_psk_usage_nt =
  | RPSKU_application: [@@@ with_num_tag 1 1] unit -> resumption_psk_usage_nt
  | RPSKU_reinit: [@@@ with_num_tag 1 2] unit -> resumption_psk_usage_nt
  | RPSKU_branch: [@@@ with_num_tag 1 3] unit -> resumption_psk_usage_nt

%splice [ps_resumption_psk_usage_nt] (gen_parser (`resumption_psk_usage_nt))

noeq type pre_shared_key_id_nt (bytes:Type0) {|bytes_like bytes|} =
  | PSKI_external: [@@@ with_tag (PSKT_external ())] psk_id:mls_bytes bytes -> psk_nonce:mls_bytes bytes -> pre_shared_key_id_nt bytes
  | PSKI_resumption: [@@@ with_tag (PSKT_resumption ())] usage: resumption_psk_usage_nt -> psk_group_id:mls_bytes bytes -> psk_epoch:nat_lbytes 8 -> psk_nonce:mls_bytes bytes -> pre_shared_key_id_nt bytes

%splice [ps_pre_shared_key_id_nt] (gen_parser (`pre_shared_key_id_nt))

noeq type psk_label_nt (bytes:Type0) {|bytes_like bytes|} = {
  id: pre_shared_key_id_nt bytes;
  index: nat_lbytes 2;
  count: nat_lbytes 2;
}

%splice [ps_psk_label_nt] (gen_parser (`psk_label_nt))

instance parseable_serializeable_psk_label_nt (bytes:Type0) {|bytes_like bytes|}: parseable_serializeable bytes (psk_label_nt bytes) = mk_parseable_serializeable ps_psk_label_nt

(*** Proposals ***)

noeq type add_nt (bytes:Type0) {|bytes_like bytes|} = {
  key_package: key_package_nt bytes;
}

%splice [ps_add_nt] (gen_parser (`add_nt))

noeq type update_nt (bytes:Type0) {|bytes_like bytes|} = {
  leaf_node: leaf_node_nt bytes;
}

%splice [ps_update_nt] (gen_parser (`update_nt))

noeq type remove_nt (bytes:Type0) {|bytes_like bytes|} = {
  removed: nat_lbytes 4;
}

%splice [ps_remove_nt] (gen_parser (`remove_nt))

noeq type pre_shared_key_nt (bytes:Type0) {|bytes_like bytes|} = {
  psk: pre_shared_key_id_nt bytes;
}

%splice [ps_pre_shared_key_nt] (gen_parser (`pre_shared_key_nt))

noeq type reinit_nt (bytes:Type0) {|bytes_like bytes|} = {
  group_id: mls_bytes bytes;
  version: protocol_version_nt;
  cipher_suite: cipher_suite_nt;
  extensions: mls_seq bytes ps_extension_nt
}

%splice [ps_reinit_nt] (gen_parser (`reinit_nt))

noeq type external_init_nt (bytes:Type0) {|bytes_like bytes|} = {
  kem_output: mls_bytes bytes
}

%splice [ps_external_init_nt] (gen_parser (`external_init_nt))

noeq type group_context_extensions_nt (bytes:Type0) {|bytes_like bytes|} = {
  extensions: mls_seq bytes ps_extension_nt;
}

%splice [ps_group_context_extensions_nt] (gen_parser (`group_context_extensions_nt))

//TODO: move part of these in treekem
noeq type hpke_ciphertext_nt (bytes:Type0) {|bytes_like bytes|} = {
  kem_output: mls_bytes bytes;
  ciphertext: mls_bytes bytes;
}

%splice [ps_hpke_ciphertext_nt] (gen_parser (`hpke_ciphertext_nt))

noeq type update_path_node_nt (bytes:Type0) {|bytes_like bytes|} = {
  encryption_key: hpke_public_key_nt bytes;
  encrypted_path_secret: mls_seq bytes ps_hpke_ciphertext_nt;
}

%splice [ps_update_path_node_nt] (gen_parser (`update_path_node_nt))

noeq type update_path_nt (bytes:Type0) {|bytes_like bytes|} = {
  leaf_node: leaf_node_nt bytes;
  nodes: mls_seq bytes ps_update_path_node_nt;
}

%splice [ps_update_path_nt] (gen_parser (`update_path_nt))

(*** Refs ***)

type key_package_ref_nt (bytes:Type0) {|bytes_like bytes|} = mls_bytes bytes
val ps_key_package_ref_nt: #bytes:Type0 -> {|bytes_like bytes|} -> parser_serializer bytes (key_package_ref_nt bytes)
let ps_key_package_ref_nt #bytes #bl = ps_mls_bytes

type proposal_ref_nt (bytes:Type0) {|bytes_like bytes|} = mls_bytes bytes
val ps_proposal_ref_nt: #bytes:Type0 -> {|bytes_like bytes|} -> parser_serializer bytes (proposal_ref_nt bytes)
let ps_proposal_ref_nt #bytes #bl = ps_mls_bytes

(*** Message framing ***)

noeq type proposal_nt (bytes:Type0) {|bytes_like bytes|} =
  | P_add: [@@@ with_tag (PT_add ())] add_nt bytes -> proposal_nt bytes
  | P_update: [@@@ with_tag (PT_update ())] update_nt bytes -> proposal_nt bytes
  | P_remove: [@@@ with_tag (PT_remove ())] remove_nt bytes -> proposal_nt bytes
  | P_psk: [@@@ with_tag (PT_psk ())] pre_shared_key_nt bytes -> proposal_nt bytes
  | P_reinit: [@@@ with_tag (PT_reinit ())] reinit_nt bytes -> proposal_nt bytes
  | P_external_init: [@@@ with_tag (PT_external_init ())] external_init_nt bytes -> proposal_nt bytes
  | P_group_context_extensions: [@@@ with_tag (PT_group_context_extensions ())] group_context_extensions_nt bytes -> proposal_nt bytes

%splice [ps_proposal_nt] (gen_parser (`proposal_nt))

noeq type proposal_or_ref_nt (bytes:Type0) {|bytes_like bytes|} =
  | POR_proposal: [@@@ with_num_tag 1 1] proposal_nt bytes -> proposal_or_ref_nt bytes
  | POR_reference: [@@@ with_num_tag 1 2] proposal_ref_nt bytes -> proposal_or_ref_nt bytes

%splice [ps_proposal_or_ref_nt] (gen_parser (`proposal_or_ref_nt))

noeq type commit_nt (bytes:Type0) {|bytes_like bytes|} = {
  proposals: mls_seq bytes ps_proposal_or_ref_nt;
  [@@@ with_parser #bytes (ps_option ps_update_path_nt)]
  path: option (update_path_nt bytes);
}

%splice [ps_commit_nt] (gen_parser (`commit_nt))

type sender_type_nt =
  | ST_member: [@@@ with_num_tag 1 1] unit -> sender_type_nt
  | ST_external: [@@@ with_num_tag 1 2] unit -> sender_type_nt
  | ST_new_member_proposal: [@@@ with_num_tag 1 3] unit -> sender_type_nt
  | ST_new_member_commit: [@@@ with_num_tag 1 4] unit -> sender_type_nt

%splice [ps_sender_type_nt] (gen_parser (`sender_type_nt))

noeq type sender_nt (bytes:Type0) {|bytes_like bytes|} =
  | S_member: [@@@ with_tag (ST_member ())] leaf_index:nat_lbytes 4 -> sender_nt bytes
  | S_external: [@@@ with_tag (ST_external ())] sender_index:nat_lbytes 4 -> sender_nt bytes
  | S_new_member_proposal: [@@@ with_tag (ST_new_member_proposal ())] unit -> sender_nt bytes
  | S_new_member_commit: [@@@ with_tag (ST_new_member_commit ())] unit -> sender_nt bytes

%splice [ps_sender_nt] (gen_parser (`sender_nt))

type wire_format_nt =
  | WF_mls_plaintext: [@@@ with_num_tag 1 1] unit -> wire_format_nt
  | WF_mls_ciphertext: [@@@ with_num_tag 1 2] unit -> wire_format_nt
  | WF_mls_welcome: [@@@ with_num_tag 1 3] unit -> wire_format_nt
  | WF_mls_group_info: [@@@ with_num_tag 1 4] unit -> wire_format_nt
  | WF_mls_key_package: [@@@ with_num_tag 1 5] unit -> wire_format_nt

%splice [ps_wire_format_nt] (gen_parser (`wire_format_nt))

type mac_nt (bytes:Type0) {|bytes_like bytes|} = mls_bytes bytes
val ps_mac_nt: #bytes:Type0 -> {|bytes_like bytes|} -> parser_serializer bytes (mac_nt bytes)
let ps_mac_nt #bytes #bl = ps_mls_bytes

type content_type_nt =
  | CT_application: [@@@ with_num_tag 1 1] unit -> content_type_nt
  | CT_proposal: [@@@ with_num_tag 1 2] unit -> content_type_nt
  | CT_commit: [@@@ with_num_tag 1 3] unit -> content_type_nt

%splice [ps_content_type_nt] (gen_parser (`content_type_nt))

val mls_untagged_content_nt: bytes:Type0 -> {|bytes_like bytes|} -> content_type_nt -> Type0
let mls_untagged_content_nt bytes #bl content_type =
  match content_type with
  | CT_application () -> mls_bytes bytes
  | CT_proposal () -> proposal_nt bytes
  | CT_commit () -> commit_nt bytes

val ps_mls_untagged_content_nt: #bytes:Type0 -> {|bytes_like bytes|} -> content_type:content_type_nt -> parser_serializer bytes (mls_untagged_content_nt bytes content_type)
let ps_mls_untagged_content_nt #bytes #bl content_type =
  match content_type with
  | CT_application () -> ps_mls_bytes
  | CT_proposal () -> ps_proposal_nt
  | CT_commit () -> ps_commit_nt

noeq type mls_tagged_content_nt (bytes:Type0) {|bytes_like bytes|} = {
  content_type: content_type_nt;
  content: mls_untagged_content_nt bytes content_type;
}

%splice [ps_mls_tagged_content_nt] (gen_parser (`mls_tagged_content_nt))

noeq type mls_content_nt (bytes:Type0) {|bytes_like bytes|} = {
  group_id: mls_bytes bytes;
  epoch: nat_lbytes 8;
  sender: sender_nt bytes;
  authenticated_data: mls_bytes bytes;
  content: mls_tagged_content_nt bytes;
}

%splice [ps_mls_content_nt] (gen_parser (`mls_content_nt))

let mls_content_tbs_group_context_nt (bytes:Type0) {|bytes_like bytes|} (s:sender_nt bytes) =
  match s with
  | S_member _
  | S_new_member_commit _ -> group_context_nt bytes
  | S_external _
  | S_new_member_proposal _ -> unit

val ps_mls_content_tbs_group_context_nt: #bytes:Type0 -> {|bytes_like bytes|} -> s:sender_nt bytes -> parser_serializer_unit bytes (mls_content_tbs_group_context_nt bytes s)
let ps_mls_content_tbs_group_context_nt #bytes #bl s =
  match s with
  | S_member _
  | S_new_member_commit _ -> ps_group_context_nt
  | S_external _
  | S_new_member_proposal _ -> ps_unit

noeq type mls_content_tbs_nt (bytes:Type0) {|bytes_like bytes|} = {
  wire_format: wire_format_nt;
  content: mls_content_nt bytes;
  group_context: mls_content_tbs_group_context_nt bytes (content.sender);
}

%splice [ps_mls_content_tbs_nt] (gen_parser (`mls_content_tbs_nt))

instance parseable_serializeable_mls_content_tbs_nt (bytes:Type0) {|bytes_like bytes|}: parseable_serializeable bytes (mls_content_tbs_nt bytes) = mk_parseable_serializeable ps_mls_content_tbs_nt

val confirmation_tag_nt: bytes:Type0 -> {|bytes_like bytes|} -> content_type_nt -> Type0
let confirmation_tag_nt bytes #bl content =
  match content with
  | CT_commit () -> mac_nt bytes
  | _ -> unit

val ps_confirmation_tag_nt: #bytes:Type0 -> {|bytes_like bytes|} -> content_type:content_type_nt -> parser_serializer_unit bytes (confirmation_tag_nt bytes content_type)
let ps_confirmation_tag_nt #bytes #bl content_type =
  match content_type with
  | CT_commit () -> ps_mac_nt
  | _ -> ps_unit

noeq type mls_content_auth_data_nt (bytes:Type0) {|bl:bytes_like bytes|} (content_type:content_type_nt) = {
  signature: mls_bytes bytes;
  confirmation_tag: confirmation_tag_nt bytes #bl content_type;
}

%splice [ps_mls_content_auth_data_nt] (gen_parser (`mls_content_auth_data_nt))

noeq type mls_authenticated_content_nt (bytes:Type0) {|bytes_like bytes|} = {
  wire_format: wire_format_nt;
  content: mls_content_nt bytes;
  auth: mls_content_auth_data_nt bytes content.content.content_type;
}

%splice [ps_mls_authenticated_content_nt] (gen_parser (`mls_authenticated_content_nt))

noeq type mls_content_tbm_nt (bytes:Type0) {|bytes_like bytes|} = {
  content_tbs: mls_content_tbs_nt bytes;
  auth: mls_content_auth_data_nt bytes content_tbs.content.content.content_type;
}

%splice [ps_mls_content_tbm_nt] (gen_parser (`mls_content_tbm_nt))

instance parseable_serializeable_mls_content_tbm_nt (bytes:Type0) {|bytes_like bytes|}: parseable_serializeable bytes (mls_content_tbm_nt bytes) = mk_parseable_serializeable ps_mls_content_tbm_nt

let membership_tag_nt (bytes:Type0) {|bytes_like bytes|} (s:sender_nt bytes) =
  match s with
  | S_member _ -> mac_nt bytes
  | _ -> unit

val ps_membership_tag_nt: #bytes:Type0 -> {|bytes_like bytes|} -> s:sender_nt bytes -> parser_serializer_unit bytes (membership_tag_nt bytes s)
let ps_membership_tag_nt #bytes #bl s =
  match s with
  | S_member _ -> ps_mac_nt
  | _ -> ps_unit

noeq type mls_plaintext_nt (bytes:Type0) {|bytes_like bytes|} = {
  content: mls_content_nt bytes;
  auth: mls_content_auth_data_nt bytes content.content.content_type;
  membership_tag: membership_tag_nt bytes content.sender;
}

%splice [ps_mls_plaintext_nt] (gen_parser (`mls_plaintext_nt))

noeq type mls_ciphertext_nt (bytes:Type0) {|bytes_like bytes|} = {
  group_id: mls_bytes bytes;
  epoch: nat_lbytes 8;
  content_type: content_type_nt;
  authenticated_data: mls_bytes bytes;
  encrypted_sender_data: mls_bytes bytes;
  ciphertext: mls_bytes bytes;
}

%splice [ps_mls_ciphertext_nt] (gen_parser (`mls_ciphertext_nt))

noeq type mls_ciphertext_content_data_nt (bytes:Type0) {|bytes_like bytes|} (content_type: content_type_nt) = {
  content: mls_untagged_content_nt bytes content_type;
  auth: mls_content_auth_data_nt bytes content_type;
}

%splice [ps_mls_ciphertext_content_data_nt] (gen_parser (`mls_ciphertext_content_data_nt))

let is_nat_zero (n:nat_lbytes 1) = n = 0
let zero_byte = refined (nat_lbytes 1) is_nat_zero
let ps_zero_byte (#bytes:Type0) {|bytes_like bytes|} = refine #bytes (ps_nat_lbytes 1) is_nat_zero

noeq type mls_ciphertext_content_nt (bytes:Type0) {|bytes_like bytes|} (content_type: content_type_nt) = {
  data: mls_ciphertext_content_data_nt bytes content_type;
  padding: list zero_byte;
}

val pse_mls_ciphertext_content_nt: #bytes:Type0 -> {|bytes_like bytes|} -> content_type:content_type_nt -> parser_serializer_exact bytes (mls_ciphertext_content_nt bytes content_type)
let pse_mls_ciphertext_content_nt #bytes #bl content_type =
  let iso = mk_isomorphism_between
    (fun (|data, padding|) -> {data; padding})
    (fun {data; padding} -> (|data, padding|))
  in
  isomorphism_exact
    (bind_exact (ps_mls_ciphertext_content_data_nt content_type) (fun _ -> pse_list ps_zero_byte))
    iso

instance parseable_serializeable_mls_ciphertext_content_nt (bytes:Type0) {|bytes_like bytes|} (content_type:content_type_nt): parseable_serializeable bytes (mls_ciphertext_content_nt bytes content_type) = mk_parseable_serializeable_from_exact (pse_mls_ciphertext_content_nt content_type)

noeq type mls_ciphertext_content_aad_nt (bytes:Type0) {|bytes_like bytes|} = {
  group_id: mls_bytes bytes;
  epoch: nat_lbytes 8;
  content_type: content_type_nt;
  authenticated_data: mls_bytes bytes;
}

%splice [ps_mls_ciphertext_content_aad_nt] (gen_parser (`mls_ciphertext_content_aad_nt))

instance parseable_serializeable_mls_ciphertext_content_aad_nt (bytes:Type0) {|bytes_like bytes|}: parseable_serializeable bytes (mls_ciphertext_content_aad_nt bytes) = mk_parseable_serializeable ps_mls_ciphertext_content_aad_nt

noeq type mls_sender_data_nt (bytes:Type0) {|bytes_like bytes|} = {
  leaf_index: nat_lbytes 4;
  generation: nat_lbytes 4;
  reuse_guard: lbytes bytes 4;
}

%splice [ps_mls_sender_data_nt] (gen_parser (`mls_sender_data_nt))

instance parseable_serializeable_mls_sender_data_nt (bytes:Type0) {|bytes_like bytes|}: parseable_serializeable bytes (mls_sender_data_nt bytes) = mk_parseable_serializeable ps_mls_sender_data_nt

noeq type mls_sender_data_aad_nt (bytes:Type0) {|bytes_like bytes|} = {
  group_id: mls_bytes bytes;
  epoch: nat_lbytes 8;
  content_type: content_type_nt;
}

%splice [ps_mls_sender_data_aad_nt] (gen_parser (`mls_sender_data_aad_nt))

instance parseable_serializeable_mls_sender_data_aad_nt (bytes:Type0) {|bytes_like bytes|}: parseable_serializeable bytes (mls_sender_data_aad_nt bytes) = mk_parseable_serializeable ps_mls_sender_data_aad_nt

noeq type confirmed_transcript_hash_input_nt (bytes:Type0) {|bytes_like bytes|} = {
  wire_format: wire_format_nt;
  content: mls_content_nt bytes;
  signature: mls_bytes bytes;
}

%splice [ps_confirmed_transcript_hash_input_nt] (gen_parser (`confirmed_transcript_hash_input_nt))

instance parseable_serializeable_confirmed_transcript_hash_input_nt (bytes:Type0) {|bytes_like bytes|}: parseable_serializeable bytes (confirmed_transcript_hash_input_nt bytes) = mk_parseable_serializeable ps_confirmed_transcript_hash_input_nt

noeq type interim_transcript_hash_input_nt (bytes:Type0) {|bytes_like bytes|} = {
  confirmation_tag: mac_nt bytes;
}

%splice [ps_interim_transcript_hash_input_nt] (gen_parser (`interim_transcript_hash_input_nt))

instance parseable_serializeable_interim_transcript_hash_input_nt (bytes:Type0) {|bytes_like bytes|}: parseable_serializeable bytes (interim_transcript_hash_input_nt bytes) = mk_parseable_serializeable ps_interim_transcript_hash_input_nt

noeq type group_info_tbs_nt (bytes:Type0) {|bytes_like bytes|} = {
  group_context: group_context_nt bytes;
  extensions: mls_bytes bytes;
  confirmation_tag: mac_nt bytes;
  signer: nat_lbytes 4;
}

%splice [ps_group_info_tbs_nt] (gen_parser (`group_info_tbs_nt))

instance parseable_serializeable_group_info_tbs_nt (bytes:Type0) {|bytes_like bytes|}: parseable_serializeable bytes (group_info_tbs_nt bytes) = mk_parseable_serializeable ps_group_info_tbs_nt

noeq type group_info_nt (bytes:Type0) {|bytes_like bytes|} = {
  tbs: group_info_tbs_nt bytes;
  signature: mls_bytes bytes;
}

%splice [ps_group_info_nt] (gen_parser (`group_info_nt))


instance parseable_serializeable_group_info_nt (bytes:Type0) {|bytes_like bytes|}: parseable_serializeable bytes (group_info_nt bytes) = mk_parseable_serializeable ps_group_info_nt

noeq type path_secret_nt (bytes:Type0) {|bytes_like bytes|} = {
  path_secret: mls_bytes bytes;
}

%splice [ps_path_secret_nt] (gen_parser (`path_secret_nt))

noeq type group_secrets_nt (bytes:Type0) {|bytes_like bytes|} = {
  joiner_secret: mls_bytes bytes;
  [@@@ with_parser #bytes (ps_option ps_path_secret_nt)]
  path_secret: option (path_secret_nt bytes);
  psks: mls_seq bytes (ps_pre_shared_key_nt);
}

%splice [ps_group_secrets_nt] (gen_parser (`group_secrets_nt))

instance parseable_serializeable_group_secrets_nt (bytes:Type0) {|bytes_like bytes|}: parseable_serializeable bytes (group_secrets_nt bytes) = mk_parseable_serializeable ps_group_secrets_nt

noeq type encrypted_group_secrets_nt (bytes:Type0) {|bytes_like bytes|} = {
  new_member: key_package_ref_nt bytes;
  encrypted_group_secrets: hpke_ciphertext_nt bytes;
}

%splice [ps_encrypted_group_secrets_nt] (gen_parser (`encrypted_group_secrets_nt))

noeq type welcome_nt (bytes:Type0) {|bytes_like bytes|} = {
  cipher_suite: cipher_suite_nt;
  secrets: mls_seq bytes ps_encrypted_group_secrets_nt;
  encrypted_group_info: mls_bytes bytes;
}

%splice [ps_welcome_nt] (gen_parser (`welcome_nt))

noeq type mls_10_message_nt (bytes:Type0) {|bytes_like bytes|} =
  | M_plaintext: [@@@ with_tag (WF_mls_plaintext ())] mls_plaintext_nt bytes -> mls_10_message_nt bytes
  | M_ciphertext: [@@@ with_tag (WF_mls_ciphertext ())] mls_ciphertext_nt bytes -> mls_10_message_nt bytes
  | M_welcome: [@@@ with_tag (WF_mls_welcome ())] welcome_nt bytes -> mls_10_message_nt bytes
  | M_group_info: [@@@ with_tag (WF_mls_group_info ())] group_info_nt bytes -> mls_10_message_nt bytes
  | M_key_package: [@@@ with_tag (WF_mls_key_package ())] key_package_nt bytes -> mls_10_message_nt bytes

%splice [ps_mls_10_message_nt] (gen_parser (`mls_10_message_nt))

noeq type mls_message_nt (bytes:Type0) {|bytes_like bytes|} =
  | M_mls10: [@@@ with_tag (PV_mls10 ())] mls_10_message_nt bytes -> mls_message_nt bytes

%splice [ps_mls_message_nt] (gen_parser (`mls_message_nt))
