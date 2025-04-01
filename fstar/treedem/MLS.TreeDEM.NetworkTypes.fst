module MLS.TreeDEM.NetworkTypes

open Comparse
open MLS.NetworkTypes
open MLS.TreeSync.NetworkTypes
open MLS.TreeKEM.NetworkTypes
open MLS.Bootstrap.NetworkTypes

(*** Proposals ***)

/// struct {
///     KeyPackage key_package;
/// } Add;

type add_nt (bytes:Type0) {|bytes_like bytes|} = {
  key_package: key_package_nt bytes tkt;
}

%splice [ps_add_nt] (gen_parser (`add_nt))
%splice [ps_add_nt_is_well_formed] (gen_is_well_formed_lemma (`add_nt))

/// struct {
///     LeafNode leaf_node;
/// } Update;

type update_nt (bytes:Type0) {|bytes_like bytes|} = {
  leaf_node: leaf_node_nt bytes tkt;
}

%splice [ps_update_nt] (gen_parser (`update_nt))
%splice [ps_update_nt_is_well_formed] (gen_is_well_formed_lemma (`update_nt))

/// struct {
///     uint32 removed;
/// } Remove;

type remove_nt (bytes:Type0) {|bytes_like bytes|} = {
  removed: nat_lbytes 4;
}

%splice [ps_remove_nt] (gen_parser (`remove_nt))
%splice [ps_remove_nt_is_well_formed] (gen_is_well_formed_lemma (`remove_nt))

/// struct {
///     PreSharedKeyID psk;
/// } PreSharedKey;

type pre_shared_key_nt (bytes:Type0) {|bytes_like bytes|} = {
  psk: pre_shared_key_id_nt bytes;
}

%splice [ps_pre_shared_key_nt] (gen_parser (`pre_shared_key_nt))
%splice [ps_pre_shared_key_nt_is_well_formed] (gen_is_well_formed_lemma (`pre_shared_key_nt))

/// struct {
///     opaque group_id<V>;
///     ProtocolVersion version;
///     CipherSuite cipher_suite;
///     Extension extensions<V>;
/// } ReInit;

type reinit_nt (bytes:Type0) {|bytes_like bytes|} = {
  group_id: mls_bytes bytes;
  version: protocol_version_nt;
  cipher_suite: cipher_suite_nt;
  extensions: mls_list bytes ps_extension_nt
}

%splice [ps_reinit_nt] (gen_parser (`reinit_nt))
%splice [ps_reinit_nt_is_well_formed] (gen_is_well_formed_lemma (`reinit_nt))

/// struct {
///   opaque kem_output<V>;
/// } ExternalInit;

type external_init_nt (bytes:Type0) {|bytes_like bytes|} = {
  kem_output: mls_bytes bytes
}

%splice [ps_external_init_nt] (gen_parser (`external_init_nt))
%splice [ps_external_init_nt_is_well_formed] (gen_is_well_formed_lemma (`external_init_nt))

/// struct {
///   Extension extensions<V>;
/// } GroupContextExtensions;

type group_context_extensions_nt (bytes:Type0) {|bytes_like bytes|} = {
  extensions: mls_list bytes ps_extension_nt;
}

%splice [ps_group_context_extensions_nt] (gen_parser (`group_context_extensions_nt))
%splice [ps_group_context_extensions_nt_is_well_formed] (gen_is_well_formed_lemma (`group_context_extensions_nt))

(*** Refs ***)

/// opaque HashReference<V>;
///
/// HashReference ProposalRef;

type proposal_ref_nt (bytes:Type0) {|bytes_like bytes|} = mls_bytes bytes
%splice [ps_proposal_ref_nt] (gen_parser (`proposal_ref_nt))

(*** Message framing ***)

/// // See IANA registry for registered values
/// uint16 ProposalType;

type proposal_nt (bytes:Type0) {|bytes_like bytes|} =
  | [@@@ with_tag PT_add] P_add: add_nt bytes -> proposal_nt bytes
  | [@@@ with_tag PT_update] P_update: update_nt bytes -> proposal_nt bytes
  | [@@@ with_tag PT_remove] P_remove: remove_nt bytes -> proposal_nt bytes
  | [@@@ with_tag PT_psk] P_psk: pre_shared_key_nt bytes -> proposal_nt bytes
  | [@@@ with_tag PT_reinit] P_reinit: reinit_nt bytes -> proposal_nt bytes
  | [@@@ with_tag PT_external_init] P_external_init: external_init_nt bytes -> proposal_nt bytes
  | [@@@ with_tag PT_group_context_extensions] P_group_context_extensions: group_context_extensions_nt bytes -> proposal_nt bytes

%splice [ps_proposal_nt] (gen_parser (`proposal_nt))
%splice [ps_proposal_nt_is_well_formed] (gen_is_well_formed_lemma (`proposal_nt))

instance parseable_serializeable_proposal_nt (bytes:Type0) {|bytes_like bytes|}: parseable_serializeable bytes (proposal_nt bytes) = mk_parseable_serializeable ps_proposal_nt

/// enum {
///   reserved(0),
///   proposal(1),
///   reference(2),
///   (255)
/// } ProposalOrRefType;
///
/// struct {
///   ProposalOrRefType type;
///   select (ProposalOrRef.type) {
///     case proposal:  Proposal proposal;
///     case reference: ProposalRef reference;
///   };
/// } ProposalOrRef;

type proposal_or_ref_nt (bytes:Type0) {|bytes_like bytes|} =
  | [@@@ with_num_tag 1 1] POR_proposal: proposal_nt bytes -> proposal_or_ref_nt bytes
  | [@@@ with_num_tag 1 2] POR_reference: proposal_ref_nt bytes -> proposal_or_ref_nt bytes

%splice [ps_proposal_or_ref_nt] (gen_parser (`proposal_or_ref_nt))
%splice [ps_proposal_or_ref_nt_is_well_formed] (gen_is_well_formed_lemma (`proposal_or_ref_nt))

/// struct {
///     ProposalOrRef proposals<V>;
///     optional<UpdatePath> path;
/// } Commit;

type commit_nt (bytes:Type0) {|bytes_like bytes|} = {
  proposals: mls_list bytes ps_proposal_or_ref_nt;
  [@@@ with_parser #bytes (ps_option ps_update_path_nt)]
  path: option (update_path_nt bytes);
}

%splice [ps_commit_nt] (gen_parser (`commit_nt))
%splice [ps_commit_nt_is_well_formed] (gen_is_well_formed_lemma (`commit_nt))

/// enum {
///     reserved(0),
///     member(1),
///     external(2),
///     new_member_proposal(3),
///     new_member_commit(4),
///     (255)
/// } SenderType;

type sender_type_nt =
  | [@@@ with_num_tag 1 1] ST_member: sender_type_nt
  | [@@@ with_num_tag 1 2] ST_external: sender_type_nt
  | [@@@ with_num_tag 1 3] ST_new_member_proposal: sender_type_nt
  | [@@@ with_num_tag 1 4] ST_new_member_commit: sender_type_nt

%splice [ps_sender_type_nt] (gen_parser (`sender_type_nt))
%splice [ps_sender_type_nt_is_well_formed] (gen_is_well_formed_lemma (`sender_type_nt))

/// struct {
///     SenderType sender_type;
///     select (Sender.sender_type) {
///         case member:
///             uint32 leaf_index;
///         case external:
///             uint32 sender_index;
///         case new_member_commit:
///         case new_member_proposal:
///             struct{};
///     };
/// } Sender;

type sender_nt (bytes:Type0) {|bytes_like bytes|} =
  | [@@@ with_tag ST_member] S_member: leaf_index:nat_lbytes 4 -> sender_nt bytes
  | [@@@ with_tag ST_external] S_external: sender_index:nat_lbytes 4 -> sender_nt bytes
  | [@@@ with_tag ST_new_member_proposal] S_new_member_proposal: sender_nt bytes
  | [@@@ with_tag ST_new_member_commit] S_new_member_commit: sender_nt bytes

%splice [ps_sender_nt] (gen_parser (`sender_nt))
%splice [ps_sender_nt_is_well_formed] (gen_is_well_formed_lemma (`sender_nt))

/// // See IANA registry for registered values
/// uint16 WireFormat;

type wire_format_nt =
  | [@@@ with_num_tag 2 0] WF_reserved: wire_format_nt
  | [@@@ with_num_tag 2 1] WF_mls_public_message: wire_format_nt
  | [@@@ with_num_tag 2 2] WF_mls_private_message: wire_format_nt
  | [@@@ with_num_tag 2 3] WF_mls_welcome: wire_format_nt
  | [@@@ with_num_tag 2 4] WF_mls_group_info: wire_format_nt
  | [@@@ with_num_tag 2 5] WF_mls_key_package: wire_format_nt
  | [@@@ open_tag] WF_unknown: n:nat_lbytes 2{~(n <= 5)} -> wire_format_nt

%splice [ps_wire_format_nt] (gen_parser (`wire_format_nt))

/// enum {
///     reserved(0),
///     application(1),
///     proposal(2),
///     commit(3),
///     (255)
/// } ContentType;

type content_type_nt =
  | [@@@ with_num_tag 1 1] CT_application: content_type_nt
  | [@@@ with_num_tag 1 2] CT_proposal: content_type_nt
  | [@@@ with_num_tag 1 3] CT_commit: content_type_nt

%splice [ps_content_type_nt] (gen_parser (`content_type_nt))
%splice [ps_content_type_nt_is_well_formed] (gen_is_well_formed_lemma (`content_type_nt))

/// struct {
///     opaque group_id<V>;
///     uint64 epoch;
///     Sender sender;
///     opaque authenticated_data<V>;
///
///     ContentType content_type;
///     select (FramedContent.content_type) {
///         case application:
///           opaque application_data<V>;
///         case proposal:
///           Proposal proposal;
///         case commit:
///           Commit commit;
///     };
/// } FramedContent;

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
%splice [ps_mls_tagged_content_nt_is_well_formed] (gen_is_well_formed_lemma (`mls_tagged_content_nt))

type framed_content_nt (bytes:Type0) {|bytes_like bytes|} = {
  group_id: mls_bytes bytes;
  epoch: nat_lbytes 8;
  sender: sender_nt bytes;
  authenticated_data: mls_bytes bytes;
  content: mls_tagged_content_nt bytes;
}

%splice [ps_framed_content_nt] (gen_parser (`framed_content_nt))
%splice [ps_framed_content_nt_is_well_formed] (gen_is_well_formed_lemma (`framed_content_nt))

/// struct {
///     ProtocolVersion version = mls10;
///     WireFormat wire_format;
///     FramedContent content;
///     select (FramedContentTBS.content.sender.sender_type) {
///         case member:
///         case new_member_commit:
///             GroupContext context;
///         case external:
///         case new_member_proposal:
///             struct{};
///     };
/// } FramedContentTBS;

type framed_content_tbs_nt (bytes:Type0) {|bytes_like bytes|} = {
  version: protocol_version_nt;
  wire_format: wire_format_nt;
  content: framed_content_nt bytes;
  [@@@ with_parser #bytes (ps_static_option (S_member? content.sender || S_new_member_commit? content.sender) ps_group_context_nt)]
  group_context: static_option (S_member? content.sender || S_new_member_commit? content.sender) (group_context_nt bytes);
}

%splice [ps_framed_content_tbs_nt] (gen_parser (`framed_content_tbs_nt))

instance parseable_serializeable_framed_content_tbs_nt (bytes:Type0) {|bytes_like bytes|}: parseable_serializeable bytes (framed_content_tbs_nt bytes) = mk_parseable_serializeable ps_framed_content_tbs_nt

/// struct {
///     /* SignWithLabel(., "FramedContentTBS", FramedContentTBS) */
///     opaque signature<V>;
///     select (FramedContent.content_type) {
///         case commit:
///             /*
///               MAC(confirmation_key,
///                   GroupContext.confirmed_transcript_hash)
///             */
///             MAC confirmation_tag;
///         case application:
///         case proposal:
///             struct{};
///     };
/// } FramedContentAuthData;

type framed_content_auth_data_nt (bytes:Type0) {|bl:bytes_like bytes|} (content_type:content_type_nt) = {
  signature: mls_bytes bytes;
  [@@@ with_parser #bytes (ps_static_option (content_type = CT_commit) ps_mac_nt)]
  confirmation_tag: static_option (content_type = CT_commit) (mac_nt bytes);
}

%splice [ps_framed_content_auth_data_nt] (gen_parser (`framed_content_auth_data_nt))

/// struct {
///     WireFormat wire_format;
///     FramedContent content;
///     FramedContentAuthData auth;
/// } AuthenticatedContent;

type authenticated_content_nt (bytes:Type0) {|bytes_like bytes|} = {
  wire_format: wire_format_nt;
  content: framed_content_nt bytes;
  auth: framed_content_auth_data_nt bytes content.content.content_type;
}

%splice [ps_authenticated_content_nt] (gen_parser (`authenticated_content_nt))

/// struct {
///   FramedContentTBS content_tbs;
///   FramedContentAuthData auth;
/// } AuthenticatedContentTBM;

type authenticated_content_tbm_nt (bytes:Type0) {|bytes_like bytes|} = {
  content_tbs: framed_content_tbs_nt bytes;
  auth: framed_content_auth_data_nt bytes content_tbs.content.content.content_type;
}

%splice [ps_authenticated_content_tbm_nt] (gen_parser (`authenticated_content_tbm_nt))

instance parseable_serializeable_authenticated_content_tbm_nt (bytes:Type0) {|bytes_like bytes|}: parseable_serializeable bytes (authenticated_content_tbm_nt bytes) = mk_parseable_serializeable ps_authenticated_content_tbm_nt

/// struct {
///     FramedContent content;
///     FramedContentAuthData auth;
///     select (PublicMessage.content.sender.sender_type) {
///         case member:
///             MAC membership_tag;
///         case external:
///         case new_member_commit:
///         case new_member_proposal:
///             struct{};
///     };
/// } PublicMessage;

type public_message_nt (bytes:Type0) {|bytes_like bytes|} = {
  content: framed_content_nt bytes;
  auth: framed_content_auth_data_nt bytes content.content.content_type;
  [@@@with_parser #bytes (ps_static_option (S_member? content.sender) ps_mac_nt)]
  membership_tag: static_option (S_member? content.sender) (mac_nt bytes);
}

%splice [ps_public_message_nt] (gen_parser (`public_message_nt))

/// struct {
///     opaque group_id<V>;
///     uint64 epoch;
///     ContentType content_type;
///     opaque authenticated_data<V>;
///     opaque encrypted_sender_data<V>;
///     opaque ciphertext<V>;
/// } PrivateMessage;

type private_message_nt (bytes:Type0) {|bytes_like bytes|} = {
  group_id: mls_bytes bytes;
  epoch: nat_lbytes 8;
  content_type: content_type_nt;
  authenticated_data: mls_bytes bytes;
  encrypted_sender_data: mls_bytes bytes;
  ciphertext: mls_bytes bytes;
}

%splice [ps_private_message_nt] (gen_parser (`private_message_nt))

/// struct {
///     select (PrivateMessage.content_type) {
///         case application:
///           opaque application_data<V>;
///
///         case proposal:
///           Proposal proposal;
///
///         case commit:
///           Commit commit;
///     };
///
///     FramedContentAuthData auth;
///     opaque padding[length_of_padding];
/// } PrivateMessageContent;

type private_message_content_data_nt (bytes:Type0) {|bytes_like bytes|} (content_type: content_type_nt) = {
  content: mls_untagged_content_nt bytes content_type;
  auth: framed_content_auth_data_nt bytes content_type;
}

%splice [ps_private_message_content_data_nt] (gen_parser (`private_message_content_data_nt))

let is_nat_zero (n:nat_lbytes 1) = n = 0
let zero_byte = refined (nat_lbytes 1) is_nat_zero
let ps_zero_byte (#bytes:Type0) {|bytes_like bytes|} = refine #bytes (ps_nat_lbytes 1) is_nat_zero

type private_message_content_nt (bytes:Type0) {|bytes_like bytes|} (content_type: content_type_nt) = {
  data: private_message_content_data_nt bytes content_type;
  padding: list zero_byte;
}

val pse_private_message_content_nt: #bytes:Type0 -> {|bytes_like bytes|} -> content_type:content_type_nt -> parser_serializer_whole bytes (private_message_content_nt bytes content_type)
let pse_private_message_content_nt #bytes #bl content_type =
  let iso = mk_isomorphism_between
    (fun (|data, padding|) -> {data; padding})
    (fun {data; padding} -> (|data, padding|))
  in
  isomorphism_whole
    (bind_whole (ps_private_message_content_data_nt content_type) (fun _ -> ps_whole_list ps_zero_byte))
    iso

instance parseable_serializeable_private_message_content_nt (bytes:Type0) {|bytes_like bytes|} (content_type:content_type_nt): parseable_serializeable bytes (private_message_content_nt bytes content_type) = mk_parseable_serializeable_from_whole (pse_private_message_content_nt content_type)

/// struct {
///     opaque group_id<V>;
///     uint64 epoch;
///     ContentType content_type;
///     opaque authenticated_data<V>;
/// } PrivateContentAAD;

type private_content_aad_nt (bytes:Type0) {|bytes_like bytes|} = {
  group_id: mls_bytes bytes;
  epoch: nat_lbytes 8;
  content_type: content_type_nt;
  authenticated_data: mls_bytes bytes;
}

%splice [ps_private_content_aad_nt] (gen_parser (`private_content_aad_nt))

instance parseable_serializeable_private_content_aad_nt (bytes:Type0) {|bytes_like bytes|}: parseable_serializeable bytes (private_content_aad_nt bytes) = mk_parseable_serializeable ps_private_content_aad_nt

/// struct {
///     uint32 leaf_index;
///     uint32 generation;
///     opaque reuse_guard[4];
/// } SenderData;

type sender_data_nt (bytes:Type0) {|bytes_like bytes|} = {
  leaf_index: nat_lbytes 4;
  generation: nat_lbytes 4;
  reuse_guard: lbytes bytes 4;
}

%splice [ps_sender_data_nt] (gen_parser (`sender_data_nt))

instance parseable_serializeable_sender_data_nt (bytes:Type0) {|bytes_like bytes|}: parseable_serializeable bytes (sender_data_nt bytes) = mk_parseable_serializeable ps_sender_data_nt

/// struct {
///     opaque group_id<V>;
///     uint64 epoch;
///     ContentType content_type;
/// } SenderDataAAD;

type sender_data_aad_nt (bytes:Type0) {|bytes_like bytes|} = {
  group_id: mls_bytes bytes;
  epoch: nat_lbytes 8;
  content_type: content_type_nt;
}

%splice [ps_sender_data_aad_nt] (gen_parser (`sender_data_aad_nt))

instance parseable_serializeable_sender_data_aad_nt (bytes:Type0) {|bytes_like bytes|}: parseable_serializeable bytes (sender_data_aad_nt bytes) = mk_parseable_serializeable ps_sender_data_aad_nt

/// struct {
///     WireFormat wire_format;
///     FramedContent content; /* with content_type == commit */
///     opaque signature<V>;
/// } ConfirmedTranscriptHashInput;

type confirmed_transcript_hash_input_nt (bytes:Type0) {|bytes_like bytes|} = {
  wire_format: wire_format_nt;
  content: framed_content_nt bytes;
  signature: mls_bytes bytes;
}

%splice [ps_confirmed_transcript_hash_input_nt] (gen_parser (`confirmed_transcript_hash_input_nt))
%splice [ps_confirmed_transcript_hash_input_nt_is_well_formed] (gen_is_well_formed_lemma (`confirmed_transcript_hash_input_nt))

instance parseable_serializeable_confirmed_transcript_hash_input_nt (bytes:Type0) {|bytes_like bytes|}: parseable_serializeable bytes (confirmed_transcript_hash_input_nt bytes) = mk_parseable_serializeable ps_confirmed_transcript_hash_input_nt

/// struct {
///     MAC confirmation_tag;
/// } InterimTranscriptHashInput;

type interim_transcript_hash_input_nt (bytes:Type0) {|bytes_like bytes|} = {
  confirmation_tag: mac_nt bytes;
}

%splice [ps_interim_transcript_hash_input_nt] (gen_parser (`interim_transcript_hash_input_nt))
%splice [ps_interim_transcript_hash_input_nt_is_well_formed] (gen_is_well_formed_lemma (`interim_transcript_hash_input_nt))

instance parseable_serializeable_interim_transcript_hash_input_nt (bytes:Type0) {|bytes_like bytes|}: parseable_serializeable bytes (interim_transcript_hash_input_nt bytes) = mk_parseable_serializeable ps_interim_transcript_hash_input_nt

/// struct {
///     ProtocolVersion version = mls10;
///     WireFormat wire_format;
///     select (MLSMessage.wire_format) {
///         case mls_public_message:
///             PublicMessage public_message;
///         case mls_private_message:
///             PrivateMessage private_message;
///         case mls_welcome:
///             Welcome welcome;
///         case mls_group_info:
///             GroupInfo group_info;
///         case mls_key_package:
///             KeyPackage key_package;
///     };
/// } MLSMessage;

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
