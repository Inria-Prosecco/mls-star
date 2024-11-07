module MLS.NetworkTypes

open Comparse

let mls_nat_pred (n:nat) = n < normalize_term (pow2 30)
let mls_nat_pred_eq (n:nat): Lemma(pow2 30 == normalize_term (pow2 30)) [SMTPat (mls_nat_pred n)] =
  assert_norm(pow2 30 == normalize_term (pow2 30))
type mls_nat = refined nat mls_nat_pred
val ps_mls_nat: #bytes:Type0 -> {| bytes_like bytes |} -> nat_parser_serializer bytes mls_nat_pred
let ps_mls_nat #bytes #bl =
  mk_trivial_isomorphism (refine ps_quic_nat mls_nat_pred)

val ps_mls_nat_length:
  #bytes:Type0 -> {| bytes_like bytes |} ->
  x:mls_nat ->
  Lemma (
    prefixes_length #bytes (ps_mls_nat.serialize x) == (
      if x < pow2 6 then 1
      else if x < pow2 14 then 2
      else 4
    ) /\
    pow2 6 == normalize_term (pow2 6) /\
    pow2 14 == normalize_term (pow2 14)
  )
  [SMTPat (prefixes_length #bytes (ps_mls_nat.serialize x))]
let ps_mls_nat_length #bytes #bl x = ()

type mls_bytes (bytes:Type0) {|bytes_like bytes|} = pre_length_bytes bytes mls_nat_pred
type mls_list (bytes:Type0) {|bytes_like bytes|} (#a:Type) (ps_a:parser_serializer bytes a) = pre_length_list ps_a mls_nat_pred

let ps_mls_bytes (#bytes:Type0) {|bytes_like bytes|}: parser_serializer bytes (mls_bytes bytes) = ps_pre_length_bytes mls_nat_pred ps_mls_nat
let ps_mls_list (#bytes:Type0) {|bytes_like bytes|} (#a:Type) (ps_a:parser_serializer bytes a): parser_serializer bytes (mls_list bytes ps_a) = ps_pre_length_list #bytes mls_nat_pred ps_mls_nat ps_a

let mls_ascii_string_pred (s:ascii_string): bool = mls_nat_pred (FStar.String.strlen s)
type mls_ascii_string = refined ascii_string mls_ascii_string_pred
let ps_mls_ascii_string (#bytes:Type0) {|bytes_like bytes|}: parser_serializer bytes mls_ascii_string =
  length_prefix_ps_whole mls_nat_pred ps_mls_nat (refine_whole ps_whole_ascii_string mls_ascii_string_pred)

val ps_mls_ascii_string_length:
  #bytes:Type0 -> {|bytes_like bytes|} ->
  x:mls_ascii_string ->
  Lemma (
    prefixes_length #bytes (ps_mls_ascii_string.serialize x) ==
      prefixes_length #bytes (ps_mls_nat.serialize (String.strlen x)) +
      String.strlen x
  )
  [SMTPat (prefixes_length #bytes (ps_mls_ascii_string.serialize x))]
let ps_mls_ascii_string_length #bytes #bl x =
  length_prefix_ps_whole_length #bytes mls_nat_pred ps_mls_nat (refine_whole ps_whole_ascii_string mls_ascii_string_pred) x

val ps_mls_ascii_string_is_well_formed:
  #bytes:Type0 -> {|bytes_like bytes|} ->
  pre:bytes_compatible_pre bytes ->
  x:mls_ascii_string ->
  Lemma (is_well_formed_prefix ps_mls_ascii_string pre x)
  [SMTPat (is_well_formed_prefix ps_mls_ascii_string pre x)]
let ps_mls_ascii_string_is_well_formed #bytes #bl pre x =
  assert(is_well_formed_whole ps_whole_ascii_string pre x);
  length_prefix_ps_whole_is_well_formed #bytes mls_nat_pred ps_mls_nat (refine_whole ps_whole_ascii_string mls_ascii_string_pred) pre x

/// opaque HPKEPublicKey<V>;

type hpke_public_key_nt (bytes:Type0) {|bytes_like bytes|} = mls_bytes bytes
%splice [ps_hpke_public_key_nt] (gen_parser (`hpke_public_key_nt))

/// opaque MAC<V>;

type mac_nt (bytes:Type0) {|bytes_like bytes|} = mls_bytes bytes
%splice [ps_mac_nt] (gen_parser (`mac_nt))

/// enum {
///     reserved(0),
///     mls10(1),
///     (255)
/// } ProtocolVersion;

type protocol_version_nt =
  | [@@@ with_num_tag 2 0] PV_mls_reserved: protocol_version_nt
  | [@@@ with_num_tag 2 1] PV_mls10: protocol_version_nt
  | [@@@ open_tag] PV_unknown: n:nat_lbytes 2{~(n <= 1)} -> protocol_version_nt

%splice [ps_protocol_version_nt] (gen_parser (`protocol_version_nt))

/// uint16 CipherSuite;

type cipher_suite_nt =
  | [@@@ with_num_tag 2 0x0000] CS_reserved: cipher_suite_nt
  | [@@@ with_num_tag 2 0x0001] CS_mls_128_dhkemx25519_aes128gcm_sha256_ed25519: cipher_suite_nt
  | [@@@ with_num_tag 2 0x0002] CS_mls_128_dhkemp256_aes128gcm_sha256_p256: cipher_suite_nt
  | [@@@ with_num_tag 2 0x0003] CS_mls_128_dhkemx25519_chacha20poly1305_sha256_ed25519: cipher_suite_nt
  | [@@@ with_num_tag 2 0x0004] CS_mls_256_dhkemx448_aes256gcm_sha512_ed448: cipher_suite_nt
  | [@@@ with_num_tag 2 0x0005] CS_mls_256_dhkemp521_aes256gcm_sha512_p521: cipher_suite_nt
  | [@@@ with_num_tag 2 0x0006] CS_mls_256_dhkemx448_chacha20poly1305_sha512_ed448: cipher_suite_nt
  | [@@@ with_num_tag 2 0x0007] CS_mls_256_dhkemp384_aes256gcm_sha384_p384: cipher_suite_nt
  | [@@@ open_tag] CS_unknown: n:nat_lbytes 2{~(n <= 7)} -> cipher_suite_nt

%splice [ps_cipher_suite_nt] (gen_parser (`cipher_suite_nt))

/// // See IANA registry for registered values
/// uint16 ExtensionType;

//TODO extension belong here??
type extension_type_nt: eqtype =
  | [@@@ with_num_tag 2 0x0000] ET_reserved: extension_type_nt
  | [@@@ with_num_tag 2 0x0001] ET_application_id: extension_type_nt
  | [@@@ with_num_tag 2 0x0002] ET_ratchet_tree: extension_type_nt
  | [@@@ with_num_tag 2 0x0003] ET_required_capabilities: extension_type_nt
  | [@@@ with_num_tag 2 0x0004] ET_external_pub: extension_type_nt
  | [@@@ with_num_tag 2 0x0005] ET_external_senders: extension_type_nt
  | [@@@ open_tag] ET_unknown: n:nat_lbytes 2{~(n <= 5)} -> extension_type_nt

%splice [ps_extension_type_nt] (gen_parser (`extension_type_nt))

/// struct {
///     ExtensionType extension_type;
///     opaque extension_data<V>;
/// } Extension;

type extension_nt (bytes:Type0) {|bytes_like bytes|} = {
  extension_type: extension_type_nt;
  extension_data: mls_bytes bytes;
}

%splice [ps_extension_nt] (gen_parser (`extension_nt))

/// struct {
///     uint8 present;
///     select (present) {
///         case 0: struct{};
///         case 1: T value;
///     }
/// } optional<T>;

[@@"opaque_to_smt"]
val ps_option:
  #bytes:Type0 -> {|bytes_like bytes|} -> #a:Type0 ->
  parser_serializer_prefix bytes a ->
  parser_serializer bytes (option a)
let ps_option #bytes #bl #a ps_a =
  let n_pred = (fun n -> n <= 1) in
  let b_type (x:refined (nat_lbytes 1) n_pred): Type0 =
    if x = 1 then a else unit
  in
  mk_isomorphism (option a)
    (
      bind #_ #_ #_ #b_type (refine (ps_nat_lbytes 1) n_pred) (fun present ->
        if present = 1 then
          ps_a
        else
          ps_unit
      )
    )
  (fun (|present, x|) -> match present with
    | 0 -> None
    | 1 -> Some x
  )
  (fun x -> match x with
    | None -> (|0, ()|)
    | Some x -> (|1, x|)
  )

val ps_option_length:
  #bytes:Type0 -> {|bytes_like bytes|} -> #a:Type0 ->
  ps_a:parser_serializer bytes a -> x:option a ->
  Lemma (
    prefixes_length ((ps_option ps_a).serialize x) == (
      match x with
      | None -> 1
      | Some y -> 1 + prefixes_length (ps_a.serialize y)
    )
  )
  [SMTPat (prefixes_length ((ps_option ps_a).serialize x))]
let ps_option_length #bytes #bl #a ps_a x =
  reveal_opaque (`%ps_option) (ps_option ps_a)

val ps_option_is_well_formed:
  #bytes:Type0 -> {|bytes_like bytes|} -> #a:Type0 ->
  ps_a:parser_serializer bytes a -> pre:bytes_compatible_pre bytes -> x:option a ->
  Lemma (
    is_well_formed_prefix (ps_option ps_a) pre x <==> (
      match x with
      | None -> True
      | Some y -> is_well_formed_prefix ps_a pre y
    )
  )
  [SMTPat (is_well_formed_prefix (ps_option ps_a) pre x)]
let ps_option_is_well_formed #bytes #bl #a ps_a pre x =
  reveal_opaque (`%ps_option) (ps_option ps_a)

// Special "option" type, when we know statically whether it is a "Some" or "None"

let static_option (b:bool) (a:Type): Type =
  if b then a else unit

val ps_static_option:
  #bytes:Type0 -> {|bytes_like bytes|} -> #a:Type0 ->
  b:bool -> parser_serializer_prefix bytes a ->
  parser_serializer_prefix bytes (static_option b a)
let ps_static_option #bytes #bl #a b ps_a =
  if b then ps_a else ps_unit

val mk_static_option: #b:bool -> #a:Type -> a -> static_option b a
let mk_static_option #b #a x =
  if b then x else ()

/// struct {
///     ProtocolVersion version = mls10;
///     CipherSuite cipher_suite;
///     opaque group_id<V>;
///     uint64 epoch;
///     opaque tree_hash<V>;
///     opaque confirmed_transcript_hash<V>;
///     Extension extensions<V>;
/// } GroupContext;

type group_context_nt (bytes:Type0) {|bytes_like bytes|} = {
  version: protocol_version_nt;
  cipher_suite: cipher_suite_nt;
  group_id: mls_bytes bytes;
  epoch: nat_lbytes 8;
  tree_hash: mls_bytes bytes;
  confirmed_transcript_hash: mls_bytes bytes;
  extensions: mls_list bytes ps_extension_nt;
}

%splice [ps_group_context_nt] (gen_parser (`group_context_nt))

instance parseable_serializeable_group_context_nt (bytes:Type0) {|bytes_like bytes|}: parseable_serializeable bytes (group_context_nt bytes) = mk_parseable_serializeable ps_group_context_nt

(*** Proposals ***)

/// uint16 ProposalType;

// Defined here because needed in TreeSync's proposal list in leaf node capabilities
// Actual sum type defined in TreeDEM.NetworkTypes
type proposal_type_nt =
  | [@@@ with_num_tag 2 0x0000] PT_reserved: proposal_type_nt
  | [@@@ with_num_tag 2 0x0001] PT_add: proposal_type_nt
  | [@@@ with_num_tag 2 0x0002] PT_update: proposal_type_nt
  | [@@@ with_num_tag 2 0x0003] PT_remove: proposal_type_nt
  | [@@@ with_num_tag 2 0x0004] PT_psk: proposal_type_nt
  | [@@@ with_num_tag 2 0x0005] PT_reinit: proposal_type_nt
  | [@@@ with_num_tag 2 0x0006] PT_external_init: proposal_type_nt
  | [@@@ with_num_tag 2 0x0007] PT_group_context_extensions: proposal_type_nt
  | [@@@ open_tag] PT_unknown: n:nat_lbytes 2{~(n <= 7)} -> proposal_type_nt

%splice [ps_proposal_type_nt] (gen_parser (`proposal_type_nt))

/// opaque SignaturePublicKey<V>;

type signature_public_key_nt (bytes:Type0) {|bytes_like bytes|} = mls_bytes bytes
%splice [ps_signature_public_key_nt] (gen_parser (`signature_public_key_nt))

/// // See IANA registry for registered values
/// uint16 CredentialType;

type credential_type_nt =
  | [@@@ with_num_tag 2 0x0000] CT_reserved: credential_type_nt
  | [@@@ with_num_tag 2 0x0001] CT_basic: credential_type_nt
  | [@@@ with_num_tag 2 0x0002] CT_x509: credential_type_nt
  | [@@@ open_tag] CT_unknown: n:nat_lbytes 2{~(n <= 2)} -> credential_type_nt

%splice [ps_credential_type_nt] (gen_parser (`credential_type_nt))

/// struct {
///     opaque cert_data<V>;
/// } Certificate;

type certificate_nt (bytes:Type0) {|bytes_like bytes|} = mls_bytes bytes
%splice [ps_certificate_nt] (gen_parser (`certificate_nt))

/// struct {
///     CredentialType credential_type;
///     select (Credential.credential_type) {
///         case basic:
///             opaque identity<V>;
///
///         case x509:
///             Certificate chain<V>;
///     };
/// } Credential;

type credential_nt (bytes:Type0) {|bytes_like bytes|} =
  | [@@@ with_tag CT_basic] C_basic: identity: mls_bytes bytes -> credential_nt bytes
  | [@@@ with_tag CT_x509] C_x509: chain: mls_list bytes ps_certificate_nt -> credential_nt bytes

%splice [ps_credential_nt] (gen_parser (`credential_nt))

