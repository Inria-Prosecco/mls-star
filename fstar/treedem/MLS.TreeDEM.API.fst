module MLS.TreeDEM.API

open Comparse
open MLS.Crypto
open MLS.Tree
open MLS.NetworkTypes
open MLS.TreeDEM.NetworkTypes
open MLS.TreeDEM.Keys
open MLS.TreeDEM.Message.Framing
open MLS.TreeDEM.API.Types
open MLS.Result

#set-options "--fuel 0 --ifuel 0"

#push-options "--ifuel 1"
type treedem_init_arguments (bytes:Type0) {|bytes_like bytes|} = {
  tree_height: nat;
  my_leaf_index: leaf_index tree_height 0;
  group_context: group_context_nt bytes;
  encryption_secret: bytes;
  sender_data_secret: bytes;
  membership_key: bytes;
  my_signature_key: bytes;
  verification_keys: tree (option (signature_public_key_nt bytes)) unit tree_height 0;
}
#pop-options

val init:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  treedem_init_arguments bytes ->
  result (treedem_state bytes)
let init #bytes #cb {tree_height; my_leaf_index; group_context; encryption_secret; sender_data_secret; membership_key; my_signature_key; verification_keys} =
  let? leaf_tree_secret = leaf_kdf encryption_secret my_leaf_index in
  let? my_application_ratchet = init_application_ratchet leaf_tree_secret in
  let? my_handshake_ratchet = init_handshake_ratchet leaf_tree_secret in
  return ({
    tree_height;
    my_leaf_index; 
    group_context;
    encryption_secret;
    sender_data_secret;
    membership_key;
    my_signature_key;
    my_handshake_ratchet;
    my_application_ratchet;
    verification_keys;
  } <: treedem_state bytes)

(*** Authentication ***)

/// Proposals and application messages are authenticated using a single signature.
/// This function will compute it.

val authenticate_non_commit:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  treedem_state bytes ->
  wf:wire_format_nt ->
  msg:framed_content_nt bytes{msg.content.content_type =!= CT_commit} ->
  sign_nonce bytes ->
  result (res:authenticated_content_nt bytes{res.wire_format == wf /\ res.content == msg})
let authenticate_non_commit #bytes #cb st wf msg nonce =
  let? signature = compute_message_signature st.my_signature_key nonce wf msg (mk_static_option st.group_context) in
  return ({
    wire_format = wf;
    content = msg;
    auth = {
      signature;
      confirmation_tag = ();
    }
  } <: res:authenticated_content_nt bytes{res.wire_format == wf /\ res.content == msg})

/// Commits are authenticated using both a signature and a confirmation tag.
/// Because the confirmation tag is computed using the next epoch's confirmation key,
/// which itself depend on the confirmed transcript hash,
/// which itself depend on the commit's signature,
/// commits are authenticated in two steps:
/// first the signature,
/// then the confirmation tag.

type half_authenticated_commit (bytes:Type0) {|bytes_like bytes|} = {
  wire_format: wire_format_nt;
  content: content:framed_content_nt bytes{content.content.content_type == CT_commit};
  signature: mls_bytes bytes;
}

val start_authenticate_commit:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  treedem_state bytes ->
  wf:wire_format_nt ->
  msg:framed_content_nt bytes{msg.content.content_type == CT_commit} ->
  sign_nonce bytes ->
  result (res:half_authenticated_commit bytes{res.wire_format == wf /\ res.content == msg})
let start_authenticate_commit #bytes #cb st wf msg nonce =
  let? signature = compute_message_signature st.my_signature_key nonce wf msg (mk_static_option st.group_context) in
  return ({
    wire_format = wf;
    content = msg;
    signature;
  } <: res:half_authenticated_commit bytes{res.wire_format == wf /\ res.content == msg})

val finish_authenticate_commit:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  msg:half_authenticated_commit bytes ->
  bytes ->
  result (res:authenticated_content_nt bytes{res.wire_format == msg.wire_format /\ res.content == msg.content})
let finish_authenticate_commit #bytes #cb msg confirmation_tag  =
  if not (length confirmation_tag < pow2 30) then error "finish_authenticate_commit: confirmation_tag too long"
  else (
    return ({
      wire_format = msg.wire_format;
      content = msg.content;
      auth = {
        signature = msg.signature;
        confirmation_tag;
      }
    } <: res:authenticated_content_nt bytes{res.wire_format == msg.wire_format /\ res.content == msg.content})
  )

/// Functions to verify the authentication.

val verify_signature:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  treedem_state bytes ->
  authenticated_content_nt bytes ->
  bool
let verify_signature #bytes #cb st msg =
  let opt_verif_key = 
    match msg.content.sender with
    | S_member leaf_index -> (
      if not (leaf_index < pow2 st.tree_height) then None
      else (
        leaf_at st.verification_keys leaf_index
      )
    )
    | _ -> None //TODO
  in
  match opt_verif_key with
  | None -> false
  | Some verif_key ->
    check_message_signature verif_key msg.auth.signature msg.wire_format msg.content (mk_static_option st.group_context)

val verify_confirmation_tag:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  treedem_state bytes ->
  authenticated_content_nt bytes ->
  bytes ->
  result bool
let verify_confirmation_tag #bytes #cb st msg confirmation_tag =
  bytes_hasEq #bytes;
  match msg.content.content.content_type with
  | CT_commit ->
    return (msg.auth.confirmation_tag = confirmation_tag)
  | _ -> internal_failure "verify_confirmation_tag: not a commit"

(*** Protection ***)

/// Protect public messages, by computing or checking the membership tag

val protect_public:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  treedem_state bytes ->
  msg:authenticated_content_nt bytes{msg.wire_format == WF_mls_public_message} ->
  result (public_message_nt bytes)
let protect_public #bytes #cb st msg =
  authenticated_content_to_public_message msg (mk_static_option st.group_context) (mk_static_option st.membership_key)

val unprotect_public:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  treedem_state bytes ->
  public_message_nt bytes ->
  result (authenticated_content_nt bytes)
let unprotect_public #bytes #cb st msg =
  public_message_to_authenticated_content msg (mk_static_option st.group_context) (mk_static_option st.membership_key)

/// Protect private messages, by encrypting using the secret tree.
/// These functions are stateful, for forward secrecy.

val protect_private:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  treedem_state bytes ->
  msg:authenticated_content_nt bytes{msg.wire_format == WF_mls_private_message} ->
  lbytes bytes 4 ->
  result (private_message_nt bytes & treedem_state bytes)
let protect_private #bytes #cb st msg reuse_guard =
  let ratchet =
    match msg.content.content.content_type with
    | CT_application -> st.my_application_ratchet
    | _ -> st.my_handshake_ratchet
  in
  let? (res, new_ratchet) = authenticated_content_to_private_message msg ratchet reuse_guard st.sender_data_secret in
  let new_st =
    match msg.content.content.content_type with
    | CT_application -> { st with my_application_ratchet = new_ratchet }
    | _ -> { st with my_handshake_ratchet = new_ratchet }
  in
  return (res, new_st)

val unprotect_private:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  treedem_state bytes ->
  private_message_nt bytes ->
  result (authenticated_content_nt bytes & treedem_state bytes)
let unprotect_private #bytes #cb st msg =
  let? res = private_message_to_authenticated_content msg st.tree_height st.encryption_secret st.sender_data_secret in
  return (res, st)

