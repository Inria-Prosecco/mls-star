module MLS.TreeSync.Invariants.AuthService

open Comparse
open MLS.Crypto
open MLS.Tree
open MLS.TreeCommon
open MLS.TreeSync.NetworkTypes
open MLS.TreeSync.Types

#set-options "--fuel 1 --ifuel 1"

/// Abstraction for the Authentication Service (AS).
/// The goal for the AS is to verify that a signature public key belong to some credential.
/// To make no assumption on how it is implemented, we abstract it away:
/// - when a signature public key and a credential is validated by the AS, it gives a token of type `token_t`,
/// - we also obtain some relationship between the signature public key, credential and the token (`credential_ok`).
/// We store tokens for every leaf with the `as_tokens` type,
/// and have the invariant that every leaf identity has been validated by the AS, using the tokens.
/// At the end, there are several instantiations for `as_parameters`:
/// - in the DY* proofs,
/// - in the executable, concrete MLS API.

type as_input (bytes:Type0) {|bytes_like bytes|} = signature_public_key_nt bytes & credential_nt bytes

val leaf_node_to_as_input:
  #bytes:Type0 -> {|bytes_like bytes|} -> #tkt:treekem_types bytes ->
  leaf_node_nt bytes tkt ->
  as_input bytes
let leaf_node_to_as_input #bytes #bl #tkt ln =
  (ln.data.signature_key, ln.data.credential)

noeq type as_parameters (bytes:Type0) {|bytes_like bytes|} = {
  token_t: Type0;
  credential_ok: as_input bytes -> token_t -> prop;
  valid_successor: as_input bytes -> as_input bytes -> prop;
}

/// An array of tokens for every leaf of a tree.
/// Internally it's defined as a tree with no internal node content,
/// because it's easier to manipulate with TreeSync like that in the proofs
let as_tokens (bytes:Type0) {|bytes_like bytes|} (token_t:Type0) = tree (option token_t) unit

val as_add_update:
  #bytes:Type0 -> {|bytes_like bytes|} -> #asp:as_parameters bytes ->
  #l:nat -> #i:tree_index l ->
  as_tokens bytes asp.token_t l i -> leaf_index l i -> asp.token_t ->
  as_tokens bytes asp.token_t l i
let as_add_update #bytes #bl #asp #l #i t li token =
  tree_change_path t li (Some token) ()

val as_remove:
  #bytes:Type0 -> {|bytes_like bytes|} -> #asp:as_parameters bytes ->
  #l:nat -> #i:tree_index l ->
  as_tokens bytes asp.token_t l i -> leaf_index l i ->
  as_tokens bytes asp.token_t l i
let as_remove #bytes #bl #asp #l #i t li =
  tree_change_path t li None ()

val as_truncate:
  #bytes:Type0 -> {|bytes_like bytes|} -> #asp:as_parameters bytes ->
  #l:pos ->
  as_tokens bytes asp.token_t l 0 ->
  as_tokens bytes asp.token_t (l-1) 0
let as_truncate #bytes #bl #asp #l t =
  let TNode _ left _ = t in
  left

val as_extend:
  #bytes:Type0 -> {|bytes_like bytes|} -> #asp:as_parameters bytes ->
  #l:nat ->
  as_tokens bytes asp.token_t l 0 ->
  as_tokens bytes asp.token_t (l+1) 0
let as_extend #bytes #bl #asp #l t =
  TNode () t (mk_blank_tree_general _ _ None ())

val one_credential_ok:
  #bytes:Type0 -> {|bytes_like bytes|} -> #tkt:treekem_types bytes -> #asp:as_parameters bytes ->
  #l:nat -> #i:tree_index l ->
  treesync bytes tkt l i -> as_tokens bytes asp.token_t l i -> li:leaf_index l i ->
  prop
let one_credential_ok #bytes #bl #tkt #asp #l #i ts ast li =
  match leaf_at ts li, leaf_at ast li with
  | Some ln, Some as_token -> asp.credential_ok ((ln <: leaf_node_nt bytes tkt).data.signature_key, (ln <: leaf_node_nt bytes tkt).data.credential) as_token
  | None, None -> True
  | _, _ -> False

/// The authentication service invariant:
/// Every non-blank leaf is associated with a token that attests its identity was validated by the AS.
val all_credentials_ok:
  #bytes:Type0 -> {|bytes_like bytes|} -> #tkt:treekem_types bytes -> #asp:as_parameters bytes ->
  #l:nat -> #i:tree_index l ->
  treesync bytes tkt l i -> as_tokens bytes asp.token_t l i ->
  prop
let all_credentials_ok #bytes #bl #tkt #asp #l #i ts ast =
  forall li. one_credential_ok ts ast li
