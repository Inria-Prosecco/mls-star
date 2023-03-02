module MLS.TreeSync.Invariants.AuthService

open Comparse
open MLS.Crypto
open MLS.Tree
open MLS.TreeCommon
open MLS.TreeSync.NetworkTypes
open MLS.TreeSync.Types

#set-options "--fuel 1 --ifuel 1"

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

// Actually an array, but it's easier to manipulate with TreeSync like that
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

val all_credentials_ok:
  #bytes:Type0 -> {|bytes_like bytes|} -> #tkt:treekem_types bytes -> #asp:as_parameters bytes ->
  #l:nat -> #i:tree_index l ->
  treesync bytes tkt l i -> as_tokens bytes asp.token_t l i ->
  prop
let all_credentials_ok #bytes #bl #tkt #asp #l #i ts ast =
  forall li. one_credential_ok ts ast li
