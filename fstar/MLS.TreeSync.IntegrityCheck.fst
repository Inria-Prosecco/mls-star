module MLS.TreeSync.IntegrityCheck

open Comparse
open MLS.Crypto
open MLS.Tree
open MLS.TreeSync
open MLS.TreeSync.Types
open MLS.NetworkBinder
open MLS.NetworkTypes
open MLS.TreeSync.Extensions
open MLS.TreeSync.ParentHash
open MLS.TreeKEM.Types
open MLS.TreeSyncTreeKEMBinder
open MLS.Result

#set-options "--fuel 0 --ifuel 0"

type leaf_integrity_error =
  | LIE_BadSignature
  | LIE_ExtensionsNotInCapabilities

type node_integrity_error =
  | NIE_BadParentHash

type integrity_error =
  | IE_LeafError: leaf_integrity_error -> leaf_index:nat -> integrity_error
  | IE_NodeError: node_integrity_error -> nb_left_leaves:nat -> level:nat -> integrity_error

type integrity_either =
  | IE_Good: integrity_either
  | IE_Errors: list integrity_error -> integrity_either

#push-options "--ifuel 1"
private val op_Amp_Amp_Amp: integrity_either -> integrity_either -> integrity_either
let op_Amp_Amp_Amp i1 i2 =
  match i1, i2 with
  | IE_Good, _ -> i2
  | IE_Errors l1, IE_Good -> i1
  | IE_Errors l1, IE_Errors l2 -> IE_Errors (l1@l2)
#pop-options

val integrity_either_to_bool: integrity_either -> bool
let integrity_either_to_bool ie =
  match ie with
  | IE_Good -> true
  | _ -> false

val check_signature: #bytes:Type0 -> {|crypto_bytes bytes|} -> leaf_package_t bytes -> bytes -> result (option leaf_integrity_error)
let check_signature #bytes #cb lp group_id =
  if not (length lp.credential.signature_key = sign_public_key_length #bytes) then
    error "check_leaf_package: signature key has wrong length"
  else if not (length lp.signature = sign_signature_length #bytes) then
    error "check_leaf_package: signature has wrong length"
  else if not (length group_id < pow2 30) then
    error "check_leaf_package: group_id too long"
  else (
    leaf_node <-- leaf_package_to_network lp;
    let tbs = {
      data = leaf_node.data;
      group_id = (match leaf_node.data.source with | LNS_commit () | LNS_update () -> group_id | _ -> ());
    } in
    let leaf_package_bytes: bytes = serialize (leaf_node_tbs_nt bytes) tbs in
    signature_ok <-- verify_with_label lp.credential.signature_key (string_to_bytes #bytes "LeafNodeTBS") leaf_package_bytes lp.signature;
    if signature_ok then
      return None
    else
      return (Some LIE_BadSignature)
  )

val check_capabilities: #bytes:Type0 -> {|bytes_like bytes|} -> leaf_package_t bytes -> result (option leaf_integrity_error)
let check_capabilities #bytes #bl lp =
  extensions_list <-- get_extension_list lp.extensions;
  let capabilities = lp.capabilities in
  let extension_inclusion = (
    List.Tot.for_all (fun ext_type ->
      List.Tot.mem ext_type (Seq.seq_to_list capabilities.extensions)
    ) extensions_list
  ) in
  if extension_inclusion then return None
  else return (Some LIE_ExtensionsNotInCapabilities)

val check_lifetime: #bytes:Type0 -> {|bytes_like bytes|} -> leaf_package_t bytes -> result (option leaf_integrity_error)
let check_lifetime #bytes #bl lp =
  return None //TODO

val convert_opt_leaf_error_to_either: option leaf_integrity_error -> nat -> integrity_either
let convert_opt_leaf_error_to_either opt leaf_index =
  match opt with
  | None -> IE_Good
  | Some x -> IE_Errors [IE_LeafError x leaf_index]

val check_leaf: #bytes:Type0 -> {|crypto_bytes bytes|} -> nat -> olp:option (leaf_package_t bytes) -> bytes -> result integrity_either
let check_leaf #bytes #cb leaf_index olp group_id =
  match olp with
  | None -> return IE_Good
  | Some lp -> (
    signature_check <-- check_signature lp group_id;
    capabilities_check <-- check_capabilities lp;
    lifetime_check <-- check_lifetime lp;
    let signature_either = convert_opt_leaf_error_to_either signature_check leaf_index in
    let capabilities_either = convert_opt_leaf_error_to_either capabilities_check leaf_index in
    let lifetime_either = convert_opt_leaf_error_to_either lifetime_check leaf_index in
    return (signature_either &&& capabilities_either &&& lifetime_either)
  )

#push-options "--ifuel 1"
val get_original_right_node: #bytes:Type0 -> {|bytes_like bytes|} -> #l:nat -> #n:tree_size l -> treesync bytes l n -> option (l_res:nat & n_res:tree_size l_res & treesync bytes l_res n_res)
let rec get_original_right_node #bytes #bl #l #n t =
  match t with
  | TNode (Some np) _ _ ->
    Some (|l, n, t|)
  | TNode None left _ ->
    get_original_right_node left
  | TSkip _ t' ->
    get_original_right_node t'
  | TLeaf (Some lp) ->
    Some (|l, n, t|)
  | TLeaf None ->
    None
#pop-options

#push-options "--ifuel 1"
val has_child_with_parent_hash: #bytes:Type0 -> {|crypto_bytes bytes|} -> #l:nat -> #n:tree_size l -> t:treesync bytes l n -> bytes -> bool
let rec has_child_with_parent_hash #bytes #cb #l #n t parent_hash =
  match t with
  | TLeaf None -> false
  | TLeaf (Some lp) -> (
    match lp.source with
    | LNS_commit () -> (lp.parent_hash <: bytes) = parent_hash
    | _ -> false
  )
  | TSkip _ t' ->
    has_child_with_parent_hash t' parent_hash
  | TNode (Some kp) _ _ ->
    kp.parent_hash = parent_hash
  | TNode None left right ->
    has_child_with_parent_hash left parent_hash || has_child_with_parent_hash right parent_hash
#pop-options

#push-options "--ifuel 1"
val check_internal_node: #bytes:Type0 -> {|crypto_bytes bytes|} -> #l:nat -> #n:tree_size l -> nat -> t:treesync bytes l n{TNode? t} -> result integrity_either
let check_internal_node #bytes #cb #l #n nb_left_leaves t =
  let (TNode onp left right) = t in
  match onp with
  | None -> return IE_Good
  | Some np -> (
    parent_hash_from_left_ok <-- (
      computed_parent_hash <-- compute_parent_hash_from_dir np.content.content np.parent_hash nb_left_leaves t Left;
      return (has_child_with_parent_hash left computed_parent_hash)
    );
    parent_hash_from_right_ok <-- (
      computed_parent_hash <-- compute_parent_hash_from_dir np.content.content np.parent_hash nb_left_leaves t Right;
      return (has_child_with_parent_hash right computed_parent_hash)
    );
    if (parent_hash_from_left_ok || parent_hash_from_right_ok) then
      return IE_Good
    else
      return (IE_Errors [IE_NodeError NIE_BadParentHash nb_left_leaves l])
  )
#pop-options

#push-options "--ifuel 1"
val check_treesync_aux: #bytes:Type0 -> {|crypto_bytes bytes|} -> #l:nat -> #n:tree_size l -> nat -> treesync bytes l n -> bytes -> result integrity_either
let rec check_treesync_aux #bytes #cb #l #n nb_left_leaves t group_id =
  match t with
  | TNode onp left right ->
    left_ok <-- check_treesync_aux nb_left_leaves left group_id;
    right_ok <-- check_treesync_aux (nb_left_leaves + pow2 (l-1)) right group_id;
    cur_ok <-- check_internal_node nb_left_leaves t;
    return (left_ok &&& cur_ok &&& right_ok)
  | TSkip _ t' ->
    check_treesync_aux nb_left_leaves t' group_id
  | TLeaf olp ->
    check_leaf nb_left_leaves olp group_id
#pop-options

val check_treesync: #bytes:Type0 -> {|crypto_bytes bytes|} -> #l:nat -> #n:tree_size l -> treesync bytes l n -> bytes -> result integrity_either
let check_treesync #bytes #cb #l #n t group_id =
  check_treesync_aux 0 t group_id
