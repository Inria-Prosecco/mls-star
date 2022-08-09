module MLS.TreeSync.IntegrityCheck

open Comparse
open MLS.Crypto
open MLS.Tree
open MLS.TreeSync
open MLS.TreeSync.NetworkTypes
open MLS.TreeSync.Types
open MLS.TreeSync.Extensions
open MLS.TreeSync.ParentHash
open MLS.Result

#set-options "--fuel 0 --ifuel 0"

type leaf_integrity_error =
  | LIE_BadSignature
  | LIE_ExtensionsNotInCapabilities

type node_integrity_error =
  | NIE_BadParentHash

type integrity_error =
  | IE_LeafError: leaf_integrity_error -> leaf_index:nat -> integrity_error
  | IE_NodeError: node_integrity_error -> level:nat -> ind:tree_index level -> integrity_error

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

val check_signature: #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes -> leaf_node_nt bytes tkt -> bytes -> nat -> result (option leaf_integrity_error)
let check_signature #bytes #cb #tkt lp group_id leaf_index =
  if not (length #bytes lp.data.signature_key = sign_public_key_length #bytes) then
    error "check_leaf_package: signature key has wrong length"
  else if not (length #bytes lp.signature = sign_signature_length #bytes) then
    error "check_leaf_package: signature has wrong length"
  else if not (length group_id < pow2 30) then
    error "check_leaf_package: group_id too long"
  else if not (leaf_index < pow2 32) then
    error "check_leaf_package: leaf_index too big"
  else (
    let tbs = ({
      data = lp.data;
      group_id = (match lp.data.source with | LNS_commit () | LNS_update () -> group_id | _ -> ());
      leaf_index = (match lp.data.source with | LNS_commit () | LNS_update () -> leaf_index | _ -> ());
    } <: leaf_node_tbs_nt bytes tkt) in
    let leaf_package_bytes: bytes = serialize (leaf_node_tbs_nt bytes _) tbs in
    if not (length leaf_package_bytes < pow2 30 && sign_with_label_pre #bytes "LeafNodeTBS" (length #bytes leaf_package_bytes)) then error "check_signature: tbs too long"
    else (
      if verify_with_label #bytes lp.data.signature_key "LeafNodeTBS" leaf_package_bytes lp.signature then
        return None
      else
        return (Some LIE_BadSignature)
    )
  )

val check_capabilities: #bytes:Type0 -> {|bytes_like bytes|} -> #tkt:treekem_types bytes -> leaf_node_nt bytes tkt -> result (option leaf_integrity_error)
let check_capabilities #bytes #bl lp =
  let extensions_list = get_extension_list lp.data.extensions in
  let capabilities = lp.data.capabilities in
  let extension_inclusion = (
    List.Tot.for_all (fun ext_type ->
      List.Tot.mem ext_type capabilities.extensions
    ) extensions_list
  ) in
  if extension_inclusion then return None
  else return (Some LIE_ExtensionsNotInCapabilities)

val check_lifetime: #bytes:Type0 -> {|bytes_like bytes|} -> #tkt:treekem_types bytes -> leaf_node_nt bytes tkt -> result (option leaf_integrity_error)
let check_lifetime #bytes #bl #tkt lp =
  return None //TODO

val convert_opt_leaf_error_to_either: option leaf_integrity_error -> nat -> integrity_either
let convert_opt_leaf_error_to_either opt leaf_index =
  match opt with
  | None -> IE_Good
  | Some x -> IE_Errors [IE_LeafError x leaf_index]

val check_leaf: #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes -> nat -> olp:option (leaf_node_nt bytes tkt) -> bytes -> result integrity_either
let check_leaf #bytes #cb leaf_index olp group_id =
  match olp with
  | None -> return IE_Good
  | Some lp -> (
    signature_check <-- check_signature lp group_id leaf_index;
    capabilities_check <-- check_capabilities lp;
    lifetime_check <-- check_lifetime lp;
    let signature_either = convert_opt_leaf_error_to_either signature_check leaf_index in
    let capabilities_either = convert_opt_leaf_error_to_either capabilities_check leaf_index in
    let lifetime_either = convert_opt_leaf_error_to_either lifetime_check leaf_index in
    return (signature_either &&& capabilities_either &&& lifetime_either)
  )

#push-options "--ifuel 1"
val has_child_with_parent_hash: #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes -> #l:nat -> #i:tree_index l -> t:treesync bytes tkt l i -> bytes -> bool
let rec has_child_with_parent_hash #bytes #cb #tkt #l t parent_hash =
  match t with
  | TLeaf None -> false
  | TLeaf (Some lp) -> (
    match lp.data.source with
    | LNS_commit () -> (lp.data.parent_hash <: bytes) = parent_hash
    | _ -> false
  )
  | TNode (Some kp) _ _ ->
    kp.parent_hash = parent_hash
  | TNode None left right ->
    has_child_with_parent_hash left parent_hash || has_child_with_parent_hash right parent_hash
#pop-options

#push-options "--ifuel 1"
val check_internal_node: #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes -> #l:nat -> #i:tree_index l -> t:treesync bytes tkt l i{TNode? t} -> result integrity_either
let check_internal_node #bytes #cb #tkt #l #i t =
  let (TNode onp left right) = t in
  match onp with
  | None -> return IE_Good
  | Some np -> (
    parent_hash_from_left_ok <-- (
      if not (compute_parent_hash_pre np.content (length #bytes np.parent_hash) (MLS.TreeSync.Invariants.ParentHash.un_add right np.unmerged_leaves)) then
        error "check_internal_node: parent hash precondition not verified"
      else (
        let computed_parent_hash = compute_parent_hash np.content np.parent_hash (MLS.TreeSync.Invariants.ParentHash.un_add right np.unmerged_leaves) in
        return (has_child_with_parent_hash left computed_parent_hash)
      )
    );
    parent_hash_from_right_ok <-- (
      if not (compute_parent_hash_pre np.content (length #bytes np.parent_hash) (MLS.TreeSync.Invariants.ParentHash.un_add left np.unmerged_leaves)) then
        error "check_internal_node: parent hash precondition not verified"
      else (
        let computed_parent_hash = compute_parent_hash np.content np.parent_hash (MLS.TreeSync.Invariants.ParentHash.un_add left np.unmerged_leaves) in
        return (has_child_with_parent_hash right computed_parent_hash)
      )
    );
    if (parent_hash_from_left_ok || parent_hash_from_right_ok) then
      return IE_Good
    else
      return (IE_Errors [IE_NodeError NIE_BadParentHash l i])
  )
#pop-options

#push-options "--ifuel 1"
val check_treesync: #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes -> #l:nat -> #i:tree_index l -> treesync bytes tkt l i -> bytes -> result integrity_either
let rec check_treesync #bytes #cb #tkt #l #i t group_id =
  match t with
  | TNode onp left right ->
    left_ok <-- check_treesync left group_id;
    right_ok <-- check_treesync right group_id;
    cur_ok <-- check_internal_node t;
    return (left_ok &&& cur_ok &&& right_ok)
  | TLeaf olp ->
    check_leaf i olp group_id
#pop-options
