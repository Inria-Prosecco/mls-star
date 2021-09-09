module MLS.TreeSync.IntegrityCheck

open Lib.ByteSequence
open MLS.Crypto
open MLS.Parser
open MLS.Result
open MLS.Tree
open MLS.TreeSync
open MLS.TreeSync.Types
open MLS.NetworkBinder
open MLS.NetworkTypes
open MLS.TreeSync.Extensions
open MLS.TreeSync.ParentHash
open MLS.TreeKEM.Types
open MLS.TreeSyncTreeKEMBinder

#set-options "--fuel 0 --ifuel 0"

type leaf_integrity_error =
  | LIE_BadSignature
  | LIE_NoCapabilities
  | LIE_ExtensionsNotInCapabilities
  | LIE_NoLifetime

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

val check_signature: ciphersuite -> leaf_package_t -> result (option leaf_integrity_error)
let check_signature cs lp =
  if not (Seq.length lp.lp_credential.cred_signature_key = sign_public_key_length cs) then
    error "check_leaf_package: signature key has wrong length"
  else if not (Seq.length lp.lp_signature = sign_signature_length cs) then
    error "check_leaf_package: signature has wrong length"
  else (
    key_package <-- treesync_to_keypackage cs lp;
    let leaf_package_bytes = ps_key_package_tbs.serialize (key_package_get_tbs key_package) in
    if sign_verify cs lp.lp_credential.cred_signature_key leaf_package_bytes lp.lp_signature then
      return None
    else
      return (Some LIE_BadSignature)
  )

val check_capabilities: leaf_package_t -> result (option leaf_integrity_error)
let check_capabilities lp =
  extensions_list <-- get_extension_list lp.lp_extensions;
  let opt_capabilities_extension = get_capabilities_extension lp.lp_extensions in
  return (
    match opt_capabilities_extension with
    | None -> Some LIE_NoCapabilities
    | Some capabilities ->
      let extension_inclusion = (
        List.Tot.for_all (fun ext_type ->
          List.Tot.mem ext_type (Seq.seq_to_list capabilities.cen_extensions)
        ) extensions_list
      ) in
      if extension_inclusion then None
      else Some LIE_ExtensionsNotInCapabilities
  )

val check_lifetime: leaf_package_t -> result (option leaf_integrity_error)
let check_lifetime lp =
  let opt_lifetime_extension = get_lifetime_extension lp.lp_extensions in
  return (
    match opt_lifetime_extension with
    | None -> Some LIE_NoLifetime
    | Some lifetime ->
      None //TODO
  )

val convert_opt_leaf_error_to_either: option leaf_integrity_error -> nat -> integrity_either
let convert_opt_leaf_error_to_either opt leaf_index =
  match opt with
  | None -> IE_Good
  | Some x -> IE_Errors [IE_LeafError x leaf_index]

val check_leaf: #l:nat -> #n:tree_size l -> ciphersuite -> nat -> t:treesync l n{TLeaf? t} -> result integrity_either
let check_leaf #l #n cs leaf_index t =
  let (TLeaf (_, olp)) = t in
  match olp with
  | None -> return IE_Good
  | Some lp -> (
    signature_check <-- check_signature cs lp;
    capabilities_check <-- check_capabilities lp;
    lifetime_check <-- check_lifetime lp;
    let signature_either = convert_opt_leaf_error_to_either signature_check leaf_index in
    let capabilities_either = convert_opt_leaf_error_to_either capabilities_check leaf_index in
    let lifetime_either = convert_opt_leaf_error_to_either lifetime_check leaf_index in
    return (signature_either &&& capabilities_either &&& lifetime_either)
  )

#push-options "--ifuel 1"
val get_original_right_node: #l:nat -> #n:tree_size l -> treesync l n -> option (l_res:nat & n_res:tree_size l_res & treesync l_res n_res)
let rec get_original_right_node #l #n t =
  match t with
  | TNode (_, Some np) _ _ ->
    Some (|l, n, t|)
  | TNode (_, None) left _ ->
    get_original_right_node left
  | TSkip _ t' ->
    get_original_right_node t'
  | TLeaf (_, Some lp) ->
    Some (|l, n, t|)
  | TLeaf (_, None) ->
    None
#pop-options

#push-options "--ifuel 1"
val get_parent_hash: #l:nat -> #n:tree_size l -> treesync l n -> option bytes
let get_parent_hash #l #n t =
  match t with
  | TNode (_, None) _ _ -> None
  | TNode (_, Some np) _ _ -> Some np.np_parent_hash
  | TSkip _ _ -> None
  | TLeaf (_, None) -> None
  | TLeaf (_, Some lp) -> (
    match get_parent_hash_extension lp.lp_extensions with
    | Some parent_hash_ext -> Some (parent_hash_ext.phen_parent_hash)
    | None -> None
  )
#pop-options

#push-options "--ifuel 1"
val check_internal_node: #l:nat -> #n:tree_size l -> ciphersuite -> nat -> t:treesync l n{TNode? t} -> result integrity_either
let check_internal_node #l #n cs nb_left_leaves t =
  let (TNode (_, onp) left right) = t in
  match onp with
  | None -> return IE_Good
  | Some np -> (
    parent_hash_from_left_ok <-- (
      let real_parent_hash = get_parent_hash left in
      computed_parent_hash <-- compute_parent_hash_from_dir cs np.np_content np.np_parent_hash nb_left_leaves t Left;
      return (real_parent_hash = Some computed_parent_hash)
    );
    parent_hash_from_right_ok <-- (
      match get_original_right_node right with
      | None -> return false
      | Some (|_, _, original_right|) -> (
        let real_parent_hash = get_parent_hash original_right in
        computed_parent_hash <-- compute_parent_hash_from_dir cs np.np_content np.np_parent_hash nb_left_leaves t Right;
        return (real_parent_hash = Some computed_parent_hash)
      )
    );
    if (parent_hash_from_left_ok || parent_hash_from_right_ok) then
      return IE_Good
    else
      return (IE_Errors [IE_NodeError NIE_BadParentHash nb_left_leaves l])
  )
#pop-options

#push-options "--ifuel 1"
val check_treesync_aux: #l:nat -> #n:tree_size l -> ciphersuite -> nat -> treesync l n -> result integrity_either
let rec check_treesync_aux #l #n cs nb_left_leaves t =
  match t with
  | TNode (_, onp) left right ->
    left_ok <-- check_treesync_aux cs nb_left_leaves left;
    right_ok <-- check_treesync_aux cs (nb_left_leaves + pow2 (l-1)) right;
    cur_ok <-- check_internal_node cs nb_left_leaves t;
    return (left_ok &&& cur_ok &&& right_ok)
  | TSkip _ t' ->
    check_treesync_aux cs nb_left_leaves t'
  | TLeaf _ ->
    check_leaf cs nb_left_leaves t
#pop-options

val check_treesync: #l:nat -> #n:tree_size l -> ciphersuite -> treesync l n -> result integrity_either
let check_treesync #l #n cs t =
  check_treesync_aux cs 0 t
