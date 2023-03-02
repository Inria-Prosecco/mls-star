module MLS.NetworkBinder

open FStar.List.Tot
open Comparse
open MLS.NetworkTypes
open MLS.TreeSync.NetworkTypes
open MLS.TreeKEM.NetworkTypes
open MLS.Crypto
open MLS.Result
open MLS.Tree
open MLS.MiscLemmas
module TS = MLS.TreeSync.Types
module TK = MLS.TreeKEM.Types

#set-options "--fuel 1 --ifuel 1"

let sparse_update_path (bytes:Type0) {|bytes_like bytes|} = path (leaf_node_nt bytes tkt) (option (update_path_node_nt bytes))

(*** UpdatePath to MLS* ***)

val tree_resolution_empty:
  #leaf_t:Type -> #node_t:Type ->
  #l:nat -> #i:tree_index l ->
  tree (option leaf_t) (option node_t) l i ->
  bool
let rec tree_resolution_empty #leaf_t #node_t #l #i t =
  match t with
  | TLeaf None -> true
  | TLeaf (Some _) -> false
  | TNode None left right ->
    tree_resolution_empty left && tree_resolution_empty right
  | TNode (Some _) _ _ -> false

val uncompress_update_path:
  #bytes:Type0 -> {|bytes_like bytes|} ->
  #leaf_t:Type -> #node_t:Type ->
  #l:nat -> #i:tree_index l ->
  li:leaf_index l i -> tree (option leaf_t) (option node_t) l i -> update_path_nt bytes ->
  result (sparse_update_path bytes l i li)
let rec uncompress_update_path #bytes #bl #leaf_t #node_t #l #i li t update_path =
  match t with
  | TLeaf _ -> (
    if not (List.length update_path.nodes = 0) then
      error "uncompress_update_path: update_path.nodes is too long"
    else (
      return (PLeaf update_path.leaf_node)
    )
  )
  | TNode _ left right -> (
    let (child, sibling) = get_child_sibling t li in
    if tree_resolution_empty sibling then (
      let? path_next = uncompress_update_path _ child update_path in
      return (PNode None path_next)
    ) else (
      if not (List.length update_path.nodes > 0) then
        error "uncompress_update_path: update_path.nodes is too short"
      else (
        let update_path_length = (List.length update_path.nodes) in
        let (tail_update_path_nodes, head_update_path_nodes) = List.unsnoc update_path.nodes in
        bytes_length_unsnoc ps_update_path_node_nt update_path.nodes;
        let next_update_path = { update_path with nodes = tail_update_path_nodes } in
        let? path_next = uncompress_update_path _ child next_update_path in
        return (PNode (Some head_update_path_nodes) path_next)
      )
    )
  )

val update_path_to_treesync:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  #l:nat -> #i:tree_index l -> #li:leaf_index l i ->
  update_path:sparse_update_path bytes l i li ->
  TS.pathsync bytes tkt l i li
let rec update_path_to_treesync #bytes #cb #l #i #li p =
  match p with
  | PLeaf ln -> PLeaf ln
  | PNode onp p_next -> (
    let path_next = update_path_to_treesync p_next in
    let path_data =
      match onp with
      | Some np -> Some np.encryption_key
      | None -> None
    in
    PNode path_data path_next
  )

val leaf_node_to_treekem:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  leaf_node_nt bytes tkt ->
  result (TK.member_info bytes)
let leaf_node_to_treekem #bytes #cb ln =
  if not (length (ln.data.content <: bytes) = hpke_public_key_length #bytes) then
    error "leaf_node_to_treekem: public key has wrong length"
  else
    return ({
      TK.public_key = ln.data.content;
    } <: TK.member_info bytes)

val update_path_node_to_treekem:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  bytes -> TK.direction -> update_path_node_nt bytes ->
  result (TK.key_package bytes)
let update_path_node_to_treekem #bytes #cb group_context dir update_path_node =
  if not (length (update_path_node.encryption_key <: bytes) = hpke_public_key_length #bytes) then
    error "update_path_node_to_treekem: public key has wrong length"
  else (
    let? path_secret_ciphertext = mapM (fun (hpke_ciphertext: hpke_ciphertext_nt bytes) ->
      if not (length (hpke_ciphertext.kem_output <: bytes) = hpke_kem_output_length #bytes) then
        error "update_path_node_to_treekem: kem output has wrong length"
      else
        return ({
          TK.kem_output = hpke_ciphertext.kem_output;
          TK.ciphertext = hpke_ciphertext.ciphertext;
        } <: TK.path_secret_ciphertext bytes)
    ) update_path_node.encrypted_path_secret in
    return ({
      TK.public_key = update_path_node.encryption_key;
      TK.last_group_context = group_context;
      TK.unmerged_leaves = [];
      TK.path_secret_from = dir;
      TK.path_secret_ciphertext = path_secret_ciphertext;
    })
  )

val update_path_to_treekem:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  #l:nat -> #i:tree_index l -> #li:leaf_index l i ->
  bytes -> update_path:sparse_update_path bytes l i li ->
  result (TK.pathkem bytes l i li)
let rec update_path_to_treekem #bytes #cb #l #i #li group_context p =
  match p with
  | PLeaf ln -> (
    let? leaf_package = leaf_node_to_treekem ln in
    return (PLeaf leaf_package)
  )
  | PNode onp p_next -> (
    let dir = if is_left_leaf li then TK.Left else TK.Right in
    let? path_next = update_path_to_treekem group_context p_next in
    let? path_data = (
      match onp with
      | Some np -> (
        let? res = update_path_node_to_treekem group_context dir np in
        return (Some res)
      )
      | None -> return None
    ) in
    return (PNode path_data path_next)
  )

(*** MLS* to UpdatePath ***)

val compress_update_path:
  #bytes:Type0 -> {|bytes_like bytes|} ->
  #leaf_t:Type -> #node_t:Type ->
  #l:nat -> #i:tree_index l -> #li:leaf_index l i ->
  (tree (option leaf_t) (option node_t) l i) -> sparse_update_path bytes l i li ->
  result (update_path_nt bytes)
let rec compress_update_path #bytes #bl #leaf_t #node_t #l #i #li t update_path =
  match update_path with
  | PLeaf ln ->
    return ({leaf_node = ln; nodes = []})
  | PNode p_opt_data p_next ->
    let (child, sibling) = get_child_sibling t li in
    if tree_resolution_empty sibling then (
      compress_update_path child p_next
    ) else (
      let? compressed_p_next = compress_update_path child p_next in
      match p_opt_data with
      | None -> return compressed_p_next
      | Some p_data -> (
        let new_nodes = List.Tot.snoc (compressed_p_next.nodes, p_data) in
        if not (bytes_length ps_update_path_node_nt new_nodes < pow2 30) then
          error "compress_update_path: update path too long!"
        else
          return ({ compressed_p_next with nodes = new_nodes; })
      )
    )

val encrypted_path_secret_tk_to_nt:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  TK.path_secret_ciphertext bytes ->
  result (hpke_ciphertext_nt bytes)
let encrypted_path_secret_tk_to_nt #bytes #cb x =
  if not (length (x.kem_output <: bytes) < pow2 30) then
    internal_failure "encrypted_path_secret_tk_to_nt: kem_output too long"
  else if not (length (x.ciphertext <: bytes) < pow2 30) then
    internal_failure "encrypted_path_secret_tk_to_nt: ciphertext too long"
  else
    return ({
      kem_output = x.kem_output;
      ciphertext = x.ciphertext;
    } <: hpke_ciphertext_nt bytes)

val treekem_to_update_path_node:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  TK.key_package bytes ->
  result (update_path_node_nt bytes)
let treekem_to_update_path_node #bytes #cb kp =
  let? encrypted_path_secret = mapM encrypted_path_secret_tk_to_nt kp.path_secret_ciphertext in
  if not (bytes_length ps_hpke_ciphertext_nt encrypted_path_secret < pow2 30) then
    error "treekem_to_update_path_node: encrypted_path_secret too long"
  else (
    return ({
      encryption_key = kp.public_key;
      encrypted_path_secret;
    } <: update_path_node_nt bytes)
  )

val mls_star_paths_to_update_path:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  #l:nat -> #i:tree_index l -> #li:leaf_index l i ->
  TS.pathsync bytes tkt l i li -> TK.pathkem bytes l i li ->
  result (sparse_update_path bytes l i li)
let rec mls_star_paths_to_update_path #bytes #cb #l #i #li psync pkem =
  match psync, pkem with
  | PLeaf lp, PLeaf _ -> return (PLeaf lp)
  | PNode _ psync_next, PNode onp pkem_next ->
    let? res_next = mls_star_paths_to_update_path psync_next pkem_next in
    let? opt_upn = (
      match onp with
      | None -> return None
      | Some np -> (
        let? upn = treekem_to_update_path_node np in
        return (Some upn)
      )
    ) in
    return (PNode opt_upn res_next)

(*** ratchet_tree extension (13.4.3.3) ***)

val ratchet_tree_l:
  #bytes:Type0 -> {|bytes_like bytes|} -> #tkt:treekem_types bytes ->
  nodes:ratchet_tree_nt bytes tkt ->
  result (new_nodes:list (option (node_nt bytes tkt)) & l:nat{List.length new_nodes == (pow2 (l+1))-1})
let ratchet_tree_l #bytes #bl #tkt nodes =
  let n_nodes = List.length nodes in
  if n_nodes%2 = 0 then
    error "ratchet_tree_l: length must be odd"
  else
    let n = (n_nodes+1)/2 in
    let l = (TreeMath.Internal.log2 n) in
    if n_nodes = (pow2 (l+1))-1 then
      return (|nodes, l|)
    else
      let new_nodes = nodes @ (FStar.Seq.seq_to_list (Seq.create ((pow2 (l+2))-1-n_nodes) None)) in
      return (|new_nodes, l+1|)

#push-options "--ifuel 1 --fuel 2"
val ratchet_tree_to_treesync_aux:
  #bytes:Type0 -> {|bytes_like bytes|} -> #tkt:treekem_types bytes ->
  l:nat -> i:tree_index l -> nodes:list (option (node_nt bytes tkt)){List.length nodes = (pow2 (l+1)-1)} ->
  result (TS.treesync bytes tkt l i)
let rec ratchet_tree_to_treesync_aux #bytes #bl #tkt l i nodes =
  if l = 0 then (
    assert(List.length nodes = 1);
    match nodes with
    | [Some (N_leaf kp)] ->
      return (TLeaf (Some kp))
    | [Some _] -> error "ratchet_tree_to_treesync_aux: node must be a leaf!"
    | [None] ->
      return (TLeaf None)
  ) else (
    let (left_nodes, my_node, right_nodes) = List.Tot.split3 nodes ((pow2 l) - 1) in
    List.Pure.lemma_split3_length nodes ((pow2 l) - 1);
    let? left_res = ratchet_tree_to_treesync_aux (l-1) _ left_nodes in
    let? right_res = ratchet_tree_to_treesync_aux (l-1) _ right_nodes in
    match my_node with
    | Some (N_parent pn) ->
      return (TNode (Some pn) left_res right_res)
    | Some _ -> error "ratchet_tree_to_treesync_aux: node must be a parent!"
    | None ->
      return (TNode None left_res right_res)
  )
#pop-options

val ratchet_tree_to_treesync:
  #bytes:Type0 -> {|bytes_like bytes|} -> #tkt:treekem_types bytes ->
  ratchet_tree_nt bytes tkt ->
  result (l:nat & TS.treesync bytes tkt l 0)
let ratchet_tree_to_treesync #bytes #bl #tkt nodes =
  let? (|new_nodes, l|) = ratchet_tree_l nodes in
  let? res = ratchet_tree_to_treesync_aux l 0 new_nodes in
  return #((l:nat & TS.treesync bytes tkt l 0)) (|l, res|)

val treesync_to_ratchet_tree_aux:
  #bytes:Type0 -> {|bytes_like bytes|} -> #tkt:treekem_types bytes ->
  #l:nat -> #i:tree_index l ->
  TS.treesync bytes tkt l i ->
  result (list (option (node_nt bytes tkt)))
let rec treesync_to_ratchet_tree_aux #bytes #bl #tkt #l #i t =
  match t with
  | TLeaf None ->
    return [None]
  | TLeaf (Some lp) ->
    return [Some (N_leaf lp)]
  | TNode onp left right ->
    let? parent_node = (
      match onp with
      | None -> return None
      | Some np ->
        return (Some (N_parent np))
    ) in
    let? left_ratchet = treesync_to_ratchet_tree_aux left in
    let? right_ratchet = treesync_to_ratchet_tree_aux right in
    return (left_ratchet @ [parent_node] @ right_ratchet)

val shrink_ratchet_tree_aux:
  #bytes:Type0 -> {|bytes_like bytes|} -> #tkt:treekem_types bytes ->
  list (option (node_nt bytes tkt)) ->
  option (list (option (node_nt bytes tkt)))
let rec shrink_ratchet_tree_aux #bytes #bl #tkt l =
  match l with
  | [] -> None
  | opt_h::t -> (
    let opt_shrinked_t = shrink_ratchet_tree_aux t in
    match opt_h, opt_shrinked_t with
    | None, None -> None
    | Some _, None -> Some ([opt_h])
    | _, Some shrinked_t -> Some (opt_h::shrinked_t)
  )

val shrink_ratchet_tree:
  #bytes:Type0 -> {|bytes_like bytes|} -> #tkt:treekem_types bytes ->
  list (option (node_nt bytes tkt)) ->
  result (ratchet_tree_nt bytes tkt)
let shrink_ratchet_tree #bytes #bl #tkt l =
  match shrink_ratchet_tree_aux l with
  | None -> return []
  | Some res -> (
    if not (bytes_length (ps_option (ps_node_nt tkt)) res < pow2 30) then
      internal_failure "shrink_ratchet_tree: ratchet_tree too long"
    else
      return res
  )

val treesync_to_ratchet_tree:
  #bytes:Type0 -> {|bytes_like bytes|} -> #tkt:treekem_types bytes ->
  #l:nat -> #i:tree_index l ->
  TS.treesync bytes tkt l i ->
  result (ratchet_tree_nt bytes tkt)
let treesync_to_ratchet_tree #bytes #bl #tkt #l #i t =
  let? pre_ratchet_tree = treesync_to_ratchet_tree_aux t in
  shrink_ratchet_tree pre_ratchet_tree
