module MLS.NetworkBinder

open FStar.List.Tot
open Comparse
open MLS.NetworkTypes
open MLS.TreeSync.NetworkTypes
open MLS.TreeKEM.NetworkTypes
open MLS.Crypto
open MLS.Result
open MLS.Tree
open MLS.TreeCommon
module TS = MLS.TreeSync.Types
module TK = MLS.TreeKEM.Types

#set-options "--fuel 1 --ifuel 1"

let sparse_update_path (bytes:Type0) {|bytes_like bytes|} = path (leaf_node_nt bytes tkt) (option (update_path_node_nt bytes))

(*** UpdatePath to MLS* ***)


val uncompress_update_path_aux:
  #bytes:Type0 -> {|bytes_like bytes|} ->
  #leaf_t:Type -> #node_t:Type ->
  #l:nat -> #i:tree_index l ->
  li:leaf_index l i -> tree (option leaf_t) (option node_t) l i -> (leaf_node_nt bytes tkt & list (update_path_node_nt bytes)) ->
  result (sparse_update_path bytes l i li)
let rec uncompress_update_path_aux #bytes #bl #leaf_t #node_t #l #i li t (leaf_node, nodes) =
  match t with
  | TLeaf _ -> (
    if not (List.length nodes = 0) then
      error "uncompress_update_path: update_path.nodes is too long"
    else (
      return (PLeaf leaf_node)
    )
  )
  | TNode _ left right -> (
    let (child, sibling) = get_child_sibling t li in
    if is_tree_empty sibling then (
      let? path_next = uncompress_update_path_aux _ child (leaf_node, nodes) in
      return (PNode None path_next)
    ) else (
      if not (List.length nodes > 0) then
        error "uncompress_update_path: update_path.nodes is too short"
      else (
        let (tail_nodes, head_nodes) = List.unsnoc nodes in
        let? path_next = uncompress_update_path_aux _ child (leaf_node, tail_nodes) in
        return (PNode (Some head_nodes) path_next)
      )
    )
  )

val uncompress_update_path:
  #bytes:Type0 -> {|bytes_like bytes|} ->
  #leaf_t:Type -> #node_t:Type ->
  #l:nat -> #i:tree_index l ->
  li:leaf_index l i -> tree (option leaf_t) (option node_t) l i -> update_path_nt bytes ->
  result (sparse_update_path bytes l i li)
let uncompress_update_path #bytes #bl #leaf_t #node_t #l #i li t update_path =
  uncompress_update_path_aux li t (update_path.leaf_node, update_path.nodes)

val update_path_to_treesync:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  #l:nat -> #i:tree_index l -> #li:leaf_index l i ->
  sparse_update_path bytes l i li ->
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
  TK.treekem_leaf bytes
let leaf_node_to_treekem #bytes #cb ln =
  {TK.public_key = ln.data.content;}

val update_path_to_treekem:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  #l:nat -> #i:tree_index l -> #li:leaf_index l i ->
  sparse_update_path bytes l i li ->
  TK.pathkem bytes l i li
let update_path_to_treekem #bytes #cb #l #i #li p =
  set_path_leaf p (leaf_node_to_treekem (get_path_leaf p))

  (*** MLS* to UpdatePath ***)

val compress_update_path_aux:
  #bytes:Type0 -> {|bytes_like bytes|} ->
  #l:nat -> #i:tree_index l -> #li:leaf_index l i ->
  sparse_update_path bytes l i li ->
  (leaf_node_nt bytes tkt & list (update_path_node_nt bytes))
let rec compress_update_path_aux #bytes #bl #l #i #li p =
  match p with
  | PLeaf ln ->
    (ln, [])
  | PNode p_opt_data p_next ->
    let (ln, nodes) = compress_update_path_aux p_next in
    match p_opt_data with
    | None -> (ln, nodes)
    | Some p_data -> (
      (ln, List.Tot.snoc (nodes, p_data))
    )

val compress_update_path:
  #bytes:Type0 -> {|bytes_like bytes|} ->
  #l:nat -> #i:tree_index l -> #li:leaf_index l i ->
  sparse_update_path bytes l i li ->
  result (update_path_nt bytes)
let compress_update_path #bytes #bl #l #i #li p =
  let (leaf_node, nodes) = compress_update_path_aux p in
  let? nodes = mk_mls_list nodes "compress_update_path" "update_path" in
  return {leaf_node; nodes;}

val mls_star_paths_to_update_path:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  #l:nat -> #i:tree_index l -> #li:leaf_index l i ->
  TS.pathsync bytes tkt l i li -> TK.pathkem bytes l i li ->
  (sparse_update_path bytes l i li)
let mls_star_paths_to_update_path #bytes #cb #l #i #li psync pkem =
  set_path_leaf pkem (get_path_leaf psync)

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

#push-options "--ifuel 0 --fuel 0"
val ratchet_tree_to_treesync:
  #bytes:Type0 -> {|bytes_like bytes|} -> #tkt:treekem_types bytes ->
  ratchet_tree_nt bytes tkt ->
  result (l:nat & TS.treesync bytes tkt l 0)
let ratchet_tree_to_treesync #bytes #bl #tkt nodes =
  let? (|new_nodes, l|) = ratchet_tree_l nodes in
  let? res = ratchet_tree_to_treesync_aux l 0 new_nodes in
  return #((l:nat & TS.treesync bytes tkt l 0)) (|l, res|)
#pop-options

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
  | Some res -> mk_mls_list res "shrink_ratchet_tree" "ratchet_tree"

val treesync_to_ratchet_tree:
  #bytes:Type0 -> {|bytes_like bytes|} -> #tkt:treekem_types bytes ->
  #l:nat -> #i:tree_index l ->
  TS.treesync bytes tkt l i ->
  result (ratchet_tree_nt bytes tkt)
let treesync_to_ratchet_tree #bytes #bl #tkt #l #i t =
  let? pre_ratchet_tree = treesync_to_ratchet_tree_aux t in
  shrink_ratchet_tree pre_ratchet_tree
