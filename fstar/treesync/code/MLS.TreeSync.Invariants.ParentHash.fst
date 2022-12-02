module MLS.TreeSync.Invariants.ParentHash

open Comparse
open MLS.Crypto
open MLS.NetworkTypes
open MLS.TreeSync.NetworkTypes
open MLS.Tree
open MLS.Tree.Lemmas
open MLS.TreeSync.ParentHash
open MLS.TreeSync.Types
open MLS.TreeSync.Operations

#set-options "--fuel 1 --ifuel 1"

val node_not_blank: #bytes:Type0 -> {|bytes_like bytes|} -> #tkt:treekem_types bytes -> #l:nat -> #i:tree_index l -> treesync bytes tkt l i -> bool
let node_not_blank #bytes #bl #tkt #l #i t =
  match t with
  | TLeaf (Some _) -> true
  | TNode (Some _) _ _ -> true
  | _ -> false

val node_has_parent_hash: #bytes:Type0 -> {|bytes_like bytes|} -> #tkt:treekem_types bytes -> #l:nat -> #i:tree_index l -> treesync bytes tkt l i -> bool
let node_has_parent_hash #bytes #bl #tkt #l #i t =
  match t with
  | TLeaf (Some ln) -> ln.data.source = LNS_commit
  | TNode (Some _) _ _ -> true
  | _ -> false

val get_parent_hash_of: #bytes:Type0 -> {|bytes_like bytes|} -> #tkt:treekem_types bytes -> #l:nat -> #i:tree_index l -> t:treesync bytes tkt l i{node_has_parent_hash t} -> mls_bytes bytes
let get_parent_hash_of #bytes #bl #tkt #l #i t =
  match t with
  | TLeaf (Some content) -> content.data.parent_hash
  | TNode (Some content) _ _ -> content.parent_hash

val max: int -> int -> int
let max x y =
  if x < y then y else x

val last_commit_epoch:
  #bytes:Type0 -> {|bytes_like bytes|} -> #tkt:treekem_types bytes ->
  #l:nat -> #i:tree_index l ->
  t:treesync bytes tkt l i -> nat_lbytes 8
let rec last_commit_epoch #bytes #bl #tkt #l #i t =
  match t with
  | TLeaf None -> 0
  | TLeaf (Some ln) -> (
    match ln.data.source with
    | LNS_commit -> ln.data.commit_epoch
    | _ -> 0
  )
  | TNode _ left right ->
    max (last_commit_epoch left) (last_commit_epoch right)

val parent_hash_correct:
  #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes ->
  #ld:nat -> #lp:nat{ld < lp} -> #id:tree_index ld -> #ip:tree_index lp{leaf_index_inside lp ip id} ->
  d:treesync bytes tkt ld id{node_has_parent_hash d} -> p:treesync bytes tkt lp ip{node_not_blank p} ->
  bool
let parent_hash_correct #bytes #cb #tkt #ld #lp #id #ip d p =
  let p_content = (Some?.v (TNode?.data p)) in
  let expected_parent_hash = get_parent_hash_of d in
  let (_, sibling) = get_child_sibling p id in
  let original_sibling = un_add sibling (last_commit_epoch p) in
  compute_parent_hash_pre p_content.content (length #bytes p_content.parent_hash) original_sibling &&
  expected_parent_hash = compute_parent_hash p_content.content p_content.parent_hash original_sibling

val last_update_correct:
  #bytes:Type0 -> {|bytes_like bytes|} -> #tkt:treekem_types bytes ->
  #ld:nat -> #lp:nat{ld < lp} -> #id:tree_index ld -> #ip:tree_index lp{leaf_index_inside lp ip id} ->
  d:treesync bytes tkt ld id -> p:treesync bytes tkt lp ip ->
  bool
let last_update_correct #bytes #bl #tkt #ld #lp #id #ip d p =
  last_commit_epoch d = last_commit_epoch p

val mem_flipped: #a:eqtype -> list a -> a -> bool
let mem_flipped #a l x =
  List.Tot.mem x l

val set_subset: #a:eqtype -> list a -> list a -> bool
let set_subset #a l1 l2 =
  List.Tot.for_all (mem_flipped l2) l1

val unmerged_leaves_aux:
  #bytes:Type0 -> {|bytes_like bytes|} -> #tkt:treekem_types bytes ->
  #l:nat -> #i:tree_index l ->
  epoch:nat -> t:treesync bytes tkt l i ->
  list nat
let rec unmerged_leaves_aux #bytes #bl #tkt #l #i epoch t =
  match t with
  | TLeaf None -> []
  | TLeaf oln ->
    if is_unmerged_leaf epoch oln then
      [i]
    else
      []
  | TNode _ left right ->
    unmerged_leaves_aux epoch left @ unmerged_leaves_aux epoch right

val unmerged_leaves:
  #bytes:Type0 -> {|bytes_like bytes|} -> #tkt:treekem_types bytes ->
  #l:nat -> #i:tree_index l ->
  t:treesync bytes tkt l i ->
  list nat
let unmerged_leaves #bytes #bl #tkt #l #i t =
  unmerged_leaves_aux (last_commit_epoch t) t

type node_index = dtuple2 nat tree_index

val nat_to_node_index: nat -> node_index
let nat_to_node_index n = (|0, n|)

val unmerged_resolution: list nat -> list node_index
let unmerged_resolution l =
  List.Tot.map nat_to_node_index l

val resolution:
  #bytes:Type0 -> {|bytes_like bytes|} -> #tkt:treekem_types bytes ->
  #l:nat -> #i:tree_index l ->
  treesync bytes tkt l i ->
  list node_index
let rec resolution #bytes #bl #tkt #l #i t =
  match t with
  | TLeaf None -> []
  | TLeaf (Some _) -> assert(l == 0); [(|l, i|)]
  | TNode None left right ->
    resolution left @ resolution right
  | TNode (Some content) _ _ ->
    (|l, i|)::(unmerged_resolution (unmerged_leaves t))

val filter_lhs: #bytes:Type0 -> {|bytes_like bytes|} -> #tkt:treekem_types bytes -> #ld:nat -> #lp:nat{ld < lp} -> #id:tree_index ld -> #ip:tree_index lp{leaf_index_inside lp ip id} -> d:treesync bytes tkt ld id -> p:treesync bytes tkt lp ip{node_not_blank p} -> list node_index
let filter_lhs #bytes #bl #tkt #ld #lp #id #ip d p =
  let (c, _) = get_child_sibling p id in
  (resolution c)

val filter_rhs: #bytes:Type0 -> {|bytes_like bytes|} -> #tkt:treekem_types bytes -> #ld:nat -> #lp:nat{ld < lp} -> #id:tree_index ld -> #ip:tree_index lp{leaf_index_inside lp ip id} -> d:treesync bytes tkt ld id -> p:treesync bytes tkt lp ip{node_not_blank p} -> list node_index
let filter_rhs #bytes #bl #tkt #ld #lp #id #ip d p =
  (|ld, id|)::(unmerged_resolution (unmerged_leaves p))

val filter_d_in_res_c: #bytes:Type0 -> {|bytes_like bytes|} -> #tkt:treekem_types bytes -> #ld:nat -> #lp:nat{ld < lp} -> #id:tree_index ld -> #ip:tree_index lp{leaf_index_inside lp ip id} -> d:treesync bytes tkt ld id -> p:treesync bytes tkt lp ip{node_not_blank p} -> bool
let filter_d_in_res_c #bytes #bl #tkt #ld #lp #id #ip d p =
  let (c, _) = get_child_sibling p id in
  List.Tot.mem (|ld, id|) (resolution c)

val filter_correct: #bytes:Type0 -> {|bytes_like bytes|} -> #tkt:treekem_types bytes -> #ld:nat -> #lp:nat{ld < lp} -> #id:tree_index ld -> #ip:tree_index lp{leaf_index_inside lp ip id} -> d:treesync bytes tkt ld id -> p:treesync bytes tkt lp ip{node_not_blank p} -> bool
let filter_correct #bytes #bl #tkt #ld #lp #id #ip d p =
  filter_d_in_res_c d p && set_subset (filter_lhs d p) (filter_rhs d p)

val parent_hash_linked: #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes -> #ld:nat -> #lp:nat{ld < lp} -> #id:tree_index ld -> #ip:tree_index lp{leaf_index_inside lp ip id} -> d:treesync bytes tkt ld id{node_has_parent_hash d} -> p:treesync bytes tkt lp ip{node_not_blank p} -> bool
let parent_hash_linked #bytes #cb #tkt #ld #lp #id #ip d p =
  parent_hash_correct d p && last_update_correct d p && filter_correct d p

val node_has_parent_hash_link_aux: #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes -> #ld:nat -> #lp:nat{ld < lp} -> #id:tree_index ld -> #ip:tree_index lp{leaf_index_inside lp ip id} -> d:treesync bytes tkt ld id -> p:treesync bytes tkt lp ip{node_not_blank p} -> bool
let rec node_has_parent_hash_link_aux #bytes #cb #tkt #ld #lp #id #ip d p =
  match d with
  | TLeaf None -> false
  | TLeaf (Some lp) -> (
    match lp.data.source with
    | LNS_commit -> parent_hash_linked d p
    | _ -> false
  )
  | TNode (Some kp) _ _ ->
    parent_hash_linked d p
  | TNode None left right -> (
    node_has_parent_hash_link_aux left p || node_has_parent_hash_link_aux right p
  )

val node_has_parent_hash_link: #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes -> #lp:pos -> #ip:tree_index lp -> p:treesync bytes tkt lp ip{node_not_blank p} -> bool
let node_has_parent_hash_link #bytes #cb #tkt #lp #ip p =
  match p with
  | TNode (Some _) left right ->
    node_has_parent_hash_link_aux left p || node_has_parent_hash_link_aux right p

val parent_hash_invariant: #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes -> #lp:nat -> #ip:tree_index lp -> t:treesync bytes tkt lp ip -> bool
let rec parent_hash_invariant #bytes #cb #tkt #lp #ip t =
  match t with
  | TLeaf _ -> true
  | TNode opn left right ->
    parent_hash_invariant left &&
    parent_hash_invariant right && (
      match opn with
      | None -> true
      | Some _ -> node_has_parent_hash_link t
    )
