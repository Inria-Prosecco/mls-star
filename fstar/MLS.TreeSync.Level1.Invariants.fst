module MLS.TreeSync.Level1.Invariants

open Comparse
open MLS.Crypto
open MLS.NetworkTypes
open MLS.TreeSync.NetworkTypes
open MLS.Tree
open MLS.Tree.Lemmas
open MLS.TreeSync.ParentHash
open MLS.TreeSync.Level1.Types
open MLS.TreeSync.Level1

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
  | TLeaf (Some ln) -> ln.data.source = LNS_commit ()
  | TNode (Some _) _ _ -> true
  | _ -> false

val get_parent_hash_of: #bytes:Type0 -> {|bytes_like bytes|} -> #tkt:treekem_types bytes -> #l:nat -> #i:tree_index l -> t:treesync bytes tkt l i{node_has_parent_hash t} -> mls_bytes bytes
let get_parent_hash_of #bytes #bl #tkt #l #i t =
  match t with
  | TLeaf (Some content) -> content.data.parent_hash
  | TNode (Some content) _ _ -> content.parent_hash

val mem_ul: x:nat -> l:list (nat_lbytes 4) -> bool
let rec mem_ul x l =
  match l with
  | [] -> false
  | h::t -> x=h || mem_ul x t

val un_add_unmerged_leaf: list (nat_lbytes 4) -> nat -> bool
let un_add_unmerged_leaf leaves i =
  not (mem_ul i leaves)

val un_add: #bytes:Type0 -> {|bytes_like bytes|} -> #tkt:treekem_types bytes -> #l:nat -> #i:tree_index l -> treesync bytes tkt l i -> list (nat_lbytes 4) -> treesync bytes tkt l i
let un_add #bytes #bl #tkt #l #i t leaves =
  un_addP t (un_add_unmerged_leaf leaves)

val parent_hash_correct: #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes -> #lu:nat -> #lp:nat{lu < lp} -> #iu:tree_index lu -> #ip:tree_index lp{leaf_index_inside lp ip iu} -> u:treesync bytes tkt lu iu{node_has_parent_hash u} -> p:treesync bytes tkt lp ip{node_not_blank p} -> bool
let parent_hash_correct #bytes #cb #tkt #lu #lp #iu #ip u p =
  let p_content = (Some?.v (TNode?.data p)) in
  let expected_parent_hash = get_parent_hash_of u in
  let (_, sibling) = get_child_sibling p iu in
  let original_sibling = un_add sibling p_content.unmerged_leaves in
  compute_parent_hash_pre p_content.content (length #bytes p_content.parent_hash) original_sibling &&
  expected_parent_hash = compute_parent_hash p_content.content p_content.parent_hash original_sibling

val set_equal_mem: #a:eqtype -> list a -> a -> bool
let set_equal_mem #a l x =
  List.Tot.mem x l

val set_eq: #a:eqtype -> list a -> list a -> bool
let set_eq #a l1 l2 =
  List.Tot.for_all (set_equal_mem l1) l2 && List.Tot.for_all (set_equal_mem l2) l1

type node_index = dtuple2 nat tree_index

val nat_to_node_index: nat -> node_index
let nat_to_node_index n = (|0, n|)

val unmerged_resolution: list (nat_lbytes 4) -> list node_index
let unmerged_resolution l =
  List.Tot.map nat_to_node_index l

val resolution: #bytes:Type0 -> {|bytes_like bytes|} -> #tkt:treekem_types bytes -> #l:nat -> #i:tree_index l -> treesync bytes tkt l i -> list node_index
let rec resolution #bytes #bl #tkt #l #i t =
  match t with
  | TLeaf None -> []
  | TLeaf (Some _) -> assert(l == 0); [(|l, i|)]
  | TNode None left right ->
    resolution left @ resolution right
  | TNode (Some content) _ _ -> (|l, i|)::(unmerged_resolution content.unmerged_leaves)

val last_update_lhs: #bytes:Type0 -> {|bytes_like bytes|} -> #tkt:treekem_types bytes -> #lu:nat -> #lp:nat{lu < lp} -> #iu:tree_index lu -> #ip:tree_index lp{leaf_index_inside lp ip iu} -> u:treesync bytes tkt lu iu -> p:treesync bytes tkt lp ip{node_not_blank p} -> list node_index
let last_update_lhs #bytes #bl #tkt #lu #lp #iu #ip u p =
  let (c, _) = get_child_sibling p iu in
  List.Tot.filter (op_disEquality (|lu, iu|)) (resolution c)

val last_update_rhs: #bytes:Type0 -> {|bytes_like bytes|} -> #tkt:treekem_types bytes -> #lu:nat -> #lp:nat{lu < lp} -> #iu:tree_index lu -> #ip:tree_index lp{leaf_index_inside lp ip iu} -> u:treesync bytes tkt lu iu -> p:treesync bytes tkt lp ip{node_not_blank p} -> list node_index
let last_update_rhs #bytes #bl #tkt #lu #lp #iu #ip u p =
  let (c, _) = get_child_sibling p iu in
  let p_unmerged_leaves = (Some?.v (TNode?.data p)).unmerged_leaves in
  unmerged_resolution (List.Tot.filter (leaf_index_inside_tree c) p_unmerged_leaves)

val last_update_u_in_res_c: #bytes:Type0 -> {|bytes_like bytes|} -> #tkt:treekem_types bytes -> #lu:nat -> #lp:nat{lu < lp} -> #iu:tree_index lu -> #ip:tree_index lp{leaf_index_inside lp ip iu} -> u:treesync bytes tkt lu iu -> p:treesync bytes tkt lp ip{node_not_blank p} -> bool
let last_update_u_in_res_c #bytes #bl #tkt #lu #lp #iu #ip u p =
  let (c, _) = get_child_sibling p iu in
  List.Tot.mem (|lu, iu|) (resolution c)

val last_update_correct: #bytes:Type0 -> {|bytes_like bytes|} -> #tkt:treekem_types bytes -> #lu:nat -> #lp:nat{lu < lp} -> #iu:tree_index lu -> #ip:tree_index lp{leaf_index_inside lp ip iu} -> u:treesync bytes tkt lu iu -> p:treesync bytes tkt lp ip{node_not_blank p} -> bool
let last_update_correct #bytes #bl #tkt #lu #lp #iu #ip u p =
  last_update_u_in_res_c u p && set_eq (last_update_lhs u p) (last_update_rhs u p)

val parent_hash_linked: #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes -> #lu:nat -> #lp:nat{lu < lp} -> #iu:tree_index lu -> #ip:tree_index lp{leaf_index_inside lp ip iu} -> u:treesync bytes tkt lu iu{node_has_parent_hash u} -> p:treesync bytes tkt lp ip{node_not_blank p} -> bool
let parent_hash_linked #bytes #cb #tkt #lu #lp #iu #ip u p =
  parent_hash_correct u p && last_update_correct u p

val node_has_parent_hash_link_aux: #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes -> #lu:nat -> #lp:nat{lu < lp} -> #iu:tree_index lu -> #ip:tree_index lp{leaf_index_inside lp ip iu} -> u:treesync bytes tkt lu iu -> p:treesync bytes tkt lp ip{node_not_blank p} -> bool
let rec node_has_parent_hash_link_aux #bytes #cb #tkt #lu #lp #iu #ip u p =
  match u with
  | TLeaf None -> false
  | TLeaf (Some lp) -> (
    match lp.data.source with
    | LNS_commit () -> parent_hash_linked u p
    | _ -> false
  )
  | TNode (Some kp) _ _ ->
    parent_hash_linked u p
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
