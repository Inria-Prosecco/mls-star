module MLS.TreeSync.Symbolic.IsWellFormed

open FStar.List.Tot { for_allP, for_allP_eq }
open Comparse
open MLS.Crypto
open MLS.Tree
open MLS.TreeCommon
open MLS.NetworkTypes
open MLS.TreeSync.NetworkTypes
open MLS.TreeSync.Types
open MLS.TreeCommon
open MLS.TreeSync.Operations
open MLS.TreeSync.TreeHash
open MLS.TreeSync.ParentHash
open MLS.TreeSync.Symbolic.Parsers
open MLS.Result

#set-options "--fuel 1 --ifuel 1"

(*** Definitions ***)

[@"opaque_to_smt"]
val pre_is_hash_compatible:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  pre:(bytes -> prop) ->
  prop
let pre_is_hash_compatible #bytes #cb pre =
  forall b. (pre b /\ Success? (hash_hash b)) ==> pre (Success?.v (hash_hash b))

(*** Invariant proofs ***)

val is_well_formed_tree_change_path:
  #bytes:Type0 -> {|bytes_like bytes|} ->
  pre:bytes_compatible_pre bytes ->
  #tkt:treekem_types bytes -> #l:nat -> #i:tree_index l ->
  t:treesync bytes tkt l i -> li:leaf_index l i -> oln:option (leaf_node_nt bytes tkt) ->
  Lemma
  (requires
    is_well_formed _ pre t /\
    (match oln with | None -> True | Some ln -> is_well_formed _ pre ln)
  )
  (ensures is_well_formed _ pre (tree_change_path t li oln None))
let rec is_well_formed_tree_change_path #bytes #bl pre #tkt #l #i t li oln =
  match t with
  | TLeaf _ -> ()
  | TNode _ left right ->
    if is_left_leaf li
    then is_well_formed_tree_change_path pre left li oln
    else is_well_formed_tree_change_path pre right li oln

val is_well_formed_tree_update:
  #bytes:Type0 -> {|bytes_like bytes|} ->
  pre:bytes_compatible_pre bytes ->
  #tkt:treekem_types bytes -> #l:nat -> #i:tree_index l ->
  t:treesync bytes tkt l i -> li:leaf_index l i -> ln:leaf_node_nt bytes tkt ->
  Lemma
  (requires is_well_formed _ pre t /\ is_well_formed _ pre ln)
  (ensures is_well_formed _ pre (tree_update t li ln))
let is_well_formed_tree_update #bytes #bl pre #tkt #l #i t li ln =
  is_well_formed_tree_change_path pre t li (Some ln)

val is_well_formed_tree_remove:
  #bytes:Type0 -> {|bytes_like bytes|} ->
  pre:bytes_compatible_pre bytes ->
  #tkt:treekem_types bytes -> #l:nat -> #i:tree_index l ->
  t:treesync bytes tkt l i -> li:leaf_index l i ->
  Lemma
  (requires is_well_formed _ pre t)
  (ensures is_well_formed _ pre (tree_remove t li))
let is_well_formed_tree_remove #bytes #bl pre #tkt #l #i t li =
  is_well_formed_tree_change_path pre t li None

val is_well_formed_mk_blank_tree:
  #bytes:Type0 -> {|bytes_like bytes|} ->
  pre:bytes_compatible_pre bytes ->
  #tkt:treekem_types bytes ->
  l:nat -> i:tree_index l ->
  Lemma
  (is_well_formed _ pre (mk_blank_tree l i <: treesync bytes tkt l i))
let rec is_well_formed_mk_blank_tree #bytes #bl pre #tkt l i =
  if l = 0 then ()
  else (
    is_well_formed_mk_blank_tree #bytes #_ pre #tkt (l-1) (left_index #l i);
    is_well_formed_mk_blank_tree #bytes #_ pre #tkt (l-1) (right_index #l i)
  )

val is_well_formed_tree_extend:
  #bytes:Type0 -> {|bytes_like bytes|} ->
  pre:bytes_compatible_pre bytes ->
  #tkt:treekem_types bytes -> #l:nat ->
  t:treesync bytes tkt l 0 ->
  Lemma
  (requires is_well_formed _ pre t)
  (ensures is_well_formed _ pre (tree_extend t))
let is_well_formed_tree_extend #bytes #bl pre #tkt #l t =
  is_well_formed_mk_blank_tree #bytes #bl pre #tkt l (right_index #(l+1) 0)

val is_well_formed_tree_truncate:
  #bytes:Type0 -> {|bytes_like bytes|} ->
  pre:bytes_compatible_pre bytes ->
  #tkt:treekem_types bytes -> #l:pos ->
  t:treesync bytes tkt l 0 ->
  Lemma
  (requires is_well_formed _ pre t /\ is_tree_empty (TNode?.right t))
  (ensures is_well_formed _ pre (tree_truncate t))
let is_well_formed_tree_truncate #bytes #bl pre #tkt #l t = ()

#push-options "--z3rlimit 25"
val is_well_formed_tree_add:
  #bytes:Type0 -> {|bytes_like bytes|} ->
  pre:bytes_compatible_pre bytes ->
  #tkt:treekem_types bytes -> #l:nat -> #i:tree_index l ->
  t:treesync bytes tkt l i -> li:leaf_index l i -> ln:leaf_node_nt bytes tkt ->
  Lemma
  (requires
    is_well_formed _ pre t /\
    is_well_formed _ pre ln /\
    Success? (tree_add t li ln)
  )
  (ensures is_well_formed _ pre (Success?.v (tree_add t li ln)))
let rec is_well_formed_tree_add #bytes #bl pre #tkt #l #i t li ln =
  match t with
  | TLeaf _ -> ()
  | TNode opn _ _ ->
    let (child, _) = get_child_sibling t li in
    is_well_formed_tree_add pre child li ln;
    match opn with
    | None -> ()
    | Some pn -> for_allP_eq (is_well_formed_prefix (ps_nat_lbytes 4) pre) (insert_sorted li pn.unmerged_leaves)
#pop-options

#push-options "--z3rlimit 25"
val pre_tree_hash:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  pre:bytes_compatible_pre bytes{pre_is_hash_compatible pre} ->
  #tkt:treekem_types bytes -> #l:nat -> #i:tree_index l ->
  t:treesync bytes tkt l i ->
  Lemma
  (requires is_well_formed _ pre t /\ Success? (tree_hash t))
  (ensures pre (Success?.v (tree_hash t)))
let rec pre_tree_hash #bytes #cb pre #tkt #l #i t =
  reveal_opaque (`%pre_is_hash_compatible) (pre_is_hash_compatible pre);
  match t with
  | TLeaf oln -> (
    serialize_wf_lemma (tree_hash_input_nt bytes tkt) pre (LeafTreeHashInput ({
      leaf_index = i;
      leaf_node = oln;
    }))
  )
  | TNode opn left right -> (
    pre_tree_hash pre left;
    pre_tree_hash pre right;
    let Success left_hash = tree_hash left in
    let Success right_hash = tree_hash right in
    serialize_wf_lemma (tree_hash_input_nt bytes tkt) pre (ParentTreeHashInput ({
      parent_node = opn;
      left_hash = left_hash;
      right_hash = right_hash;
    }))
  )
#pop-options

val pre_compute_parent_hash:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  pre:bytes_compatible_pre bytes{pre_is_hash_compatible pre} ->
  #tkt:treekem_types bytes -> #l:nat -> #i:tree_index l ->
  content:tkt.node_content -> parent_hash:mls_bytes bytes -> original_sibling:treesync bytes tkt l i ->
  Lemma
  (requires
    is_well_formed_prefix tkt.ps_node_content pre content /\
    pre parent_hash /\
    is_well_formed _ pre original_sibling /\
    Success? (compute_parent_hash content parent_hash original_sibling)
  )
  (ensures pre (Success?.v (compute_parent_hash content parent_hash original_sibling)))
let pre_compute_parent_hash #bytes #cb pre #tkt #l #i content parent_hash original_sibling =
  reveal_opaque (`%pre_is_hash_compatible) (pre_is_hash_compatible pre);
  pre_tree_hash pre original_sibling;
  let Success original_sibling_tree_hash = tree_hash original_sibling in
  serialize_wf_lemma (parent_hash_input_nt bytes tkt) pre ({
    content;
    parent_hash = parent_hash;
    original_sibling_tree_hash;
  })

#push-options "--z3rlimit 25"
val is_well_formed_apply_path_aux:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  pre:bytes_compatible_pre bytes{pre_is_hash_compatible pre} ->
  #tkt:treekem_types bytes -> #l:nat -> #i:tree_index l -> #li:leaf_index l i ->
  t:treesync bytes tkt l i -> p:pathsync bytes tkt l i li -> parent_parent_hash:bytes ->
  Lemma
  (requires
    is_well_formed _ pre t /\
    is_well_formed _ pre p /\
    pre parent_parent_hash /\
    Success? (apply_path_aux t p parent_parent_hash)
  )
  (ensures is_well_formed _ pre (Success?.v (apply_path_aux t p parent_parent_hash)))
let rec is_well_formed_apply_path_aux #bytes #cb pre #tkt #l #i #li t p parent_parent_hash =
  match t, p with
  | TLeaf _, PLeaf _ -> ()
  | TNode _ left right, PNode opt_ext_content p_next -> (
    let (child, sibling) = get_child_sibling t li in
    let Success (_, new_parent_parent_hash) = compute_new_np_and_ph opt_ext_content sibling parent_parent_hash in
    (match opt_ext_content with
    | None -> ()
    | Some ext_content -> pre_compute_parent_hash pre ext_content parent_parent_hash sibling
    );
    for_allP_eq (is_well_formed_prefix (ps_nat_lbytes 4) pre) [];
    is_well_formed_apply_path_aux pre child p_next new_parent_parent_hash
  )
#pop-options

val is_well_formed_apply_path:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  pre:bytes_compatible_pre bytes{pre_is_hash_compatible pre} ->
  #tkt:treekem_types bytes -> #l:nat -> #li:leaf_index l 0 ->
  t:treesync bytes tkt l 0 -> p:pathsync bytes tkt l 0 li ->
  Lemma
  (requires is_well_formed _ pre t /\ is_well_formed _ pre p /\ Success? (apply_path t p))
  (ensures is_well_formed _ pre (Success?.v (apply_path t p)))
let is_well_formed_apply_path #bytes #cb pre #tkt #l #li t p =
  is_well_formed_apply_path_aux pre t p (root_parent_hash #bytes)

#push-options "--z3rlimit 10"
val pre_compute_leaf_parent_hash_from_path:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  pre:bytes_compatible_pre bytes{pre_is_hash_compatible pre} ->
  #tkt:treekem_types bytes -> #l:nat -> #i:tree_index l -> #li:leaf_index l i ->
  t:treesync bytes tkt l i -> p:external_pathsync bytes tkt l i li -> parent_parent_hash:bytes ->
  Lemma
  (requires
    is_well_formed _ pre t /\
    is_well_formed _ pre p /\
    pre parent_parent_hash /\
    Success? (compute_leaf_parent_hash_from_path t p parent_parent_hash)
  )
  (ensures pre (Success?.v (compute_leaf_parent_hash_from_path t p parent_parent_hash)))
let rec pre_compute_leaf_parent_hash_from_path #bytes #cb pre #tkt #l #i #li t p parent_parent_hash =
  match t, p with
  | TLeaf _, PLeaf _ -> ()
  | TNode _ left right, PNode opt_ext_content p_next -> (
    let (child, sibling) = get_child_sibling t li in
    let Success (_,  new_parent_parent_hash) = compute_new_np_and_ph opt_ext_content sibling parent_parent_hash in
    (match opt_ext_content with
    | None -> ()
    | Some ext_content -> pre_compute_parent_hash pre ext_content parent_parent_hash sibling
    );
    pre_compute_leaf_parent_hash_from_path pre child p_next new_parent_parent_hash
  )
#pop-options

val is_well_formed_get_path_leaf:
  #bytes:Type0 -> {|bytes_like bytes|} ->
  pre:bytes_compatible_pre bytes ->
  #tkt:treekem_types bytes -> #l:nat -> #i:tree_index l -> #li:leaf_index l i ->
  p:external_pathsync bytes tkt l i li ->
  Lemma
  (requires is_well_formed _ pre p)
  (ensures is_well_formed_prefix (ps_leaf_node_data_nt tkt) pre (get_path_leaf p))
let rec is_well_formed_get_path_leaf #bytes #bl pre #tkt #l #i #li p =
  match p with
  | PLeaf _ -> ()
  | PNode _ p_next -> is_well_formed_get_path_leaf pre p_next

val is_well_formed_set_path_leaf:
  #bytes:Type0 -> {|bytes_like bytes|} ->
  pre:bytes_compatible_pre bytes ->
  #tkt:treekem_types bytes -> #l:nat -> #i:tree_index l -> #li:leaf_index l i ->
  p:external_pathsync bytes tkt l i li -> ln:leaf_node_nt bytes tkt ->
  Lemma
  (requires is_well_formed _ pre p /\ is_well_formed _ pre ln)
  (ensures is_well_formed _ pre (set_path_leaf p ln))
let rec is_well_formed_set_path_leaf #bytes #bl pre #tkt #l #i #li p ln =
  match p with
  | PLeaf _ -> ()
  | PNode _ p_next -> is_well_formed_set_path_leaf pre p_next ln

val is_well_formed_leaf_at:
  #bytes:Type0 -> {|bytes_like bytes|} ->
  pre:bytes_compatible_pre bytes ->
  #tkt:treekem_types bytes -> #l:nat -> #i:tree_index l ->
  t:treesync bytes tkt l i -> li:leaf_index l i ->
  Lemma
  (requires is_well_formed _ pre t)
  (ensures is_well_formed_prefix (ps_option (ps_leaf_node_nt tkt)) pre (leaf_at t li))
let rec is_well_formed_leaf_at #bytes #bl pre #tkt #l #i t li =
  if l = 0 then ()
  else (
    let (child, _) = get_child_sibling t li in
    is_well_formed_leaf_at pre child li
  )

open DY.Core
open MLS.Symbolic

val pre_is_hash_compatible_is_publishable:
  {|crypto_invariants|} -> tr:trace ->
  Lemma
  (pre_is_hash_compatible (is_publishable tr))
  [SMTPat (pre_is_hash_compatible (is_publishable tr))]
let pre_is_hash_compatible_is_publishable tr =
  reveal_opaque (`%pre_is_hash_compatible) (pre_is_hash_compatible (is_publishable tr))

val pre_is_hash_compatible_is_knowable_by:
  {|crypto_invariants|} -> l:label -> tr:trace ->
  Lemma
  (pre_is_hash_compatible (is_knowable_by l tr))
  [SMTPat (pre_is_hash_compatible (is_knowable_by l tr))]
let pre_is_hash_compatible_is_knowable_by #ci l tr =
  reveal_opaque (`%pre_is_hash_compatible) (pre_is_hash_compatible (is_knowable_by l tr))

val pre_is_hash_compatible_bytes_invariant:
  {|crypto_invariants|} -> tr:trace ->
  Lemma
  (pre_is_hash_compatible (bytes_invariant tr))
  [SMTPat (pre_is_hash_compatible (bytes_invariant tr))]
let pre_is_hash_compatible_bytes_invariant tr =
  reveal_opaque (`%pre_is_hash_compatible) (pre_is_hash_compatible (bytes_invariant tr))
