module MLS.TreeSync.Symbolic.IsValid

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

#set-options "--fuel 1 --ifuel 1"

(*** Definitions ***)

val value_has_pre: #bytes:Type0 -> {|bytes_like bytes|} -> #a:Type -> {|parseable_serializeable bytes a|} -> bytes_compatible_pre bytes -> a -> prop
let value_has_pre #bytes #bl #a #psa pre x =
  is_well_formed a pre x

val option_has_pre: #bytes:Type0 -> {|bytes_like bytes|} -> #a:Type -> {|parseable_serializeable bytes a|} -> bytes_compatible_pre bytes -> option a -> prop
let option_has_pre #bytes #bl #a #psa pre ox =
  match ox with
  | None -> True
  | Some x -> value_has_pre pre x

val treesync_has_pre: #bytes:Type0 -> {|bytes_like bytes|} -> #tkt:treekem_types bytes -> #l:nat -> #i:tree_index l -> bytes_compatible_pre bytes -> treesync bytes tkt l i -> prop
let rec treesync_has_pre #bytes #bl #tkt #l #i pre t =
  match t with
  | TLeaf oln -> option_has_pre pre oln
  | TNode opn left right ->
    option_has_pre pre opn /\ treesync_has_pre pre left /\ treesync_has_pre pre right

val pathsync_has_pre: #bytes:Type0 -> {|bytes_like bytes|} -> #tkt:treekem_types bytes -> #l:nat -> #i:tree_index l -> #li:leaf_index l i -> bytes_compatible_pre bytes -> pathsync bytes tkt l i li -> prop
let rec pathsync_has_pre #bytes #bl #tkt #l #i #li pre p =
  match p with
  | PLeaf ln -> value_has_pre pre (ln <: leaf_node_nt bytes tkt)
  | PNode opt_content p_next ->
    let content_has_pre =
      match opt_content with
      | None -> True
      | Some content -> is_well_formed_partial tkt.ps_node_content pre content
    in
    content_has_pre /\ pathsync_has_pre pre p_next

val external_pathsync_has_pre: #bytes:Type0 -> {|bytes_like bytes|} -> #tkt:treekem_types bytes -> #l:nat -> #i:tree_index l -> #li:leaf_index l i -> bytes_compatible_pre bytes -> external_pathsync bytes tkt l i li -> prop
let rec external_pathsync_has_pre #bytes #bl #tkt #l #i #li pre p =
  match p with
  | PLeaf ln_data -> is_well_formed_partial (ps_leaf_node_data_nt tkt) pre (ln_data <: leaf_node_data_nt bytes tkt)
  | PNode opt_content p_next ->
    let content_has_pre =
      match opt_content with
      | None -> True
      | Some content -> is_well_formed_partial tkt.ps_node_content pre content
    in
    content_has_pre /\ external_pathsync_has_pre pre p_next

val pre_is_hash_compatible: #bytes:Type0 -> {|crypto_bytes bytes|} -> pre:(bytes -> prop) -> prop
let pre_is_hash_compatible #bytes #cb pre =
  forall b. (pre b /\ length b < hash_max_input_length #bytes) ==> pre (hash_hash b)

(*** Weakening lemmas ***)

val value_has_pre_weaken:
  #bytes:Type0 -> {|bytes_like bytes|} -> #a:Type -> {|parseable_serializeable bytes a|} ->
  pre_strong:bytes_compatible_pre bytes -> pre_weak:bytes_compatible_pre bytes ->
  x:a -> Lemma
  (requires value_has_pre pre_strong x /\ (forall b. pre_strong b ==> pre_weak b))
  (ensures value_has_pre pre_weak x)
let value_has_pre_weaken #bytes #bl #a #ps_a pre_strong pre_weak x =
  ()

val option_has_pre_weaken:
  #bytes:Type0 -> {|bytes_like bytes|} -> #a:Type -> {|parseable_serializeable bytes a|} ->
  pre_strong:bytes_compatible_pre bytes -> pre_weak:bytes_compatible_pre bytes ->
  opt_x:option a -> Lemma
  (requires option_has_pre pre_strong opt_x /\ (forall b. pre_strong b ==> pre_weak b))
  (ensures option_has_pre pre_weak opt_x)
let option_has_pre_weaken #bytes #bl #a #ps_a pre_strong pre_weak opt_x =
  match opt_x with
  | None -> ()
  | Some x ->
    ()

val treesync_has_pre_weaken:
  #bytes:Type0 -> {|bytes_like bytes|} -> #tkt:treekem_types bytes ->
  #l:nat -> #i:tree_index l ->
  pre_strong:bytes_compatible_pre bytes -> pre_weak:bytes_compatible_pre bytes ->
  t:treesync bytes tkt l i -> Lemma
  (requires treesync_has_pre pre_strong t /\ (forall b. pre_strong b ==> pre_weak b))
  (ensures treesync_has_pre pre_weak t)
let rec treesync_has_pre_weaken #bytes #bl #tkt #l #i pre_strong pre_weak t =
  match t with
  | TLeaf oln -> option_has_pre_weaken pre_strong pre_weak oln
  | TNode opn left right -> (
    treesync_has_pre_weaken pre_strong pre_weak left;
    treesync_has_pre_weaken pre_strong pre_weak right;
    option_has_pre_weaken pre_strong pre_weak opn
  )

val pathsync_has_pre_weaken:
  #bytes:Type0 -> {|bytes_like bytes|} -> #tkt:treekem_types bytes ->
  #l:nat -> #i:tree_index l -> #li:leaf_index l i ->
  pre_strong:bytes_compatible_pre bytes -> pre_weak:bytes_compatible_pre bytes ->
  p:pathsync bytes tkt l i li ->
  Lemma
  (requires pathsync_has_pre pre_strong p /\ (forall b. pre_strong b ==> pre_weak b))
  (ensures pathsync_has_pre pre_weak p)
let rec pathsync_has_pre_weaken #bytes #bl #tkt #l #i pre_strong pre_weak p =
  match p with
  | PLeaf ln ->
    value_has_pre_weaken pre_strong pre_weak (ln <: leaf_node_nt bytes tkt)
  | PNode opt_content p_next ->
    pathsync_has_pre_weaken pre_strong pre_weak p_next;
    match opt_content with
    | None -> ()
    | Some content -> (
      is_well_formed_partial_weaken tkt.ps_node_content pre_strong pre_weak content
    )

val external_pathsync_has_pre_weaken:
  #bytes:Type0 -> {|bytes_like bytes|} -> #tkt:treekem_types bytes ->
  #l:nat -> #i:tree_index l -> #li:leaf_index l i ->
  pre_strong:bytes_compatible_pre bytes -> pre_weak:bytes_compatible_pre bytes ->
  p:external_pathsync bytes tkt l i li ->
  Lemma
  (requires external_pathsync_has_pre pre_strong p /\ (forall b. pre_strong b ==> pre_weak b))
  (ensures external_pathsync_has_pre pre_weak p)
let rec external_pathsync_has_pre_weaken #bytes #bl #tkt #l #i pre_strong pre_weak p =
  match p with
  | PLeaf ln_data ->
    is_well_formed_partial_weaken (ps_leaf_node_data_nt tkt) pre_strong pre_weak ln_data
  | PNode opt_content p_next ->
    external_pathsync_has_pre_weaken pre_strong pre_weak p_next;
    match opt_content with
    | None -> ()
    | Some content -> (
      is_well_formed_partial_weaken tkt.ps_node_content pre_strong pre_weak content
    )

(*** Invariant proofs ***)

val treesync_has_pre_tree_change_path: #bytes:Type0 -> {|bytes_like bytes|} -> pre:bytes_compatible_pre bytes -> #tkt:treekem_types bytes -> #l:nat -> #i:tree_index l -> t:treesync bytes tkt l i -> li:leaf_index l i -> oln:option (leaf_node_nt bytes tkt) -> Lemma
  (requires treesync_has_pre pre t /\ option_has_pre pre oln)
  (ensures treesync_has_pre pre (tree_change_path t li oln None))
let rec treesync_has_pre_tree_change_path #bytes #bl pre #tkt #l #i t li oln =
  match t with
  | TLeaf _ -> ()
  | TNode _ left right ->
    if is_left_leaf li
    then treesync_has_pre_tree_change_path pre left li oln
    else treesync_has_pre_tree_change_path pre right li oln

val treesync_has_pre_tree_update: #bytes:Type0 -> {|bytes_like bytes|} -> pre:bytes_compatible_pre bytes -> #tkt:treekem_types bytes -> #l:nat -> #i:tree_index l -> t:treesync bytes tkt l i -> li:leaf_index l i -> ln:leaf_node_nt bytes tkt -> Lemma
  (requires treesync_has_pre pre t /\ value_has_pre pre ln)
  (ensures treesync_has_pre pre (tree_update t li ln))
let treesync_has_pre_tree_update #bytes #bl pre #tkt #l #i t li ln =
  treesync_has_pre_tree_change_path pre t li (Some ln)

val treesync_has_pre_tree_remove: #bytes:Type0 -> {|bytes_like bytes|} -> pre:bytes_compatible_pre bytes -> #tkt:treekem_types bytes -> #l:nat -> #i:tree_index l -> t:treesync bytes tkt l i -> li:leaf_index l i -> Lemma
  (requires treesync_has_pre pre t)
  (ensures treesync_has_pre pre (tree_remove t li))
let treesync_has_pre_tree_remove #bytes #bl pre #tkt #l #i t li =
  treesync_has_pre_tree_change_path pre t li None

val treesync_has_pre_mk_blank_tree: #bytes:Type0 -> {|bytes_like bytes|} -> pre:bytes_compatible_pre bytes -> #tkt:treekem_types bytes -> l:nat -> i:tree_index l -> Lemma
  (treesync_has_pre #bytes #_ #tkt pre (mk_blank_tree l i))
let rec treesync_has_pre_mk_blank_tree #bytes #bl pre #tkt l i =
  if l = 0 then ()
  else (
    treesync_has_pre_mk_blank_tree #bytes #_ pre #tkt (l-1) (left_index #l i);
    treesync_has_pre_mk_blank_tree #bytes #_ pre #tkt (l-1) (right_index #l i)
  )

val treesync_has_pre_tree_extend: #bytes:Type0 -> {|bytes_like bytes|} -> pre:bytes_compatible_pre bytes -> #tkt:treekem_types bytes -> #l:nat -> t:treesync bytes tkt l 0 -> Lemma
  (requires treesync_has_pre pre t)
  (ensures treesync_has_pre pre (tree_extend t))
let treesync_has_pre_tree_extend #bytes #bl pre #tkt #l t =
  treesync_has_pre_mk_blank_tree #bytes #bl pre #tkt l (right_index #(l+1) 0)

val treesync_has_pre_tree_truncate: #bytes:Type0 -> {|bytes_like bytes|} -> pre:bytes_compatible_pre bytes -> #tkt:treekem_types bytes -> #l:pos -> t:treesync bytes tkt l 0 -> Lemma
  (requires treesync_has_pre pre t /\ is_tree_empty (TNode?.right t))
  (ensures treesync_has_pre pre (tree_truncate t))
let treesync_has_pre_tree_truncate #bytes #bl pre #tkt #l t = ()

val treesync_has_pre_tree_add: #bytes:Type0 -> {|bytes_like bytes|} -> pre:bytes_compatible_pre bytes -> #tkt:treekem_types bytes -> #l:nat -> #i:tree_index l -> t:treesync bytes tkt l i -> li:leaf_index l i -> ln:leaf_node_nt bytes tkt -> Lemma
  (requires treesync_has_pre pre t /\ value_has_pre pre ln /\ tree_add_pre t li)
  (ensures treesync_has_pre pre (tree_add t li ln))
let rec treesync_has_pre_tree_add #bytes #bl pre #tkt #l #i t li ln =
  match t with
  | TLeaf _ -> ()
  | TNode opn _ _ ->
    let (child, _) = get_child_sibling t li in
    treesync_has_pre_tree_add pre child li ln;
    match opn with
    | None -> ()
    | Some pn -> for_allP_eq (is_well_formed_partial (ps_nat_lbytes 4) pre) (insert_sorted li pn.unmerged_leaves)

#push-options "--z3rlimit 25"
val pre_tree_hash: #bytes:Type0 -> {|crypto_bytes bytes|} -> pre:bytes_compatible_pre bytes{pre_is_hash_compatible pre} -> #tkt:treekem_types bytes -> #l:nat -> #i:tree_index l -> t:treesync bytes tkt l i -> Lemma
  (requires treesync_has_pre pre t /\ tree_hash_pre t)
  (ensures pre (tree_hash t))
let rec pre_tree_hash #bytes #cb pre #tkt #l #i t =
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
    let left_hash = tree_hash left in
    let right_hash = tree_hash right in
    serialize_wf_lemma (tree_hash_input_nt bytes tkt) pre (ParentTreeHashInput ({
      parent_node = opn;
      left_hash = left_hash;
      right_hash = right_hash;
    }))
  )
#pop-options

val pre_compute_parent_hash: #bytes:Type0 -> {|crypto_bytes bytes|} -> pre:bytes_compatible_pre bytes{pre_is_hash_compatible pre} -> #tkt:treekem_types bytes -> #l:nat -> #i:tree_index l -> content:tkt.node_content -> parent_hash:mls_bytes bytes -> original_sibling:treesync bytes tkt l i -> Lemma
  (requires
    is_well_formed_partial tkt.ps_node_content pre content /\
    pre parent_hash /\
    treesync_has_pre pre original_sibling /\
    compute_parent_hash_pre content (length #bytes parent_hash) original_sibling
  )
  (ensures pre (compute_parent_hash content parent_hash original_sibling))
let pre_compute_parent_hash #bytes #cb pre #tkt #l #i content parent_hash original_sibling =
  pre_tree_hash pre original_sibling;
  let original_sibling_tree_hash = tree_hash original_sibling in
  serialize_wf_lemma (parent_hash_input_nt bytes tkt) pre ({
    content;
    parent_hash = parent_hash;
    original_sibling_tree_hash;
  })

#push-options "--z3rlimit 25"
val treesync_has_pre_apply_path_aux: #bytes:Type0 -> {|crypto_bytes bytes|} -> pre:bytes_compatible_pre bytes{pre_is_hash_compatible pre} -> #tkt:treekem_types bytes -> #l:nat -> #i:tree_index l -> #li:leaf_index l i -> t:treesync bytes tkt l i -> p:pathsync bytes tkt l i li -> parent_parent_hash:mls_bytes bytes -> Lemma
  (requires treesync_has_pre pre t /\ pathsync_has_pre pre p /\ pre parent_parent_hash /\ apply_path_aux_pre t p (length #bytes parent_parent_hash))
  (ensures treesync_has_pre pre (apply_path_aux t p parent_parent_hash))
let rec treesync_has_pre_apply_path_aux #bytes #cb pre #tkt #l #i #li t p parent_parent_hash =
  match t, p with
  | TLeaf _, PLeaf _ -> ()
  | TNode _ left right, PNode opt_ext_content p_next -> (
    let (child, sibling) = get_child_sibling t li in
    let (_, new_parent_parent_hash) = compute_new_np_and_ph opt_ext_content sibling parent_parent_hash in
    (match opt_ext_content with
    | None -> ()
    | Some ext_content -> pre_compute_parent_hash pre ext_content parent_parent_hash sibling
    );
    for_allP_eq (is_well_formed_partial (ps_nat_lbytes 4) pre) [];
    treesync_has_pre_apply_path_aux pre child p_next new_parent_parent_hash
  )
#pop-options

val treesync_has_pre_apply_path: #bytes:Type0 -> {|crypto_bytes bytes|} -> pre:bytes_compatible_pre bytes{pre_is_hash_compatible pre} -> #tkt:treekem_types bytes -> #l:nat -> #li:leaf_index l 0 -> t:treesync bytes tkt l 0 -> p:pathsync bytes tkt l 0 li -> Lemma
  (requires treesync_has_pre pre t /\ pathsync_has_pre pre p /\ apply_path_pre t p)
  (ensures treesync_has_pre pre (apply_path t p))
let treesync_has_pre_apply_path #bytes #cb pre #tkt #l #li t p =
  treesync_has_pre_apply_path_aux pre t p (root_parent_hash #bytes)

val pre_compute_leaf_parent_hash_from_path: #bytes:Type0 -> {|crypto_bytes bytes|} -> pre:bytes_compatible_pre bytes{pre_is_hash_compatible pre} -> #tkt:treekem_types bytes -> #l:nat -> #i:tree_index l -> #li:leaf_index l i -> t:treesync bytes tkt l i -> p:external_pathsync bytes tkt l i li -> parent_parent_hash:mls_bytes bytes -> Lemma
  (requires treesync_has_pre pre t /\ external_pathsync_has_pre pre p /\ pre parent_parent_hash /\ compute_leaf_parent_hash_from_path_pre t p (length #bytes parent_parent_hash))
  (ensures pre (compute_leaf_parent_hash_from_path t p parent_parent_hash))
let rec pre_compute_leaf_parent_hash_from_path #bytes #cb pre #tkt #l #i #li t p parent_parent_hash =
  match t, p with
  | TLeaf _, PLeaf _ -> ()
  | TNode _ left right, PNode opt_ext_content p_next -> (
    let (child, sibling) = get_child_sibling t li in
    let (_,  new_parent_parent_hash) = compute_new_np_and_ph opt_ext_content sibling parent_parent_hash in
    (match opt_ext_content with
    | None -> ()
    | Some ext_content -> pre_compute_parent_hash pre ext_content parent_parent_hash sibling
    );
    pre_compute_leaf_parent_hash_from_path pre child p_next new_parent_parent_hash
  )

val pre_get_path_leaf: #bytes:Type0 -> {|bytes_like bytes|} -> pre:bytes_compatible_pre bytes -> #tkt:treekem_types bytes -> #l:nat -> #i:tree_index l -> #li:leaf_index l i -> p:external_pathsync bytes tkt l i li -> Lemma
  (requires external_pathsync_has_pre pre p)
  (ensures is_well_formed_partial (ps_leaf_node_data_nt tkt) pre (get_path_leaf p))
let rec pre_get_path_leaf #bytes #bl pre #tkt #l #i #li p =
  match p with
  | PLeaf _ -> ()
  | PNode _ p_next -> pre_get_path_leaf pre p_next

val pre_set_path_leaf: #bytes:Type0 -> {|bytes_like bytes|} -> pre:bytes_compatible_pre bytes -> #tkt:treekem_types bytes -> #l:nat -> #i:tree_index l -> #li:leaf_index l i -> p:external_pathsync bytes tkt l i li -> ln:leaf_node_nt bytes tkt -> Lemma
  (requires external_pathsync_has_pre pre p /\ value_has_pre pre ln)
  (ensures pathsync_has_pre pre (set_path_leaf p ln))
let rec pre_set_path_leaf #bytes #bl pre #tkt #l #i #li p ln =
  match p with
  | PLeaf _ -> ()
  | PNode _ p_next -> pre_set_path_leaf pre p_next ln

open MLS.Symbolic

val pre_is_hash_compatible_is_msg: p:global_usage -> l:label -> i:timestamp -> Lemma
  (pre_is_hash_compatible (is_msg p l i))
  [SMTPat (pre_is_hash_compatible (is_msg p l i))]
let pre_is_hash_compatible_is_msg p l i =
  introduce forall b. (is_msg p l i b /\ length b < hash_max_input_length #dy_bytes) ==> is_msg p l i (hash_hash b)
  with (
    introduce  (is_msg p l i b /\ length b < hash_max_input_length #dy_bytes) ==> is_msg p l i (hash_hash b)
    with _. (
      LabeledCryptoAPI.hash_lemma #p #i #l b
    )
  )

val pre_is_hash_compatible_is_valid: p:global_usage -> i:timestamp -> Lemma
  (pre_is_hash_compatible (is_valid p i))
  [SMTPat (pre_is_hash_compatible (is_valid p i))]
let pre_is_hash_compatible_is_valid p i =
  pre_is_hash_compatible_is_msg p SecrecyLabels.private_label i
