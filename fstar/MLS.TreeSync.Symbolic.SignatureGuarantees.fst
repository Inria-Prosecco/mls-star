module MLS.TreeSync.Symbolic.SignatureGuarantees

open Comparse
open MLS.Crypto
open MLS.Tree
open MLS.NetworkTypes
open MLS.TreeSync.NetworkTypes
open MLS.TreeSync.Types
open MLS.TreeSync.ParentHash
open MLS.TreeSync.Operations
open MLS.TreeSync.Invariants.UnmergedLeaves
open MLS.TreeSync.Invariants.ParentHash
open MLS.TreeSync.Invariants.ParentHash.Proofs //is_subtree_of
open MLS.TreeSync.Invariants.ValidLeaves
open MLS.TreeSync.Invariants.AuthService
open MLS.TreeSync.Invariants.AuthService.Proofs
open MLS.TreeSync.Proofs.ParentHashGuarantees
open MLS.TreeSync.Symbolic.IsValid
open MLS.Symbolic

#set-options "--fuel 1 --ifuel 1"

(*** Predicates ***)

noeq type treekem_parameters = {
  types: treekem_types dy_bytes;
  pred: timestamp -> l:nat & i:tree_index l & treesync dy_bytes types l i -> prop;
  pred_eq:
    #l1:nat -> #l2:nat -> #i1:tree_index l1 -> #i2:tree_index l2 ->
    time:timestamp ->
    t1:treesync dy_bytes types l1 i1 -> t2:treesync dy_bytes types l2 i2 -> li:nat -> Lemma
    (requires pred time (|l1, i1, t1|) /\ equivalent t1 t2 li)
    (ensures pred time (|l2, i2, t2|))
  ;
  pred_later:
    t1:timestamp -> t2:timestamp -> t:(l:nat & i:tree_index l & treesync dy_bytes types l i) -> Lemma
    (requires pred t1 t /\ t1 <$ t2)
    (ensures pred t2 t)
}

type dy_as_token_ (bytes:Type0) {|bytes_like bytes|} = {
  who: principal;
  time: timestamp;
}

%splice [ps_dy_as_token_] (gen_parser (`dy_as_token_))
%splice [ps_dy_as_token__is_valid] (gen_is_valid_lemma (`dy_as_token_))

let dy_as_token = dy_as_token_ dy_bytes
let ps_dy_as_token: parser_serializer dy_bytes dy_as_token = ps_dy_as_token_

val dy_asp: global_usage -> timestamp -> as_parameters dy_bytes
let dy_asp gu current_time = {
  token_t = dy_as_token;
  credential_ok = (fun (vk, cred) token ->
    token.time <$ current_time /\
    is_verification_key gu "MLS.LeafSignKey" token.time (readers [p_id token.who]) vk
  );
  valid_successor = (fun (vk_old, cred_old) (vk_new, cred_new) ->
    True
  );
}

val tree_list_has_pred: tkp:treekem_parameters -> timestamp -> tree_list dy_bytes tkp.types -> prop
let tree_list_has_pred tkp time tl =
  for_allP (tkp.pred time) tl

val leaf_node_spred: treekem_parameters -> sign_pred
let leaf_node_spred tkp usg time vk ln_tbs_bytes =
  match (parse (leaf_node_tbs_nt dy_bytes tkp.types) ln_tbs_bytes) with
  | None -> False
  | Some ln_tbs -> (
    match ln_tbs.data.source with
    | LNS_commit () -> (
      exists tl.
        tree_list_starts_with_tbs tl ln_tbs_bytes /\
        tree_list_is_parent_hash_linkedP tl /\
        tree_list_ends_at_root tl /\
        tree_list_has_pred tkp time tl
    )
    | _ -> True
  )

(*** Proof for verification ***)

#push-options "--fuel 2 --ifuel 1 --z3rlimit 25"
val last_tree_equivalent: #bytes:eqtype -> {|bytes_like bytes|} -> #tkt:treekem_types bytes -> tl1:tree_list bytes tkt -> tl2:tree_list bytes tkt -> li:nat -> Lemma
  (requires tree_list_equivalent_subset tl1 tl2 li /\ Cons? tl1)
  (ensures
    List.Tot.length tl1 <= List.Tot.length tl2 /\ (
      let (|_, _, t1|) = List.Tot.last tl1 in
      let (|_, _, t2|) = List.Tot.index tl2 (List.Tot.length tl1 - 1) in
      equivalent t1 t2 li
    )
  )
let rec last_tree_equivalent #bytes #bl #tkt tl1 tl2 li =
  match tl1, tl2 with
  | [_], _::_ -> ()
  | h1::t1, h2::t2 -> last_tree_equivalent t1 t2 li
#pop-options

//TODO: the actual is_subtree should be like that ?!
val is_subtree_of_nopre: #bytes:Type0 -> {|bytes_like bytes|} -> #tkt:treekem_types bytes -> #lu:nat -> #lp:nat -> #iu:tree_index lu -> #ip:tree_index lp -> treesync bytes tkt lu iu -> treesync bytes tkt lp ip -> prop
let is_subtree_of_nopre #bytes #bl #tkt #lu #lp #iu #ip u p =
  lu <= lp /\ leaf_index_inside lp ip iu /\ is_subtree_of u p

val is_subtree_of_transitive:
  #bytes:Type0 -> {|bytes_like bytes|} -> #tkt:treekem_types bytes ->
  #l1:nat -> #l2:nat -> #l3:nat -> #i1:tree_index l1 -> #i2:tree_index l2 -> #i3:tree_index l3 ->
  t1:treesync bytes tkt l1 i1 -> t2:treesync bytes tkt l2 i2 -> t3:treesync bytes tkt l3 i3 ->
  Lemma
  (requires is_subtree_of_nopre t1 t2 /\ is_subtree_of_nopre t2 t3)
  (ensures is_subtree_of_nopre t1 t3)
let rec is_subtree_of_transitive #bytes #bl #tkt #l1 #l2 #l3 #i1 #i2 #i3 t1 t2 t3 =
  if l2 = l3 then ()
  else (
    let (t3_child, _) = get_child_sibling t3 i2 in
    is_subtree_of_transitive t1 t2 t3_child
  )

val tree_list_head_subtree_tail: #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes -> tl:tree_list bytes tkt -> Lemma
  (requires
    Cons? tl /\
    tree_list_is_parent_hash_linkedP tl
  )
  (ensures (
    let (|_, _, t1|) = List.Tot.hd tl in
    let (|_, _, t2|) = List.Tot.last tl in
    is_subtree_of_nopre t1 t2
  ))
let rec tree_list_head_subtree_tail #bytes #cb #tkt tl =
  match tl with
  | [_] -> ()
  | head_tl::tail_tl -> (
    tree_list_head_subtree_tail tail_tl;
    let (|_, _, t1|) = head_tl in
    let (|_, _, t2|) = List.Tot.hd tail_tl in
    let (|_, _, t3|) = List.Tot.last tail_tl in
    is_subtree_of_transitive t1 t2 t3
  )

val get_authentifier_index: #tkt:treekem_types dy_bytes -> #l:nat -> #i:tree_index l -> t:treesync dy_bytes tkt l i -> Pure (leaf_index l i)
  (requires
    unmerged_leaves_ok t /\ parent_hash_invariant t /\
    node_has_parent_hash t
  )
  (ensures fun res -> Some? (leaf_at t res))
let get_authentifier_index #tkt #l #i t =
  let my_tl = parent_hash_invariant_to_tree_list t in
  let (|leaf_l, leaf_i, leaf|) = List.Tot.hd my_tl in
  tree_list_head_subtree_tail my_tl;
  leaf_at_subtree_leaf leaf t;
  leaf_i

val leaf_at_valid_leaves: #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes -> #l:nat -> #i:tree_index l -> group_id:mls_bytes bytes -> t:treesync bytes tkt l i -> li:leaf_index l i -> Lemma
  (requires valid_leaves_invariant group_id t)
  (ensures (
    match leaf_at t li with
    | Some ln -> leaf_is_valid ln group_id li
    | None -> True
  ))
let rec leaf_at_valid_leaves #bytes #cb #tkt #l #i group_id t li =
  match t with
  | TLeaf _ -> ()
  | TNode _ _ _ ->
    let (child, _) = get_child_sibling t li in
    leaf_at_valid_leaves group_id child li

val leaf_at_has_pre: #bytes:Type0 -> {|bytes_like bytes|} -> #tkt:treekem_types bytes -> #l:nat -> #i:tree_index l -> pre:bytes_compatible_pre bytes -> t:treesync bytes tkt l i -> li:leaf_index l i -> Lemma
  (requires treesync_has_pre pre t)
  (ensures option_has_pre pre (leaf_at t li))
let rec leaf_at_has_pre #bytes #bl #tkt #l #i pre t li =
  match t with
  | TLeaf _ -> ()
  | TNode _ _ _ ->
    let (child, _) = get_child_sibling t li in
    leaf_at_has_pre pre child li

#push-options "--z3rlimit 50"
val parent_hash_implies_treekem_pred: #l:nat -> #i:tree_index l -> gu:global_usage -> time:timestamp -> tkp:treekem_parameters -> group_id:mls_bytes dy_bytes -> t:treesync dy_bytes tkp.types l i -> ast:as_tokens dy_bytes (dy_asp gu time).token_t l i -> Lemma
  (requires
    has_sign_pred gu "LeafNodeTBS" (leaf_node_spred tkp) /\
    unmerged_leaves_ok t /\ parent_hash_invariant t /\ valid_leaves_invariant group_id t /\
    node_has_parent_hash t /\
    all_credentials_ok t ast /\
    treesync_has_pre (is_valid gu time) t /\
    is_valid gu time group_id
  )
  (ensures tkp.pred time (|l, i, t|) \/ is_corrupt time (p_id ((Some?.v (leaf_at ast (get_authentifier_index t))).who)))
let parent_hash_implies_treekem_pred #l #i gu time tkp group_id t ast =
  // Explicit typeclass instantiation is a workaround for FStarLang/FStar#2684
  let my_tl = parent_hash_invariant_to_tree_list #dy_bytes #crypto_dy_bytes t in
  let (|leaf_l, leaf_i, leaf|) = List.Tot.hd my_tl in
  tree_list_head_subtree_tail my_tl;
  leaf_at_subtree_leaf leaf t;
  leaf_at_valid_leaves group_id t leaf_i;
  leaf_at_has_pre (is_valid gu time) t leaf_i;
  let TLeaf (Some ln) = leaf in
  let ln_tbs = {
    data = ln.data;
    group_id = group_id;
    leaf_index = leaf_i;
  } in
  let ln_tbs_bytes = get_leaf_tbs ln group_id leaf_i in
  let leaf_token = Some?.v (leaf_at ast leaf_i) in
  let leaf_sk_label = readers [p_id leaf_token.who] in
  serialize_pre_lemma (leaf_node_tbs_nt dy_bytes tkp.types) (is_valid gu time) ln_tbs;
  verify_with_label_is_valid gu (leaf_node_spred tkp) "MLS.LeafSignKey" leaf_sk_label time ln.data.signature_key "LeafNodeTBS" ln_tbs_bytes ln.signature;

  introduce (exists time_sig. time_sig <$ time /\ leaf_node_spred tkp "MLS.LeafSignKey" time_sig ln.data.signature_key ln_tbs_bytes) ==> tkp.pred time (|l, i, t|)
  with _. (
    eliminate exists time_sig. time_sig <$ time /\ leaf_node_spred tkp "MLS.LeafSignKey" time_sig ln.data.signature_key ln_tbs_bytes
    returns tkp.pred time (|l, i, t|)
    with _. (
      parse_serialize_inv_lemma #dy_bytes (leaf_node_tbs_nt dy_bytes tkp.types) ln_tbs;
      eliminate exists (leaf_tl: tree_list dy_bytes tkp.types).
        tree_list_starts_with_tbs leaf_tl ln_tbs_bytes /\
        tree_list_is_parent_hash_linkedP leaf_tl /\
        tree_list_ends_at_root leaf_tl /\
        tree_list_has_pred tkp time_sig leaf_tl
      returns tkp.pred time_sig (|l, i, t|)
      with _. (
        let (b1, b2) = parent_hash_guarantee_theorem my_tl leaf_tl ln_tbs_bytes in
        hash_hash_inj b1 b2;
        last_tree_equivalent my_tl leaf_tl leaf_i;
        for_allP_eq (tkp.pred time_sig) leaf_tl;
        let (|_, _, original_t|) = List.Tot.index leaf_tl (List.Tot.length my_tl - 1) in
        tkp.pred_eq time_sig original_t t leaf_i
      );
      tkp.pred_later time_sig time (|l, i, t|)
    )
  );

  introduce (can_flow time leaf_sk_label public) ==> is_corrupt time (p_id ((Some?.v (leaf_at ast (get_authentifier_index t))).who))
  with _. (
    can_flow_to_public_implies_corruption time (p_id leaf_token.who)
  )
#pop-options

(*** Proof for signature ***)

val get_path_leaf_set_path_leaf: #bytes:Type0 -> {|bytes_like bytes|} -> #tkt:treekem_types bytes -> #l:nat -> #i:tree_index l -> #li:leaf_index l i -> p:external_pathsync bytes tkt l i li -> ln:leaf_node_nt bytes tkt -> Lemma
  (get_path_leaf (set_path_leaf p ln) == ln)
let rec get_path_leaf_set_path_leaf #bytes #bl #tkt #l #i #li p ln =
  match p with
  | PLeaf _ -> ()
  | PNode _ p_next -> get_path_leaf_set_path_leaf p_next ln

val compute_leaf_parent_hash_from_path_set_path_leaf: #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes -> #l:nat -> #i:tree_index l -> #li:leaf_index l i -> t:treesync bytes tkt l i -> p:external_pathsync bytes tkt l i li -> ln:leaf_node_nt bytes tkt -> parent_parent_hash:mls_bytes bytes -> Lemma
  (requires compute_leaf_parent_hash_from_path_pre t p (length #bytes parent_parent_hash))
  (ensures
    compute_leaf_parent_hash_from_path_pre t (set_path_leaf p ln) (length #bytes parent_parent_hash) /\
    compute_leaf_parent_hash_from_path t (set_path_leaf p ln) parent_parent_hash == compute_leaf_parent_hash_from_path t p parent_parent_hash
  )
let rec compute_leaf_parent_hash_from_path_set_path_leaf #bytes #cb #tkt #l #i #li t p ln parent_parent_hash =
  match t, p with
  | TLeaf _, PLeaf _ -> ()
  | TNode _ left right, PNode opt_ext_content p_next ->
    let (child, sibling) = get_child_sibling t li in
    let (_,  new_parent_parent_hash) = compute_new_np_and_ph opt_ext_content sibling parent_parent_hash in
    compute_leaf_parent_hash_from_path_set_path_leaf child p_next ln new_parent_parent_hash

#push-options "--z3rlimit 25"
val path_is_parent_hash_valid_external_path_to_path: #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes -> #l:nat -> #li:leaf_index l 0 -> t:treesync bytes tkt l 0 -> p:external_pathsync bytes tkt l 0 li -> group_id:mls_bytes bytes -> sk:sign_private_key bytes -> nonce:sign_nonce bytes -> Lemma
  (requires external_path_to_path_pre t p group_id)
  (ensures path_is_parent_hash_valid t (external_path_to_path t p group_id sk nonce))
let path_is_parent_hash_valid_external_path_to_path #bytes #cb #tkt #l #li t p group_id sk nonce =
  let new_lp = external_path_to_path_aux t p group_id sk nonce in
  get_path_leaf_set_path_leaf p new_lp;
  compute_leaf_parent_hash_from_path_set_path_leaf t p new_lp (root_parent_hash #bytes)
#pop-options

val path_is_filter_valid_set_path_leaf: #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes -> #l:nat -> #i:tree_index l -> #li:leaf_index l i -> t:treesync bytes tkt l i -> p:external_pathsync bytes tkt l i li -> ln:leaf_node_nt bytes tkt -> Lemma
  (requires path_is_filter_valid t p)
  (ensures path_is_filter_valid t (set_path_leaf p ln))
let rec path_is_filter_valid_set_path_leaf #bytes #cb #tkt #l #i #li t p ln =
  match t, p with
  | TLeaf _, PLeaf _ -> ()
  | TNode _ _ _, PNode _ p_next ->
    let (child, _) = get_child_sibling t li in
    path_is_filter_valid_set_path_leaf child p_next ln

#push-options "--z3rlimit 25"
val path_is_filter_valid_external_path_to_path: #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes -> #l:nat -> #li:leaf_index l 0 -> t:treesync bytes tkt l 0 -> p:external_pathsync bytes tkt l 0 li -> group_id:mls_bytes bytes -> sk:sign_private_key bytes -> nonce:sign_nonce bytes -> Lemma
  (requires external_path_to_path_pre t p group_id /\ path_is_filter_valid t p)
  (ensures path_is_filter_valid t (external_path_to_path t p group_id sk nonce))
let path_is_filter_valid_external_path_to_path #bytes #cb #tkt #l #li t p group_id sk nonce =
  let new_lp = external_path_to_path_aux t p group_id sk nonce in
  path_is_filter_valid_set_path_leaf t p new_lp
#pop-options

// This is the most convenient pre-condition for the signature predicate.
// Might not be great to have in TreeKEM however...
val external_path_has_pred: #tkp:treekem_parameters -> #l:nat -> #li:leaf_index l 0 -> time:timestamp -> t:treesync dy_bytes tkp.types l 0 -> p:external_pathsync dy_bytes tkp.types l 0 li -> group_id:mls_bytes dy_bytes -> sk:sign_private_key dy_bytes -> nonce:sign_nonce dy_bytes -> Pure prop
  (requires
    external_path_to_path_pre t p group_id /\
    path_is_filter_valid t p /\
    unmerged_leaves_ok t
  )
  (ensures fun _ -> True)
let external_path_has_pred #tkp #l #li time t p group_id sk nonce =
  let auth_p = external_path_to_path t p group_id sk nonce in
  path_is_parent_hash_valid_external_path_to_path t p group_id sk nonce;
  path_is_filter_valid_external_path_to_path t p group_id sk nonce;
  tree_list_has_pred tkp time (path_to_tree_list t auth_p)

#push-options "--z3rlimit 25"
val is_valid_external_path_to_path: #tkp:treekem_parameters -> #l:nat -> #li:leaf_index l 0 -> gu:global_usage -> time:timestamp -> t:treesync dy_bytes tkp.types l 0 -> p:external_pathsync dy_bytes tkp.types l 0 li -> group_id:mls_bytes dy_bytes -> sk:sign_private_key dy_bytes -> nonce:sign_nonce dy_bytes -> Lemma
  (requires
    has_sign_pred gu "LeafNodeTBS" (leaf_node_spred tkp) /\
    treesync_has_pre (is_valid gu time) t /\
    external_pathsync_has_pre (is_valid gu time) p /\
    is_valid gu time group_id /\
    is_valid gu time sk /\ get_usage gu sk == Some (sig_usage "MLS.LeafSignKey") /\
    is_valid gu time nonce /\
    get_label gu sk == get_label gu nonce /\
    unmerged_leaves_ok t /\
    path_is_filter_valid t p /\
    external_path_to_path_pre t p group_id /\
    external_path_has_pred time t p group_id sk nonce
  )
  (ensures pathsync_has_pre (is_valid gu time) (external_path_to_path t p group_id sk nonce))
let is_valid_external_path_to_path #tkp #l #li gu time t p group_id sk nonce =
  let computed_parent_hash = compute_leaf_parent_hash_from_path t p root_parent_hash in
  let lp = get_path_leaf p in
  let new_lp_data = { lp with source = LNS_commit (); parent_hash = computed_parent_hash; } in
  let new_lp_tbs: dy_bytes = serialize (leaf_node_tbs_nt dy_bytes tkp.types) ({data = new_lp_data; group_id; leaf_index = li;}) in
  let new_signature = sign_with_label sk "LeafNodeTBS" new_lp_tbs nonce in
  let new_lp = ({ data = new_lp_data; signature = new_signature } <: leaf_node_nt dy_bytes tkp.types) in
  let result_path = set_path_leaf p new_lp in
  path_is_parent_hash_valid_external_path_to_path t p group_id sk nonce;
  path_is_filter_valid_external_path_to_path t p group_id sk nonce;
  get_path_leaf_set_path_leaf p new_lp;
  pre_compute_leaf_parent_hash_from_path (is_valid gu time) t p root_parent_hash;
  pre_get_path_leaf (is_valid gu time) p;
  serialize_pre_lemma (leaf_node_tbs_nt dy_bytes tkp.types) (is_valid gu time) ({data = new_lp_data; group_id; leaf_index = li;});
  let tl = path_to_tree_list t result_path in
  introduce exists tl.
    tree_list_starts_with_tbs tl new_lp_tbs /\
    tree_list_is_parent_hash_linkedP tl /\
    tree_list_ends_at_root tl /\
    tree_list_has_pred tkp time tl
  with tl and ();
  parse_serialize_inv_lemma #dy_bytes (leaf_node_tbs_nt dy_bytes tkp.types) ({data = new_lp_data; group_id; leaf_index = li;});
  sign_with_label_valid gu (leaf_node_spred tkp) "MLS.LeafSignKey" time sk "LeafNodeTBS" new_lp_tbs nonce;
  pre_set_path_leaf (is_valid gu time) p new_lp
#pop-options
