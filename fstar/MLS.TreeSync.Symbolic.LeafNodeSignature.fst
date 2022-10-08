module MLS.TreeSync.Symbolic.LeafNodeSignature

open FStar.Mul
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
open MLS.TreeSync.API.Types
open MLS.TreeSync.Symbolic.IsValid
open MLS.Symbolic.Parsers
open MLS.Symbolic

#set-options "--fuel 1 --ifuel 1"

(*** Predicates ***)

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
    is_verification_key gu "MLS.LeafSignKey" (readers [p_id token.who]) token.time vk
  );
  valid_successor = (fun (vk_old, cred_old) (vk_new, cred_new) ->
    True
  );
}

val leaf_node_to_event: #tkt:treekem_types dy_bytes -> leaf_node_tbs_nt dy_bytes tkt -> event
let leaf_node_to_event #tkt ln_tbs =
  let evt_bytes = serialize _ ln_tbs in
  ("MLS.TreeSync.LeafNodeEvent", [evt_bytes])

val leaf_node_has_event: #tkt:treekem_types dy_bytes -> principal -> timestamp -> leaf_node_tbs_nt dy_bytes tkt -> prop
let leaf_node_has_event #tkt prin time ln_tbs =
  did_event_occur_before time prin (leaf_node_to_event ln_tbs)

type group_has_tree_event (bytes:Type0) {|bytes_like bytes|} (tkt:treekem_types bytes) = {
  group_id: mls_bytes bytes;
  [@@@ with_parser #bytes ps_nat]
  l: nat;
  [@@@ with_parser #bytes ps_nat]
  i: nat;
  [@@@ with_parser #bytes (ps_treesync tkt l (i*(pow2 l)))]
  t: treesync bytes tkt l (i*(pow2 l));
}

%splice [ps_group_has_tree_event] (gen_parser (`group_has_tree_event))

instance parseable_serializeable_group_has_tree_event (bytes:Type0) {|bytes_like bytes|} (tkt:treekem_types bytes): parseable_serializeable bytes (group_has_tree_event bytes tkt) = mk_parseable_serializeable (ps_group_has_tree_event tkt)

#push-options "--z3cliopt smt.arith.nl=false"
val tree_has_event_arithmetic_lemma: l:nat -> i:tree_index l -> Lemma
  ((i/(pow2 l))*(pow2 l) == i)
let tree_has_event_arithmetic_lemma l i =
  eliminate exists (k:nat). i = k*(pow2 l)
  returns (i/(pow2 l))*(pow2 l) == i
  with _. (
    FStar.Math.Lemmas.cancel_mul_div k (pow2 l)
  )
#pop-options

val tree_to_event:
  #tkt:treekem_types dy_bytes ->
  mls_bytes dy_bytes -> (l:nat & i:tree_index l & treesync dy_bytes tkt l i) ->
  event
let tree_to_event #tkt group_id (|l, i, t|) =
  tree_has_event_arithmetic_lemma l i;
  let evt: group_has_tree_event dy_bytes tkt = {
    group_id;
    l;
    i = i/(pow2 l);
    t;
  } in
  let evt_bytes = serialize _ evt in
  ("MLS.TreeSync.GroupHasTreeEvent", [evt_bytes])

val tree_has_event: #tkt:treekem_types dy_bytes -> principal -> timestamp -> mls_bytes dy_bytes -> (l:nat & i:tree_index l & treesync dy_bytes tkt l i) -> prop
let tree_has_event #tkt prin time group_id (|l, i, t|) =
  did_event_occur_before time prin (tree_to_event group_id (|l, i, t|))

val tree_has_equivalent_event: #l:nat -> #i:tree_index l -> tkt:treekem_types dy_bytes -> principal -> timestamp -> mls_bytes dy_bytes -> treesync dy_bytes tkt l i -> leaf_index l i -> prop
let tree_has_equivalent_event #l #i tkt prin time group_id t li =
  (exists (t':treesync dy_bytes tkt l i). equivalent t t' li /\ tree_has_event prin time group_id (|l, i, t'|))

val tree_list_has_event: #tkt:treekem_types dy_bytes -> principal -> timestamp -> mls_bytes dy_bytes -> tree_list dy_bytes tkt -> prop
let tree_list_has_event #tkt prin time group_id tl =
  for_allP (tree_has_event prin time group_id) tl

val leaf_node_label: string
let leaf_node_label = "LeafNodeTBS"

val leaf_node_spred: key_usages -> treekem_types dy_bytes -> sign_pred
let leaf_node_spred ku tkt usg time vk ln_tbs_bytes =
  match (parse (leaf_node_tbs_nt dy_bytes tkt) ln_tbs_bytes) with
  | None -> False
  | Some ln_tbs -> (
    exists prin.
      leaf_node_has_event prin time ln_tbs /\ (
      match ln_tbs.data.source with
      | LNS_commit () -> (
        exists (tl: tree_list dy_bytes tkt).
          get_signkey_label ku vk == readers [p_id prin] /\
          tree_list_starts_with_tbs tl ln_tbs_bytes /\
          tree_list_is_parent_hash_linkedP tl /\
          tree_list_ends_at_root tl /\
          tree_list_has_event prin time ln_tbs.group_id tl
      )
      | LNS_update () -> (
        get_signkey_label ku vk == readers [p_id prin] /\
        tree_has_event prin time ln_tbs.group_id (|0, ln_tbs.leaf_index, TLeaf (Some ({data = ln_tbs.data; signature = empty #dy_bytes;} <: leaf_node_nt dy_bytes tkt))|)
      )
      | LNS_key_package () -> True
      )
  )

val has_leaf_node_tbs_invariant: treekem_types dy_bytes -> global_usage -> prop
let has_leaf_node_tbs_invariant tkt gu =
  has_sign_pred gu leaf_node_label (leaf_node_spred gu.key_usages tkt)

(*** Proof of verification, for a tree ***)

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

val is_subtree_of_transitive:
  #bytes:Type0 -> {|bytes_like bytes|} -> #tkt:treekem_types bytes ->
  #l1:nat -> #l2:nat -> #l3:nat -> #i1:tree_index l1 -> #i2:tree_index l2 -> #i3:tree_index l3 ->
  t1:treesync bytes tkt l1 i1 -> t2:treesync bytes tkt l2 i2 -> t3:treesync bytes tkt l3 i3 ->
  Lemma
  (requires is_subtree_of t1 t2 /\ is_subtree_of t2 t3)
  (ensures is_subtree_of t1 t3)
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
    is_subtree_of t1 t2
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
    node_not_blank t
  )
  (ensures fun res -> Some? (leaf_at t res))
let get_authentifier_index #tkt #l #i t =
  if l = 0 then i
  else (
    let my_tl = parent_hash_invariant_to_tree_list t in
    let (|leaf_l, leaf_i, leaf|) = List.Tot.hd my_tl in
    tree_list_head_subtree_tail my_tl;
    leaf_at_subtree_leaf leaf t;
    leaf_i
  )

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

#push-options "--z3rlimit 100"
val parent_hash_implies_event: #tkt:treekem_types dy_bytes -> #l:nat -> #i:tree_index l -> gu:global_usage -> time:timestamp -> group_id:mls_bytes dy_bytes -> t:treesync dy_bytes tkt l i -> ast:as_tokens dy_bytes (dy_asp gu time).token_t l i -> Lemma
  (requires
    has_leaf_node_tbs_invariant tkt gu /\
    unmerged_leaves_ok t /\ parent_hash_invariant t /\ valid_leaves_invariant group_id t /\
    node_has_parent_hash t /\
    all_credentials_ok t ast /\
    treesync_has_pre (is_valid gu time) t /\
    is_valid gu time group_id
  )
  (ensures (
    let authentifier_li = get_authentifier_index t in
    let authentifier = (Some?.v (leaf_at ast authentifier_li)).who in
    (
      tree_has_equivalent_event tkt authentifier time group_id t authentifier_li
    ) \/ (
      is_corrupt time (p_id authentifier)
    )
  ))
let parent_hash_implies_event #tkt #l #i gu time group_id t ast =
  let my_tl = parent_hash_invariant_to_tree_list t in
  let (|leaf_l, leaf_i, leaf|) = List.Tot.hd my_tl in
  tree_list_head_subtree_tail my_tl;
  leaf_at_subtree_leaf leaf t;
  leaf_at_valid_leaves group_id t leaf_i;
  leaf_at_has_pre (is_valid gu time) t leaf_i;
  let TLeaf (Some ln) = leaf in
  let ln_tbs: leaf_node_tbs_nt dy_bytes tkt = {
    data = ln.data;
    group_id = group_id;
    leaf_index = leaf_i;
  } in
  let ln_tbs_bytes = get_leaf_tbs ln group_id leaf_i in
  let leaf_token = Some?.v (leaf_at ast leaf_i) in
  let authentifier = leaf_token.who in
  let authentifier_li = leaf_i in
  let leaf_sk_label = readers [p_id leaf_token.who] in
  serialize_pre_lemma (leaf_node_tbs_nt dy_bytes tkt) (is_valid gu time) ln_tbs;
  verify_with_label_is_valid gu (leaf_node_spred gu.key_usages tkt) "MLS.LeafSignKey" leaf_sk_label time ln.data.signature_key "LeafNodeTBS" ln_tbs_bytes ln.signature;

  introduce (exists time_sig. time_sig <$ time /\ leaf_node_spred gu.key_usages tkt "MLS.LeafSignKey" time_sig ln.data.signature_key ln_tbs_bytes) ==> tree_has_equivalent_event tkt authentifier time group_id t authentifier_li
  with _. (
    eliminate exists time_sig. time_sig <$ time /\ leaf_node_spred gu.key_usages tkt "MLS.LeafSignKey" time_sig ln.data.signature_key ln_tbs_bytes
    returns tree_has_equivalent_event tkt authentifier time group_id t authentifier_li
    with _. (
      parse_serialize_inv_lemma #dy_bytes (leaf_node_tbs_nt dy_bytes tkt) ln_tbs;

      eliminate exists (prin:principal) (leaf_tl: tree_list dy_bytes tkt).
        get_signkey_label gu.key_usages ln.data.signature_key == readers [p_id prin] /\
        tree_list_starts_with_tbs leaf_tl ln_tbs_bytes /\
        tree_list_is_parent_hash_linkedP leaf_tl /\
        tree_list_ends_at_root leaf_tl /\
        tree_list_has_event prin time_sig ln_tbs.group_id leaf_tl
      returns tree_has_equivalent_event tkt authentifier time group_id t authentifier_li
      with _. (
        let (b1, b2) = parent_hash_guarantee_theorem my_tl leaf_tl ln_tbs_bytes in
        hash_hash_inj b1 b2;
        last_tree_equivalent my_tl leaf_tl leaf_i;
        for_allP_eq (tree_has_event prin time_sig group_id) leaf_tl;
        is_verification_key_to_signkey_label gu "MLS.LeafSignKey" (readers [p_id authentifier]) time ln.data.signature_key;
        readers_is_injective prin authentifier;
        let (|_, _, original_t|) = List.Tot.index leaf_tl (List.Tot.length my_tl - 1) in
        introduce exists (t':treesync dy_bytes tkt l i). equivalent t t' authentifier_li /\ tree_has_event authentifier time group_id (|l, i, t'|)
        with original_t
        and ()
      )
    )
  );

  introduce (can_flow time leaf_sk_label public) ==> is_corrupt time (p_id ((Some?.v (leaf_at ast (get_authentifier_index t))).who))
  with _. (
    can_flow_to_public_implies_corruption time (p_id leaf_token.who)
  )
#pop-options

(*** Proof of verification, for a state ***)

val valid_leaves_invariant_subtree:
  #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes ->
  #lp:nat -> #ld:nat -> #ip:tree_index lp -> #id:tree_index ld ->
  group_id:mls_bytes bytes -> d:treesync bytes tkt ld id -> p:treesync bytes tkt lp ip -> Lemma
  (requires valid_leaves_invariant group_id p /\ is_subtree_of d p)
  (ensures valid_leaves_invariant group_id d)
let rec valid_leaves_invariant_subtree #bytes #cb #tkt #lp #ld #ip #id group_id d p =
  if ld = lp then ()
  else (
    let (c,  _) = get_child_sibling p id in
    valid_leaves_invariant_subtree group_id d c
  )

val treesync_has_pre_subtree:
  #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes ->
  #lp:nat -> #ld:nat -> #ip:tree_index lp -> #id:tree_index ld ->
  pre:bytes_compatible_pre bytes -> d:treesync bytes tkt ld id -> p:treesync bytes tkt lp ip -> Lemma
  (requires treesync_has_pre pre p /\ is_subtree_of d p)
  (ensures treesync_has_pre pre d)
let rec treesync_has_pre_subtree #bytes #cb #tkt #lp #ld #ip #id pre d p =
  if ld = lp then ()
  else (
    let (c,  _) = get_child_sibling p id in
    treesync_has_pre_subtree pre d c
  )

val all_credentials_ok_subtree:
  #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes -> #asp:as_parameters bytes ->
  #lp:nat -> #ld:nat -> #ip:tree_index lp -> #id:tree_index ld ->
  d:treesync bytes tkt ld id -> p:treesync bytes tkt lp ip ->
  ast_d:as_tokens bytes asp.token_t ld id -> ast_p:as_tokens bytes asp.token_t lp ip ->
  Lemma
  (requires all_credentials_ok p ast_p /\ is_subtree_of d p /\ is_subtree_of ast_d ast_p)
  (ensures all_credentials_ok d ast_d)
let rec all_credentials_ok_subtree #bytes #cb #tkt #asp #lp #ld #ip #id d p ast_d ast_p =
  if ld = lp then ()
  else (
    let (c,  _) = get_child_sibling p id in
    let (ast_c,  _) = get_child_sibling ast_p id in
    introduce forall li. one_credential_ok c ast_c li with (
      assert(one_credential_ok p ast_p li)
    );
    all_credentials_ok_subtree d c ast_d ast_c
  )

val state_implies_event:
  #tkt:treekem_types dy_bytes -> #l:nat -> #i:tree_index l ->
  gu:global_usage -> time:timestamp ->
  st:treesync_state dy_bytes tkt (dy_asp gu time) -> t:treesync dy_bytes tkt l i -> ast:as_tokens dy_bytes (dy_asp gu time).token_t l i -> Lemma
  (requires
    has_leaf_node_tbs_invariant tkt gu /\
    node_has_parent_hash t /\
    treesync_has_pre (is_valid gu time) st.tree /\
    is_valid gu time st.group_id /\
    is_subtree_of t st.tree /\
    is_subtree_of ast st.tokens
  )
  (ensures (
    // The following line is only there as precondition for the rest of the theorem
    unmerged_leaves_ok t /\ parent_hash_invariant t /\ all_credentials_ok t ast /\ (
      let authentifier_li = get_authentifier_index t in
      let authentifier = (Some?.v (leaf_at ast authentifier_li)).who in
      (
        tree_has_equivalent_event tkt authentifier time st.group_id t authentifier_li
      ) \/ (
        is_corrupt time (p_id authentifier)
      )
    )
  ))
let state_implies_event #tkt #l #i gu time st t ast =
  unmerged_leaves_ok_subtree t st.tree;
  parent_hash_invariant_subtree t st.tree;
  valid_leaves_invariant_subtree st.group_id t st.tree;
  treesync_has_pre_subtree (is_valid gu time) t st.tree;
  all_credentials_ok_subtree t st.tree ast st.tokens;
  parent_hash_implies_event gu time st.group_id t ast

(*** Proof of path signature ***)

val external_path_to_path_aux_nosig: #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes -> #l:nat -> #i:tree_index l -> #li:leaf_index l i -> t:treesync bytes tkt l i -> p:external_pathsync bytes tkt l i li -> group_id:mls_bytes bytes -> Pure (leaf_node_nt bytes tkt)
  (requires external_path_to_path_pre t p group_id)
  (ensures fun _ -> True)
let external_path_to_path_aux_nosig #bytes #cb #tkt #l #i #li t p group_id =
  let computed_parent_hash = compute_leaf_parent_hash_from_path t p root_parent_hash in
  let lp = get_path_leaf p in
  let new_lp_data = { lp with source = LNS_commit (); parent_hash = computed_parent_hash; } in
  ({ data = new_lp_data; signature = empty #bytes } <: leaf_node_nt bytes tkt)

val external_path_to_path_nosig: #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes -> #l:nat -> #i:tree_index l -> #li:leaf_index l i -> t:treesync bytes tkt l i -> p:external_pathsync bytes tkt l i li -> group_id:mls_bytes bytes -> Pure (pathsync bytes tkt l i li)
  (requires external_path_to_path_pre t p group_id)
  (ensures fun _ -> True)
let external_path_to_path_nosig #bytes #cb #tkt #l #i #li t p group_id =
  set_path_leaf p (external_path_to_path_aux_nosig t p group_id)

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
val path_is_parent_hash_valid_external_path_to_path_nosig: #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes -> #l:nat -> #li:leaf_index l 0 -> t:treesync bytes tkt l 0 -> p:external_pathsync bytes tkt l 0 li -> group_id:mls_bytes bytes -> Lemma
  (requires external_path_to_path_pre t p group_id)
  (ensures path_is_parent_hash_valid t (external_path_to_path_nosig t p group_id))
let path_is_parent_hash_valid_external_path_to_path_nosig #bytes #cb #tkt #l #li t p group_id =
  let new_lp = external_path_to_path_aux_nosig t p group_id in
  get_path_leaf_set_path_leaf p new_lp;
  compute_leaf_parent_hash_from_path_set_path_leaf t p new_lp (root_parent_hash #bytes)
#pop-options

(*
#push-options "--z3rlimit 25"
val path_is_parent_hash_valid_external_path_to_path: #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes -> #l:nat -> #li:leaf_index l 0 -> t:treesync bytes tkt l 0 -> p:external_pathsync bytes tkt l 0 li -> group_id:mls_bytes bytes -> sk:sign_private_key bytes -> nonce:sign_nonce bytes -> Lemma
  (requires external_path_to_path_pre t p group_id)
  (ensures path_is_parent_hash_valid t (external_path_to_path t p group_id sk nonce))
let path_is_parent_hash_valid_external_path_to_path #bytes #cb #tkt #l #li t p group_id sk nonce =
  let new_lp = external_path_to_path_aux t p group_id sk nonce in
  get_path_leaf_set_path_leaf p new_lp;
  compute_leaf_parent_hash_from_path_set_path_leaf t p new_lp (root_parent_hash #bytes)
#pop-options
*)

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
val path_is_filter_valid_external_path_to_path_nosig: #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes -> #l:nat -> #li:leaf_index l 0 -> t:treesync bytes tkt l 0 -> p:external_pathsync bytes tkt l 0 li -> group_id:mls_bytes bytes -> Lemma
  (requires external_path_to_path_pre t p group_id /\ path_is_filter_valid t p)
  (ensures path_is_filter_valid t (external_path_to_path_nosig t p group_id))
let path_is_filter_valid_external_path_to_path_nosig #bytes #cb #tkt #l #li t p group_id =
  let new_lp = external_path_to_path_aux_nosig t p group_id in
  path_is_filter_valid_set_path_leaf t p new_lp
#pop-options

(*
#push-options "--z3rlimit 25"
val path_is_filter_valid_external_path_to_path: #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes -> #l:nat -> #li:leaf_index l 0 -> t:treesync bytes tkt l 0 -> p:external_pathsync bytes tkt l 0 li -> group_id:mls_bytes bytes -> sk:sign_private_key bytes -> nonce:sign_nonce bytes -> Lemma
  (requires external_path_to_path_pre t p group_id /\ path_is_filter_valid t p)
  (ensures path_is_filter_valid t (external_path_to_path t p group_id sk nonce))
let path_is_filter_valid_external_path_to_path #bytes #cb #tkt #l #li t p group_id sk nonce =
  let new_lp = external_path_to_path_aux t p group_id sk nonce in
  path_is_filter_valid_set_path_leaf t p new_lp
#pop-options
*)

val external_path_has_pred: #tkt:treekem_types dy_bytes -> #l:nat -> #li:leaf_index l 0 -> prin:principal -> time:timestamp -> t:treesync dy_bytes tkt l 0 -> p:external_pathsync dy_bytes tkt l 0 li -> group_id:mls_bytes dy_bytes -> Pure prop
  (requires external_path_to_path_pre t p group_id)
  (ensures fun _ -> True)
let external_path_has_pred #tkt #l #li prin time t p group_id =
  //This lemma is useful to know that auth_ln.data.source == LNS_commit
  path_is_parent_hash_valid_external_path_to_path_nosig t p group_id;
  let auth_p = external_path_to_path_nosig t p group_id in
  let auth_ln = get_path_leaf auth_p in
  leaf_node_has_event prin time ({data = auth_ln.data; group_id; leaf_index = li;}) /\
  tree_list_has_event prin time group_id (path_to_tree_list t auth_p)

// This theorem can be instantiated with various labels to prove more specific theorems.
// With label = SecrecyLabels.public, we get a version with `is_publishable`.
// With label= SecrecyLabels.private_label, we get a version with `is_valid`.
#push-options "--z3rlimit 50"
val is_msg_external_path_to_path:
  #tkt:treekem_types dy_bytes ->
  #l:nat -> #li:leaf_index l 0 ->
  gu:global_usage -> prin:principal -> label:label -> time:timestamp ->
  t:treesync dy_bytes tkt l 0 -> p:external_pathsync dy_bytes tkt l 0 li -> group_id:mls_bytes dy_bytes ->
  sk:sign_private_key dy_bytes -> nonce:sign_nonce dy_bytes ->
  Lemma
  (requires
    external_path_to_path_pre t p group_id /\
    path_is_filter_valid t p /\
    unmerged_leaves_ok t /\
    external_path_has_pred prin time t p group_id /\
    treesync_has_pre (is_msg gu label time) t /\
    external_pathsync_has_pre (is_msg gu label time) p /\
    is_msg gu label time group_id /\
    is_valid gu time sk /\ get_usage gu sk == Some (sig_usage "MLS.LeafSignKey") /\
    is_valid gu time nonce /\
    get_label gu sk == readers [p_id prin] /\
    get_label gu nonce == readers [p_id prin] /\
    has_leaf_node_tbs_invariant tkt gu
  )
  (ensures pathsync_has_pre (is_msg gu label time) (external_path_to_path t p group_id sk nonce))
let is_msg_external_path_to_path #tkt #l #li gu prin label time t p group_id sk nonce =
  let computed_parent_hash = compute_leaf_parent_hash_from_path t p root_parent_hash in
  let ln_data = get_path_leaf p in
  let new_ln_data = { ln_data with source = LNS_commit (); parent_hash = computed_parent_hash; } in
  let new_ln_tbs: leaf_node_tbs_nt dy_bytes tkt = ({data = new_ln_data; group_id; leaf_index = li;}) in
  let new_ln_tbs_bytes: dy_bytes = serialize (leaf_node_tbs_nt dy_bytes tkt) new_ln_tbs in
  let new_signature = sign_with_label sk "LeafNodeTBS" new_ln_tbs_bytes nonce in
  let new_ln = ({ data = new_ln_data; signature = new_signature; } <: leaf_node_nt dy_bytes tkt) in
  let new_unsigned_ln = ({ data = new_ln_data; signature = empty #dy_bytes; } <: leaf_node_nt dy_bytes tkt) in
  let unsigned_path = set_path_leaf p new_unsigned_ln in
  path_is_parent_hash_valid_external_path_to_path_nosig t p group_id;
  path_is_filter_valid_external_path_to_path_nosig t p group_id;
  get_path_leaf_set_path_leaf p new_unsigned_ln;
  pre_compute_leaf_parent_hash_from_path (is_msg gu label time) t p root_parent_hash;
  pre_get_path_leaf (is_msg gu label time) p;
  serialize_pre_lemma (leaf_node_tbs_nt dy_bytes tkt) (is_msg gu label time) ({data = new_ln_data; group_id; leaf_index = li;});
  let tl = path_to_tree_list t unsigned_path in
  path_to_tree_list_lemma t unsigned_path;
  introduce exists prin tl.
    get_signkey_label gu.key_usages (CryptoLib.vk sk) == readers [p_id prin] /\
    tree_list_starts_with_tbs tl new_ln_tbs_bytes /\
    tree_list_is_parent_hash_linkedP tl /\
    tree_list_ends_at_root tl /\
    tree_list_has_event prin time new_ln_tbs.group_id tl /\
    leaf_node_has_event prin time new_ln_tbs
  with prin tl and (
    LabeledCryptoAPI.vk_lemma #gu #time #(readers [p_id prin]) sk
  );
  parse_serialize_inv_lemma #dy_bytes (leaf_node_tbs_nt dy_bytes tkt) new_ln_tbs;
  sign_with_label_valid gu (leaf_node_spred gu.key_usages tkt) "MLS.LeafSignKey" time sk "LeafNodeTBS" new_ln_tbs_bytes nonce;
  pre_set_path_leaf (is_msg gu label time) p new_ln
#pop-options

(*** Proof of individual leaf signature ***)

val is_msg_sign_leaf_node_data_key_package:
  #tkt:treekem_types dy_bytes ->
  gu:global_usage -> prin:principal -> label:label -> time:timestamp ->
  ln_data:leaf_node_data_nt dy_bytes tkt ->
  sk:sign_private_key dy_bytes -> nonce:sign_nonce dy_bytes ->
  Lemma
  (requires
    ln_data.source == LNS_key_package () /\
    sign_leaf_node_data_key_package_pre ln_data /\
    leaf_node_has_event prin time ({data = ln_data; group_id = (); leaf_index = ();}) /\
    (ps_leaf_node_data_nt tkt).is_valid (is_msg gu label time) ln_data /\
    is_valid gu time sk /\ get_usage gu sk == Some (sig_usage "MLS.LeafSignKey") /\
    is_valid gu time nonce /\
    get_label gu sk == readers [p_id prin] /\
    get_label gu nonce == readers [p_id prin] /\
    has_leaf_node_tbs_invariant tkt gu
  )
  (ensures value_has_pre (is_msg gu label time) (sign_leaf_node_data_key_package ln_data sk nonce))
let is_msg_sign_leaf_node_data_key_package #tkt gu prin label time ln_data sk nonce =
  let ln_tbs: leaf_node_tbs_nt dy_bytes tkt = ({data = ln_data; group_id = (); leaf_index = ();}) in
  let ln_tbs_bytes: dy_bytes = serialize _ ln_tbs in
  parse_serialize_inv_lemma #dy_bytes (leaf_node_tbs_nt dy_bytes tkt) ln_tbs;
  serialize_pre_lemma (leaf_node_tbs_nt dy_bytes tkt) (is_msg gu label time) ln_tbs;
  sign_with_label_valid gu (leaf_node_spred gu.key_usages tkt) "MLS.LeafSignKey" time sk "LeafNodeTBS" ln_tbs_bytes nonce

#push-options "--z3rlimit 25"
val is_msg_sign_leaf_node_data_update:
  #tkt:treekem_types dy_bytes ->
  gu:global_usage -> prin:principal -> label:label -> time:timestamp ->
  ln_data:leaf_node_data_nt dy_bytes tkt -> group_id:mls_bytes dy_bytes -> leaf_index:nat_lbytes 4 ->
  sk:sign_private_key dy_bytes -> nonce:sign_nonce dy_bytes ->
  Lemma
  (requires
    ln_data.source == LNS_update () /\
    sign_leaf_node_data_update_pre ln_data group_id /\
    leaf_node_has_event prin time ({data = ln_data; group_id; leaf_index;}) /\
    tree_has_event prin time group_id (|0, (leaf_index <: nat), TLeaf (Some ({data = ln_data; signature = empty #dy_bytes;} <: leaf_node_nt dy_bytes tkt))|) /\
    (ps_leaf_node_data_nt tkt).is_valid (is_msg gu label time) ln_data /\
    is_msg gu label time group_id /\
    is_valid gu time sk /\ get_usage gu sk == Some (sig_usage "MLS.LeafSignKey") /\
    is_valid gu time nonce /\
    get_label gu sk == readers [p_id prin] /\
    get_label gu nonce == readers [p_id prin] /\
    has_leaf_node_tbs_invariant tkt gu
  )
  (ensures value_has_pre (is_msg gu label time) (sign_leaf_node_data_update ln_data group_id leaf_index sk nonce))
let is_msg_sign_leaf_node_data_update #tkt gu prin label time ln_data group_id leaf_index sk nonce =
  let ln_tbs: leaf_node_tbs_nt dy_bytes tkt = ({data = ln_data; group_id; leaf_index;}) in
  let ln_tbs_bytes: dy_bytes = serialize _ ln_tbs in
  parse_serialize_inv_lemma #dy_bytes (leaf_node_tbs_nt dy_bytes tkt) ln_tbs;
  serialize_pre_lemma (leaf_node_tbs_nt dy_bytes tkt) (is_msg gu label time) ln_tbs;
  LabeledCryptoAPI.vk_lemma #gu #time #(readers [p_id prin]) sk;
  sign_with_label_valid gu (leaf_node_spred gu.key_usages tkt) "MLS.LeafSignKey" time sk "LeafNodeTBS" ln_tbs_bytes nonce
#pop-options
