module MLS.TreeSync.Symbolic.LeafNodeSignature

open FStar.Mul
open Comparse
open DY.Core
open DY.Lib
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
open MLS.TreeSync.Symbolic.IsWellFormed
open MLS.TreeSync.Symbolic.Parsers
open MLS.TreeSync.Symbolic.AuthService
open MLS.TreeSync.Symbolic.AuthService.CredentialInterpretation
open MLS.TreeSync.Symbolic.State.SignatureKey
open MLS.Crypto.Derived.Symbolic.SignWithLabel
open MLS.Symbolic
open MLS.Result

#set-options "--fuel 1 --ifuel 1"

(*** Predicates ***)

[@@ with_bytes bytes]
type leaf_node_signed_event (tkt:treekem_types bytes) = {
  ln_tbs: leaf_node_tbs_nt bytes tkt;
}

%splice [ps_leaf_node_signed_event] (gen_parser (`leaf_node_signed_event))

instance event_leaf_node_signed_event (tkt:treekem_types bytes): event (leaf_node_signed_event tkt) = {
  tag = "MLS.TreeSync.LeafNodeSigned";
  format = mk_parseable_serializeable (ps_leaf_node_signed_event tkt);
}

val leaf_node_has_event:
  #tkt:treekem_types bytes ->
  principal -> trace -> leaf_node_tbs_nt bytes tkt ->
  prop
let leaf_node_has_event #tkt prin tr ln_tbs =
  event_triggered tr prin { ln_tbs }

type group_has_tree_event (bytes:Type0) {|bytes_like bytes|} (tkt:treekem_types bytes) = {
  group_id: mls_bytes bytes;
  authentifier_leaf_index: nat;
  [@@@ with_parser #bytes ps_nat]
  l: nat;
  [@@@ with_parser #bytes ps_nat]
  i: nat;
  [@@@ with_parser #bytes (ps_treesync tkt l (i*(pow2 l)))]
  t: treesync bytes tkt l (i*(pow2 l));
}

%splice [ps_group_has_tree_event] (gen_parser (`group_has_tree_event))

#push-options "--z3cliopt smt.arith.nl=false"
val tree_has_event_arithmetic_lemma:
  l:nat -> i:tree_index l ->
  Lemma
  ((i/(pow2 l))*(pow2 l) == i)
let tree_has_event_arithmetic_lemma l i =
  eliminate exists (k:nat). i = k*(pow2 l)
  returns (i/(pow2 l))*(pow2 l) == i
  with _. (
    FStar.Math.Lemmas.cancel_mul_div k (pow2 l)
  )
#pop-options

instance event_group_has_tree_event (tkt:treekem_types bytes): event (group_has_tree_event bytes tkt) = {
  tag = "MLS.TreeSync.GroupHasTreeEvent";
  format = mk_parseable_serializeable (ps_group_has_tree_event tkt);
}

val mk_group_has_tree_event:
  #tkt:treekem_types bytes ->
  mls_bytes bytes -> nat -> (l:nat & i:tree_index l & treesync bytes tkt l i) ->
  group_has_tree_event bytes tkt
let mk_group_has_tree_event #tkt group_id authentifier_leaf_index (|l, i, t|) =
  tree_has_event_arithmetic_lemma l i;
  {
    group_id;
    authentifier_leaf_index;
    l;
    i = i/(pow2 l);
    t;
  }

val tree_has_event:
  #tkt:treekem_types bytes ->
  principal -> trace ->
  mls_bytes bytes -> nat -> (l:nat & i:tree_index l & treesync bytes tkt l i) ->
  prop
let tree_has_event #tkt prin tr group_id authentifier_leaf_index (|l, i, t|) =
  event_triggered tr prin (mk_group_has_tree_event group_id authentifier_leaf_index (|l, i, t|))

val tree_list_has_event:
  #tkt:treekem_types bytes ->
  principal -> trace ->
  mls_bytes bytes -> nat -> tree_list bytes tkt ->
  prop
let tree_list_has_event #tkt prin tr group_id authentifier_leaf_index tl =
  for_allP (tree_has_event prin tr group_id authentifier_leaf_index) tl

val leaf_node_label: string
let leaf_node_label = "LeafNodeTBS"

/// The leaf node signature predicate.
/// When signing its leaf node for a Commit,
/// the leaf attests the existence of a tree list,
/// that is parent-hash linked and goes up to the root,
/// furthermore one event "GroupHasTreeEvent" was triggered for each of these trees.
#push-options "--fuel 0 --z3rlimit 25"
val leaf_node_sign_pred:
  {|crypto_usages|} -> treekem_types bytes ->
  signwithlabel_crypto_pred
let leaf_node_sign_pred #cu tkt = {
  pred = (fun tr sk_usg vk ln_tbs_bytes ->
    match (parse (leaf_node_tbs_nt bytes tkt) ln_tbs_bytes) with
    | None -> False
    | Some ln_tbs -> (
      exists prin.
        sk_usg == mk_mls_sigkey_usage prin /\
        leaf_node_has_event prin tr ln_tbs /\ (
        match ln_tbs.data.source with
        | LNS_commit -> (
          exists (tl: tree_list bytes tkt).
            tree_list_starts_with_tbs tl ln_tbs_bytes /\
            tree_list_is_parent_hash_linkedP tl /\
            tree_list_ends_at_root tl /\
            tree_list_is_canonicalized ln_tbs.leaf_index tl /\
            tree_list_has_event prin tr ln_tbs.group_id ln_tbs.leaf_index tl
        )
        | LNS_update -> (
          tree_has_event prin tr ln_tbs.group_id ln_tbs.leaf_index (|0, ln_tbs.leaf_index, TLeaf (Some ({data = ln_tbs.data; signature = empty #bytes;} <: leaf_node_nt bytes tkt))|)
        )
        | LNS_key_package -> True
        )
    )
  );
  pred_later = (fun tr1 tr2 sk_usg vk ln_tbs_bytes ->
    parse_wf_lemma (leaf_node_tbs_nt bytes tkt) (bytes_well_formed tr1) ln_tbs_bytes;
    introduce forall prin tr group_id authentifier_leaf_index (tl:tree_list bytes tkt). tree_list_has_event prin tr group_id authentifier_leaf_index tl <==> (forall x. List.Tot.memP x tl ==> tree_has_event prin tr group_id authentifier_leaf_index x)
    with (
      for_allP_eq (tree_has_event prin tr group_id authentifier_leaf_index) tl
    )
  );
}
#pop-options

val leaf_node_tbs_tag_and_invariant: {|crypto_usages|} -> treekem_types bytes -> (valid_label & signwithlabel_crypto_pred)
let leaf_node_tbs_tag_and_invariant #cu tkt = (leaf_node_label, leaf_node_sign_pred tkt)

val has_leaf_node_tbs_invariant:
  treekem_types bytes -> {|crypto_invariants|} ->
  prop
let has_leaf_node_tbs_invariant tkt #ci =
  has_mls_signwithlabel_pred (leaf_node_tbs_tag_and_invariant tkt)

(*** Proof of verification, for a tree ***)

#push-options "--fuel 2 --ifuel 1 --z3rlimit 25"
val last_tree_equivalent:
  #bytes:eqtype -> {|bytes_like bytes|} -> #tkt:treekem_types bytes ->
  tl1:tree_list bytes tkt -> tl2:tree_list bytes tkt -> li:nat ->
  Lemma
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

val tree_list_head_subtree_tail:
  #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes ->
  tl:tree_list bytes tkt ->
  Lemma
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

val get_authentifier_index:
  #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes ->
  #l:nat -> #i:tree_index l ->
  t:treesync bytes tkt l i ->
  Pure (leaf_index l i)
  (requires
    unmerged_leaves_ok t /\
    parent_hash_invariant t /\
    node_not_blank t
  )
  (ensures fun res -> Some? (leaf_at t res))
let get_authentifier_index #bytes #cb #tkt #l #i t =
  if l = 0 then i
  else (
    let my_tl = parent_hash_invariant_to_tree_list t in
    let (|leaf_l, leaf_i, leaf|) = List.Tot.hd my_tl in
    tree_list_head_subtree_tail my_tl;
    leaf_at_subtree_leaf leaf t;
    leaf_i
  )

val leaf_at_valid_leaves:
  #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes ->
  #l:nat -> #i:tree_index l ->
  group_id:mls_bytes bytes -> t:treesync bytes tkt l i -> li:leaf_index l i ->
  Lemma
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

val is_well_formed_leaf_at:
  #bytes:Type0 -> {|bytes_like bytes|} -> #tkt:treekem_types bytes ->
  #l:nat -> #i:tree_index l ->
  pre:bytes_compatible_pre bytes -> t:treesync bytes tkt l i -> li:leaf_index l i ->
  Lemma
  (requires is_well_formed _ pre t)
  (ensures (
    match leaf_at t li with
    | None -> True
    | Some ln -> is_well_formed _ pre ln
  ))
let rec is_well_formed_leaf_at #bytes #bl #tkt #l #i pre t li =
  match t with
  | TLeaf _ -> ()
  | TNode _ _ _ ->
    let (child, _) = get_child_sibling t li in
    is_well_formed_leaf_at pre child li

/// When a tree satisfy all the invariants,
/// then there exists a leaf inside that authenticates it:
/// - either the principal at the leaf triggered an event saying it saw the tree in the group,
/// - or the principal at the leaf is corrupt.
/// The proof works by obtaining a tree list `my_tl` from the parent-hash invariant,
/// obtaining another tree list `leaf_tl` from the signature predicate.
/// Then, using the parent-hash integrity theorem `parent_hash_guarantee_theorem`,
/// we conclude.
#push-options "--z3rlimit 100"
val parent_hash_implies_event:
  {|crypto_invariants|} ->
  #tkt:treekem_types bytes ->
  #l:nat -> #i:tree_index l ->
  tr:trace ->
  group_id:mls_bytes bytes -> t:treesync bytes tkt l i -> authentifier_token:(dy_asp tr).token_t ->
  Lemma
  (requires
    has_leaf_node_tbs_invariant tkt /\
    unmerged_leaves_ok t /\
    parent_hash_invariant t /\
    valid_leaves_invariant group_id t /\
    node_has_parent_hash t /\
    (dy_asp tr).credential_ok (leaf_node_to_as_input (Some?.v (leaf_at t (get_authentifier_index t)))) authentifier_token /\
    is_well_formed _ (bytes_invariant tr) (Some?.v (leaf_at t (get_authentifier_index t))) /\
    bytes_invariant tr group_id
  )
  (ensures (
    let authentifier_li = get_authentifier_index t in
    let authentifier_leaf_node = Some?.v (leaf_at t authentifier_li) in
    let authentifier = Some?.v (credential_to_principal authentifier_leaf_node.data.credential) in
    let authentifier_signature_key = authentifier_leaf_node.data.signature_key in
    (
      tree_has_event authentifier tr group_id authentifier_li (|l, i, (canonicalize t authentifier_li)|)
    ) \/ (
      is_corrupt tr (signature_key_label authentifier authentifier_signature_key)
    )
  ))
let parent_hash_implies_event #ci #tkt #l #i tr group_id t authentifier_token =
  let my_tl = parent_hash_invariant_to_tree_list t in
  let (|leaf_l, leaf_i, leaf|) = List.Tot.hd my_tl in
  tree_list_head_subtree_tail my_tl;
  leaf_at_subtree_leaf leaf t;
  leaf_at_valid_leaves group_id t leaf_i;
  let TLeaf (Some ln) = leaf in
  let ln_tbs: leaf_node_tbs_nt bytes tkt = {
    data = ln.data;
    group_id = group_id;
    leaf_index = leaf_i;
  } in
  let ln_tbs_bytes = get_leaf_tbs ln group_id leaf_i in
  let leaf_token = authentifier_token in
  let authentifier_li = leaf_i in
  let authentifier = (Some?.v (credential_to_principal (Some?.v (leaf_at t authentifier_li)).data.credential)) in
  let leaf_sk_label = principal_label authentifier in
  serialize_wf_lemma (leaf_node_tbs_nt bytes tkt) (bytes_invariant tr) ln_tbs;
  bytes_invariant_verify_with_label (leaf_node_sign_pred  tkt) tr authentifier ln.data.signature_key "LeafNodeTBS" ln_tbs_bytes ln.signature;

  introduce ((leaf_node_sign_pred tkt).pred tr (mk_mls_sigkey_usage authentifier) ln.data.signature_key ln_tbs_bytes) ==> tree_has_event authentifier tr group_id authentifier_li (|l, i, (canonicalize t authentifier_li)|)
  with _. (
    parse_serialize_inv_lemma #bytes (leaf_node_tbs_nt bytes tkt) ln_tbs;
    eliminate exists (leaf_tl: tree_list bytes tkt).
      tree_list_starts_with_tbs leaf_tl ln_tbs_bytes /\
      tree_list_is_parent_hash_linkedP leaf_tl /\
      tree_list_ends_at_root leaf_tl /\
      tree_list_is_canonicalized authentifier_li leaf_tl /\
      tree_list_has_event authentifier tr ln_tbs.group_id authentifier_li leaf_tl
    returns tree_has_event authentifier tr group_id authentifier_li (|l, i, (canonicalize t authentifier_li)|)
    with _. (
      let (b1, b2) = parent_hash_guarantee_theorem my_tl leaf_tl ln_tbs_bytes in
      FStar.Classical.move_requires_2 hash_injective b1 b2;
      last_tree_equivalent my_tl leaf_tl leaf_i;
      for_allP_eq (tree_has_event authentifier tr group_id authentifier_li) leaf_tl;
      let (|_, _, original_t|) = List.Tot.index leaf_tl (List.Tot.length my_tl - 1) in
      List.Tot.lemma_index_memP leaf_tl (List.Tot.length my_tl - 1);
      for_allP_eq (tree_is_canonicalized authentifier_li) leaf_tl;
      canonicalize_idempotent original_t authentifier_li
    )
  )
#pop-options

#push-options "--z3rlimit 25"
val leaf_node_source_update_implies_event:
  {|crypto_invariants|} ->
  #tkt:treekem_types bytes ->
  tr:trace ->
  ln:leaf_node_nt bytes tkt -> group_id:mls_bytes bytes -> li:nat -> leaf_token:(dy_asp tr).token_t ->
  Lemma
  (requires
    ln.data.source == LNS_update /\
    leaf_is_valid ln group_id li /\
    (dy_asp tr).credential_ok (leaf_node_to_as_input ln) leaf_token /\
    is_well_formed _ (bytes_invariant tr) ln /\
    bytes_invariant tr group_id /\
    has_leaf_node_tbs_invariant tkt
  )
  (ensures (
    let prin = Some?.v (credential_to_principal ln.data.credential) in
    let signature_key = ln.data.signature_key in
    (
      tree_has_event prin tr group_id li (|0, li, canonicalize (TLeaf (Some ln)) li|)
    ) \/ (
      is_corrupt tr (signature_key_label prin signature_key)
    )
  ))
let leaf_node_source_update_implies_event #ci #tkt tr ln group_id li leaf_token =
  let prin = Some?.v (credential_to_principal ln.data.credential) in
  let ln_tbs: leaf_node_tbs_nt bytes tkt = {
    data = ln.data;
    group_id = group_id;
    leaf_index = li;
  } in
  let ln_tbs_bytes = get_leaf_tbs ln group_id li in
  parse_serialize_inv_lemma #bytes (leaf_node_tbs_nt bytes tkt) ln_tbs;
  serialize_wf_lemma (leaf_node_tbs_nt bytes tkt) (bytes_invariant tr) ln_tbs;
  bytes_invariant_verify_with_label (leaf_node_sign_pred tkt) tr prin ln.data.signature_key "LeafNodeTBS" ln_tbs_bytes ln.signature
#pop-options

val leaf_node_source_key_package_implies_event:
  {|crypto_invariants|} ->
  #tkt:treekem_types bytes ->
  tr:trace ->
  ln:leaf_node_nt bytes tkt -> group_id:mls_bytes bytes -> li:nat -> leaf_token:(dy_asp tr).token_t ->
  Lemma
  (requires
    ln.data.source == LNS_key_package /\
    leaf_is_valid ln group_id li /\
    (dy_asp tr).credential_ok (leaf_node_to_as_input ln) leaf_token /\
    is_well_formed _ (bytes_invariant tr) ln /\
    bytes_invariant tr group_id /\
    has_leaf_node_tbs_invariant tkt
  )
  (ensures (
    let prin = Some?.v (credential_to_principal ln.data.credential) in
    let signature_key = ln.data.signature_key in
    (
      leaf_node_has_event prin tr { data = ln.data; group_id = (); leaf_index = (); }
    ) \/ (
      is_corrupt tr (signature_key_label prin signature_key)
    )
  ))
let leaf_node_source_key_package_implies_event #ci #tkt tr ln group_id li leaf_token =
  let prin = Some?.v (credential_to_principal ln.data.credential) in
  let ln_tbs: leaf_node_tbs_nt bytes tkt = {
    data = ln.data;
    group_id = ();
    leaf_index = ();
  } in
  let ln_tbs_bytes = get_leaf_tbs ln group_id li in
  parse_serialize_inv_lemma #bytes (leaf_node_tbs_nt bytes tkt) ln_tbs;
  serialize_wf_lemma (leaf_node_tbs_nt bytes tkt) (bytes_invariant tr) ln_tbs;
  bytes_invariant_verify_with_label (leaf_node_sign_pred tkt) tr prin ln.data.signature_key "LeafNodeTBS" ln_tbs_bytes ln.signature

(*** Proof of verification, for a state ***)

val valid_leaves_invariant_subtree:
  #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes ->
  #lp:nat -> #ld:nat -> #ip:tree_index lp -> #id:tree_index ld ->
  group_id:mls_bytes bytes -> d:treesync bytes tkt ld id -> p:treesync bytes tkt lp ip ->
  Lemma
  (requires valid_leaves_invariant group_id p /\ is_subtree_of d p)
  (ensures valid_leaves_invariant group_id d)
let rec valid_leaves_invariant_subtree #bytes #cb #tkt #lp #ld #ip #id group_id d p =
  if ld = lp then ()
  else (
    let (c,  _) = get_child_sibling p id in
    valid_leaves_invariant_subtree group_id d c
  )

val is_well_formed_treesync_subtree:
  #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes ->
  #lp:nat -> #ld:nat -> #ip:tree_index lp -> #id:tree_index ld ->
  pre:bytes_compatible_pre bytes -> d:treesync bytes tkt ld id -> p:treesync bytes tkt lp ip ->
  Lemma
  (requires is_well_formed _ pre p /\ is_subtree_of d p)
  (ensures is_well_formed _ pre d)
let rec is_well_formed_treesync_subtree #bytes #cb #tkt #lp #ld #ip #id pre d p =
  if ld = lp then ()
  else (
    let (c,  _) = get_child_sibling p id in
    is_well_formed_treesync_subtree pre d c
  )

val all_credentials_ok_subtree:
  #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes -> #asp:as_parameters bytes ->
  #lp:nat -> #ld:nat -> #ip:tree_index lp -> #id:tree_index ld ->
  d:treesync bytes tkt ld id -> p:treesync bytes tkt lp ip ->
  ast_d:as_tokens bytes asp.token_t ld id -> ast_p:as_tokens bytes asp.token_t lp ip ->
  Lemma
  (requires
    all_credentials_ok p ast_p /\
    is_subtree_of d p /\
    is_subtree_of ast_d ast_p
  )
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

/// If a TreeSync state contains a subtree,
/// then there exists a leaf inside that authenticates it:
/// - either the principal at the leaf triggered an event saying it saw the subtree in the group,
/// - or the principal at the leaf is corrupt.
/// This theorem is mostly a wrapper around `parent_hash_implies_event`.
val state_implies_event:
  {|crypto_invariants|} ->
  #tkt:treekem_types bytes -> #group_id:mls_bytes bytes -> #l:nat -> #i:tree_index l ->
  tr:trace ->
  st:treesync_state bytes tkt dy_as_token group_id -> t:treesync bytes tkt l i -> ast:as_tokens bytes (dy_asp tr).token_t l i ->
  Lemma
  (requires
    has_leaf_node_tbs_invariant tkt /\
    node_has_parent_hash t /\
    is_well_formed _ (bytes_invariant tr) (st.tree <: treesync _ _ _ _) /\
    bytes_invariant tr group_id /\
    is_subtree_of t st.tree /\
    is_subtree_of ast st.tokens /\
    treesync_state_valid (dy_asp tr) st
  )
  (ensures (
    // The following line is only there as precondition for the rest of the theorem
    unmerged_leaves_ok t /\ parent_hash_invariant t /\ all_credentials_ok t ast /\ (
      let authentifier_li = get_authentifier_index t in
      let authentifier_leaf_node = Some?.v (leaf_at t authentifier_li) in
      let authentifier = Some?.v (credential_to_principal authentifier_leaf_node.data.credential) in
      let authentifier_signature_key = authentifier_leaf_node.data.signature_key in
      (
        tree_has_event authentifier tr group_id authentifier_li (|l, i, (canonicalize t authentifier_li)|)
      ) \/ (
        is_corrupt tr (signature_key_label authentifier authentifier_signature_key)
      )
    )
  ))
let state_implies_event #ci #tkt #group_id #l #i tr st t ast =
  unmerged_leaves_ok_subtree t st.tree;
  parent_hash_invariant_subtree t st.tree;
  valid_leaves_invariant_subtree group_id t st.tree;
  is_well_formed_treesync_subtree (bytes_invariant tr) t st.tree;
  all_credentials_ok_subtree t st.tree ast st.tokens;
  is_well_formed_leaf_at (bytes_invariant tr) t (get_authentifier_index t);
  let authentifier_li = get_authentifier_index t in
  parent_hash_implies_event tr group_id t (Some?.v (leaf_at ast authentifier_li))

(*** Proof of path signature ***)

val external_path_to_path_aux_nosig:
  #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes ->
  #l:nat -> #i:tree_index l -> #li:leaf_index l i ->
  t:treesync bytes tkt l i -> p:external_pathsync bytes tkt l i li{(get_path_leaf p).source == LNS_update} -> group_id:mls_bytes bytes ->
  result (leaf_node_nt bytes tkt)
let external_path_to_path_aux_nosig #bytes #cb #tkt #l #i #li t p group_id =
  let? computed_parent_hash = compute_leaf_parent_hash_from_path t p (root_parent_hash #bytes) in
  let? computed_parent_hash = mk_mls_bytes computed_parent_hash "external_path_to_path_aux_nosig" "computed_parent_hash" in
  let lp = get_path_leaf p in
  let new_lp_data = { lp with source = LNS_commit; parent_hash = computed_parent_hash; } in
  return ({ data = new_lp_data; signature = empty #bytes } <: leaf_node_nt bytes tkt)

val external_path_to_path_nosig:
  #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes ->
  #l:nat -> #i:tree_index l -> #li:leaf_index l i ->
  t:treesync bytes tkt l i -> p:external_pathsync bytes tkt l i li{(get_path_leaf p).source == LNS_update} -> group_id:mls_bytes bytes ->
  result (pathsync bytes tkt l i li)
let external_path_to_path_nosig #bytes #cb #tkt #l #i #li t p group_id =
  let? new_leaf_node = external_path_to_path_aux_nosig t p group_id in
  return (set_path_leaf p new_leaf_node)

val get_path_leaf_set_path_leaf:
  #bytes:Type0 -> {|bytes_like bytes|} -> #tkt:treekem_types bytes ->
  #l:nat -> #i:tree_index l -> #li:leaf_index l i ->
  p:external_pathsync bytes tkt l i li -> ln:leaf_node_nt bytes tkt ->
  Lemma
  (get_path_leaf (set_path_leaf p ln) == ln)
let rec get_path_leaf_set_path_leaf #bytes #bl #tkt #l #i #li p ln =
  match p with
  | PLeaf _ -> ()
  | PNode _ p_next -> get_path_leaf_set_path_leaf p_next ln

val compute_leaf_parent_hash_from_path_set_path_leaf:
  #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes ->
  #l:nat -> #i:tree_index l -> #li:leaf_index l i ->
  t:treesync bytes tkt l i -> p:external_pathsync bytes tkt l i li -> ln:leaf_node_nt bytes tkt -> parent_parent_hash:bytes ->
  Lemma
  (ensures
    compute_leaf_parent_hash_from_path t (set_path_leaf p ln) parent_parent_hash == compute_leaf_parent_hash_from_path t p parent_parent_hash
  )
let rec compute_leaf_parent_hash_from_path_set_path_leaf #bytes #cb #tkt #l #i #li t p ln parent_parent_hash =
  match t, p with
  | TLeaf _, PLeaf _ -> ()
  | TNode _ left right, PNode opt_ext_content p_next ->
    let (child, sibling) = get_child_sibling t li in
    match compute_new_np_and_ph opt_ext_content sibling parent_parent_hash with
    | Success (_,  new_parent_parent_hash) ->
      compute_leaf_parent_hash_from_path_set_path_leaf child p_next ln new_parent_parent_hash
    | _ -> ()

#push-options "--z3rlimit 25"
val path_is_parent_hash_valid_external_path_to_path_nosig:
  #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes ->
  #l:nat -> #li:leaf_index l 0 ->
  t:treesync bytes tkt l 0 -> p:external_pathsync bytes tkt l 0 li -> group_id:mls_bytes bytes ->
  Lemma
  (requires
    (get_path_leaf p).source == LNS_update /\
    Success? (external_path_to_path_nosig t p group_id)
  )
  (ensures path_is_parent_hash_valid t (Success?.v (external_path_to_path_nosig t p group_id)))
let path_is_parent_hash_valid_external_path_to_path_nosig #bytes #cb #tkt #l #li t p group_id =
  let Success new_lp = external_path_to_path_aux_nosig t p group_id in
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

val path_is_filter_valid_set_path_leaf:
  #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes ->
  #l:nat -> #i:tree_index l -> #li:leaf_index l i ->
  t:treesync bytes tkt l i -> p:external_pathsync bytes tkt l i li -> ln:leaf_node_nt bytes tkt ->
  Lemma
  (requires path_is_filter_valid t p)
  (ensures path_is_filter_valid t (set_path_leaf p ln))
let rec path_is_filter_valid_set_path_leaf #bytes #cb #tkt #l #i #li t p ln =
  match t, p with
  | TLeaf _, PLeaf _ -> ()
  | TNode _ _ _, PNode _ p_next ->
    let (child, _) = get_child_sibling t li in
    path_is_filter_valid_set_path_leaf child p_next ln

#push-options "--z3rlimit 25"
val path_is_filter_valid_external_path_to_path_nosig:
  #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes ->
  #l:nat -> #li:leaf_index l 0 ->
  t:treesync bytes tkt l 0 -> p:external_pathsync bytes tkt l 0 li -> group_id:mls_bytes bytes ->
  Lemma
  (requires
    (get_path_leaf p).source == LNS_update /\
    Success? (external_path_to_path_nosig t p group_id) /\
    path_is_filter_valid t p
  )
  (ensures path_is_filter_valid t (Success?.v (external_path_to_path_nosig t p group_id)))
let path_is_filter_valid_external_path_to_path_nosig #bytes #cb #tkt #l #li t p group_id =
  let Success new_lp = external_path_to_path_aux_nosig t p group_id in
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

val apply_path_aux_compute_leaf_parent_hash_from_path_both_succeed:
  #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes ->
  #l:nat -> #i:tree_index l -> #li:leaf_index l i ->
  t:treesync bytes tkt l i -> p:pathsync bytes tkt l i li -> parent_parent_hash:bytes ->
  Lemma
  (Success? (apply_path_aux t p parent_parent_hash) <==> Success? (compute_leaf_parent_hash_from_path t p parent_parent_hash))
let rec apply_path_aux_compute_leaf_parent_hash_from_path_both_succeed #bytes #cb #tkt #l #i #li t p parent_parent_hash =
  match t, p with
  | TLeaf old_lp, PLeaf new_lp -> ()
  | TNode _ left right, PNode opt_ext_content p_next ->
    let (child, sibling) = get_child_sibling t li in
    match compute_new_np_and_ph opt_ext_content sibling parent_parent_hash with
    | Success (_,  new_parent_parent_hash) ->
      apply_path_aux_compute_leaf_parent_hash_from_path_both_succeed child p_next new_parent_parent_hash
    | _ -> ()

val external_path_has_event:
  #tkt:treekem_types bytes ->
  #l:nat -> #li:leaf_index l 0 ->
  prin:principal -> tr:trace ->
  t:treesync bytes tkt l 0 -> p:external_pathsync bytes tkt l 0 li -> group_id:mls_bytes bytes ->
  prop
let external_path_has_event #tkt #l #li prin tr t p group_id =
  (get_path_leaf p).source == LNS_update /\
  li < pow2 32 /\
  Success? (external_path_to_path_nosig t p group_id) /\ (
    //This lemma is useful to know that auth_ln.data.source == LNS_commit
    path_is_parent_hash_valid_external_path_to_path_nosig t p group_id;
    let Success auth_p = external_path_to_path_nosig t p group_id in
    let auth_ln = get_path_leaf auth_p in
    compute_leaf_parent_hash_from_path_set_path_leaf t p auth_ln (root_parent_hash #bytes);
    apply_path_aux_compute_leaf_parent_hash_from_path_both_succeed t auth_p (root_parent_hash #bytes);
    leaf_node_has_event prin tr ({data = auth_ln.data; group_id; leaf_index = li;}) /\
    tree_list_has_event prin tr group_id li (path_to_tree_list t auth_p)
  )

/// Proof that the path generated by `external_path_to_path`
/// (the function in charge of computing the path leaf signature)
/// satisfies the signature predicate.
///
/// This theorem can be instantiated with various labels to prove more specific theorems.
/// With label = SecrecyLabels.public, we get a version with `is_publishable`.
/// With label= SecrecyLabels.private_label, we get a version with `is_valid`.
#push-options "--z3rlimit 100"
val is_msg_external_path_to_path:
  {|crypto_invariants|} ->
  #tkt:treekem_types bytes ->
  #l:nat -> #li:leaf_index l 0 ->
  prin:principal -> label:label -> tr:trace ->
  t:treesync bytes tkt l 0 -> p:external_pathsync bytes tkt l 0 li -> group_id:mls_bytes bytes ->
  sk:bytes -> nonce:sign_nonce bytes ->
  Lemma
  (requires
    (get_path_leaf p).source == LNS_update /\
    Success? (external_path_to_path t p group_id sk nonce) /\
    path_is_filter_valid t p /\
    unmerged_leaves_ok t /\
    external_path_has_event prin tr t p group_id /\
    is_well_formed _ (is_knowable_by label tr) t /\
    is_well_formed _ (is_knowable_by label tr) p /\
    is_knowable_by label tr group_id /\
    is_signature_key_sk tr prin sk /\
    bytes_invariant tr nonce /\ nonce `has_usage tr` SigNonce /\
    get_label tr sk `can_flow tr` get_label tr nonce /\
    has_leaf_node_tbs_invariant tkt
  )
  (ensures is_well_formed _ (is_knowable_by label tr) (Success?.v (external_path_to_path t p group_id sk nonce)))
let is_msg_external_path_to_path #ci #tkt #l #li prin label tr t p group_id sk nonce =
  let Success computed_parent_hash = compute_leaf_parent_hash_from_path t p (root_parent_hash #bytes) in
  let ln_data = get_path_leaf p in
  let new_ln_data = { ln_data with source = LNS_commit; parent_hash = computed_parent_hash; } in
  let new_ln_tbs: leaf_node_tbs_nt bytes tkt = ({data = new_ln_data; group_id; leaf_index = li;}) in
  let new_ln_tbs_bytes: bytes = serialize (leaf_node_tbs_nt bytes tkt) new_ln_tbs in
  let Success new_signature = sign_with_label sk "LeafNodeTBS" new_ln_tbs_bytes nonce in
  let new_ln = ({ data = new_ln_data; signature = new_signature; } <: leaf_node_nt bytes tkt) in
  let new_unsigned_ln = ({ data = new_ln_data; signature = empty #bytes; } <: leaf_node_nt bytes tkt) in
  let unsigned_path = set_path_leaf p new_unsigned_ln in
  compute_leaf_parent_hash_from_path_set_path_leaf t p new_unsigned_ln (root_parent_hash #bytes);
  apply_path_aux_compute_leaf_parent_hash_from_path_both_succeed t unsigned_path (root_parent_hash #bytes);
  path_is_parent_hash_valid_external_path_to_path_nosig t p group_id;
  path_is_filter_valid_external_path_to_path_nosig t p group_id;
  get_path_leaf_set_path_leaf p new_unsigned_ln;
  pre_compute_leaf_parent_hash_from_path (is_knowable_by label tr) t p (root_parent_hash #bytes);
  is_well_formed_get_path_leaf (is_knowable_by label tr) p;
  serialize_wf_lemma (leaf_node_tbs_nt bytes tkt) (is_knowable_by label tr) ({data = new_ln_data; group_id; leaf_index = li;});
  path_to_tree_list_lemma t unsigned_path;
  parse_serialize_inv_lemma #bytes (leaf_node_tbs_nt bytes tkt) new_ln_tbs;
  bytes_invariant_sign_with_label (leaf_node_sign_pred tkt) tr prin sk "LeafNodeTBS" new_ln_tbs_bytes nonce;
  is_well_formed_set_path_leaf (is_knowable_by label tr) p new_ln
#pop-options

(*** Proof of individual leaf signature ***)

#push-options "--z3rlimit 25"
val is_msg_sign_leaf_node_data_key_package:
  {|crypto_invariants|} ->
  #tkt:treekem_types bytes ->
  prin:principal -> label:label -> tr:trace ->
  ln_data:leaf_node_data_nt bytes tkt ->
  sk:bytes -> nonce:sign_nonce bytes ->
  Lemma
  (requires
    ln_data.source == LNS_key_package /\
    Success? (sign_leaf_node_data_key_package ln_data sk nonce) /\
    leaf_node_has_event prin tr ({data = ln_data; group_id = (); leaf_index = ();}) /\
    is_well_formed_prefix (ps_leaf_node_data_nt tkt) (is_knowable_by label tr) ln_data /\
    is_signature_key_sk tr prin sk /\
    bytes_invariant tr nonce /\ nonce `has_usage tr` SigNonce /\
    get_label tr sk `can_flow tr` get_label tr nonce /\
    has_leaf_node_tbs_invariant tkt
  )
  (ensures is_well_formed _ (is_knowable_by label tr) (Success?.v (sign_leaf_node_data_key_package ln_data sk nonce)))
let is_msg_sign_leaf_node_data_key_package #ci #tkt prin label tr ln_data sk nonce =
  let ln_tbs: leaf_node_tbs_nt bytes tkt = ({data = ln_data; group_id = (); leaf_index = ();}) in
  let ln_tbs_bytes: bytes = serialize _ ln_tbs in
  parse_serialize_inv_lemma #bytes (leaf_node_tbs_nt bytes tkt) ln_tbs;
  serialize_wf_lemma (leaf_node_tbs_nt bytes tkt) (is_knowable_by label tr) ln_tbs;
  bytes_invariant_sign_with_label (leaf_node_sign_pred tkt) tr prin sk "LeafNodeTBS" ln_tbs_bytes nonce
#pop-options

#push-options "--z3rlimit 25"
val is_msg_sign_leaf_node_data_update:
  {|crypto_invariants|} ->
  #tkt:treekem_types bytes ->
  prin:principal -> label:label -> tr:trace ->
  ln_data:leaf_node_data_nt bytes tkt -> group_id:mls_bytes bytes -> leaf_index:nat_lbytes 4 ->
  sk:bytes -> nonce:sign_nonce bytes ->
  Lemma
  (requires
    ln_data.source == LNS_update /\
    Success? (sign_leaf_node_data_update ln_data group_id leaf_index sk nonce) /\
    leaf_node_has_event prin tr ({data = ln_data; group_id; leaf_index;}) /\
    tree_has_event prin tr group_id leaf_index (|0, (leaf_index <: nat), TLeaf (Some ({data = ln_data; signature = empty #bytes;} <: leaf_node_nt bytes tkt))|) /\
    is_well_formed_prefix (ps_leaf_node_data_nt tkt) (is_knowable_by label tr) ln_data /\
    is_knowable_by label tr group_id /\
    is_signature_key_sk tr prin sk /\
    bytes_invariant tr nonce /\ nonce `has_usage tr` SigNonce /\
    get_label tr sk `can_flow tr` get_label tr nonce /\
    has_leaf_node_tbs_invariant tkt
  )
  (ensures is_well_formed _ (is_knowable_by label tr) (Success?.v (sign_leaf_node_data_update ln_data group_id leaf_index sk nonce)))
let is_msg_sign_leaf_node_data_update #ci #tkt prin label tr ln_data group_id leaf_index sk nonce =
  let ln_tbs: leaf_node_tbs_nt bytes tkt = ({data = ln_data; group_id; leaf_index;}) in
  let ln_tbs_bytes: bytes = serialize _ ln_tbs in
  parse_serialize_inv_lemma #bytes (leaf_node_tbs_nt bytes tkt) ln_tbs;
  serialize_wf_lemma (leaf_node_tbs_nt bytes tkt) (is_knowable_by label tr) ln_tbs;
  bytes_invariant_sign_with_label (leaf_node_sign_pred tkt) tr prin sk "LeafNodeTBS" ln_tbs_bytes nonce
#pop-options
