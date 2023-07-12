module MLS.TreeKEM.Invariants.Proofs

open Comparse
open MLS.Crypto
open MLS.Tree
open MLS.TreeCommon
open MLS.NetworkTypes
open MLS.TreeKEM.Operations
open MLS.TreeKEM.Types
open MLS.TreeKEM.Invariants
open MLS.NetworkBinder.Properties
open MLS.TreeCommon.Lemmas
open MLS.MiscLemmas
open MLS.Result

#set-options "--fuel 1 --ifuel 1"

val is_tree_empty_un_add:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  #l:nat -> #i:tree_index l ->
  t:treekem bytes l i -> excluded_leaves:list nat ->
  Lemma
  (requires is_tree_empty t)
  (ensures is_tree_empty (un_add t excluded_leaves))
let rec is_tree_empty_un_add #bytes #cb #l #i t excluded_leaves =
  match t with
  | TLeaf _ -> ()
  | TNode _ left right ->
    is_tree_empty_un_add left excluded_leaves;
    is_tree_empty_un_add right excluded_leaves

val path_filtering_weak_ok_un_add:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  #l:nat -> #i:tree_index l -> #li:leaf_index l i ->
  t:treekem bytes l i -> p:pathkem bytes l i li ->
  excluded_leaves:list nat ->
  Lemma
  (requires path_filtering_weak_ok t p)
  (ensures path_filtering_weak_ok (un_add t excluded_leaves) p)
let rec path_filtering_weak_ok_un_add #bytes #cb #l #i #li t p excluded_leaves =
  match p with
  | PLeaf _ -> ()
  | PNode _ p_next ->
    let (child, sibling) = get_child_sibling t li in
    path_filtering_weak_ok_un_add child p_next excluded_leaves;
    FStar.Classical.move_requires_2 is_tree_empty_un_add sibling excluded_leaves

val weaken_path_filtering_ok:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  #l:nat -> #i:tree_index l -> #li:leaf_index l i ->
  t:treekem bytes l i -> p:pathkem bytes l i li ->
  Lemma
  (requires path_filtering_ok t p)
  (ensures path_filtering_weak_ok t p)
let rec weaken_path_filtering_ok #bytes #cb #l #i #li t p =
  match p with
  | PLeaf _ -> ()
  | PNode _ p_next ->
    let (child, _) = get_child_sibling t li in
    weaken_path_filtering_ok child p_next

(*** Extend invariants ***)

val treekem_invariant_mk_blank_tree:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  l:nat -> i:tree_index l ->
  Lemma (treekem_invariant #bytes (mk_blank_tree l i))
let rec treekem_invariant_mk_blank_tree #bytes #cb l i =
  if l = 0 then ()
  else (
    treekem_invariant_mk_blank_tree #bytes (l-1) (left_index i);
    treekem_invariant_mk_blank_tree #bytes (l-1) (right_index i)
  )

val treekem_invariant_extend:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  #l:nat ->
  t:treekem bytes l 0 ->
  Lemma
  (requires treekem_invariant t)
  (ensures treekem_invariant (tree_extend t))
let treekem_invariant_extend #bytes #cb #l t =
  treekem_invariant_mk_blank_tree #bytes l (right_index #(l+1) 0)

val treekem_priv_invariant_extend:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  #l:nat -> #li:leaf_index l 0 ->
  t:treekem bytes l 0 -> p:treekem_priv bytes l 0 li ->
  Lemma
  (requires treekem_priv_invariant t p)
  (ensures treekem_priv_invariant (tree_extend t) (path_extend p))
let treekem_priv_invariant_extend #bytes #cb #l #li t p = ()

(*** Truncate invariants ***)

val treekem_invariant_truncate:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  #l:pos ->
  t:treekem bytes l 0{is_tree_empty (TNode?.right t)} ->
  Lemma
  (requires treekem_invariant t)
  (ensures treekem_invariant (tree_truncate t))
let treekem_invariant_truncate #bytes #cb #l t = ()

val treekem_priv_invariant_truncate:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  #l:pos -> #li:leaf_index (l-1) 0 ->
  t:treekem bytes l 0{is_tree_empty (TNode?.right t)} -> p:treekem_priv bytes l 0 li ->
  Lemma
  (requires treekem_priv_invariant t p)
  (ensures treekem_priv_invariant (tree_truncate t) (path_truncate p))
let treekem_priv_invariant_truncate #bytes #cb #l #li t p = ()

(*** Add invariants ***)

val leaf_at_tree_add:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  #l:nat -> #i:tree_index l ->
  t:treekem bytes l i -> li:leaf_index l i -> lp:treekem_leaf bytes ->
  li':leaf_index l i ->
  Lemma
  (leaf_at (tree_add t li lp) li' == (if li = li' then Some lp else leaf_at t li'))
let rec leaf_at_tree_add #bytes #cb #l #i t li lp li' =
  match t with
  | TLeaf _ -> ()
  | TNode _ left right -> (
    match is_left_leaf li, is_left_leaf li' with
    | true, true -> leaf_at_tree_add left li lp li'
    | false, false -> leaf_at_tree_add right li lp li'
    | _, _ -> ()
  )

val treekem_invariant_add:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  #l:nat -> #i:tree_index l ->
  t:treekem bytes l i -> li:leaf_index l i -> lp:treekem_leaf bytes ->
  Lemma
  (requires treekem_invariant t)
  (ensures treekem_invariant (tree_add t li lp))
let rec treekem_invariant_add #bytes #cb #l #i t li lp =
  match t with
  | TLeaf _ -> ()
  | TNode opn _ _ -> (
    let (child, _) = get_child_sibling t li in
    treekem_invariant_add child li lp;
    match opn with
    | None -> ()
    | Some pn -> (
      Comparse.for_allP_eq (unmerged_leaf_exists t) pn.unmerged_leaves;
      Comparse.for_allP_eq (unmerged_leaf_exists (tree_add t li lp)) (insert_sorted li pn.unmerged_leaves);
      FStar.Classical.forall_intro (mem_insert_sorted li pn.unmerged_leaves);
      FStar.Classical.forall_intro (leaf_at_tree_add t li lp)
    )
  )

val treekem_priv_invariant_add:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  #l:nat -> #i:tree_index l -> #my_li:leaf_index l i ->
  t:treekem bytes l i -> p:treekem_priv bytes l i my_li -> li:leaf_index l i -> lp:treekem_leaf bytes ->
  Lemma
  (requires treekem_priv_invariant t p)
  (ensures treekem_priv_invariant (tree_add t li lp) p)
let treekem_priv_invariant_add #bytes #cb #l #i #my_li t p li lp =
  leaf_at_tree_add t li lp my_li

(*** Common Update/Remove invariants ***)

val treekem_invariant_change_path:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  #l:nat -> #i:tree_index l ->
  t:treekem bytes l i -> li:leaf_index l i -> content:option (treekem_leaf bytes) ->
  Lemma
  (requires treekem_invariant t)
  (ensures treekem_invariant (tree_change_path t li content None))
let rec treekem_invariant_change_path #bytes #cb #l #i t li content =
  match t with
  | TLeaf _ -> ()
  | TNode _ _ _ ->
    let (child, _) = get_child_sibling t li in
    treekem_invariant_change_path child li content

val treekem_priv_invariant_change_path:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  #l:nat -> #i:tree_index l -> #my_li:leaf_index l i ->
  t:treekem bytes l i -> p:treekem_priv bytes l i my_li -> li:leaf_index l i -> content:option (treekem_leaf bytes) ->
  Lemma
  (requires
    (li == my_li ==> Some? content) /\
    treekem_priv_invariant t p
  )
  (ensures treekem_priv_invariant (tree_change_path t li content None) p)
let rec treekem_priv_invariant_change_path #bytes #cb #l #i #my_li t p li content =
  match t, p with
  | TLeaf _, PLeaf _ -> ()
  | TNode _ _ _, PNode _ p_next -> (
    if is_left_leaf li = is_left_leaf my_li then (
      let (child, _) = get_child_sibling t li in
      treekem_priv_invariant_change_path child (p_next <: treekem_priv bytes (l-1) _ my_li) li content
    ) else ()
  )

(*** Update invariants ***)

val treekem_invariant_update:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  #l:nat -> #i:tree_index l ->
  t:treekem bytes l i -> li:leaf_index l i -> lp:treekem_leaf bytes ->
  Lemma
  (requires treekem_invariant t)
  (ensures treekem_invariant (tree_update t li lp))
let treekem_invariant_update #bytes #cb #l #i t li lp =
  treekem_invariant_change_path t li (Some lp)

val treekem_priv_invariant_update:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  #l:nat -> #i:tree_index l -> #my_li:leaf_index l i ->
  t:treekem bytes l i -> p:treekem_priv bytes l i my_li -> li:leaf_index l i -> lp:treekem_leaf bytes ->
  Lemma
  (requires treekem_priv_invariant t p)
  (ensures treekem_priv_invariant (tree_update t li lp) p)
let treekem_priv_invariant_update #bytes #cb #l #i #my_li t p li lp =
  treekem_priv_invariant_change_path t p li (Some lp)

(*** Remove invariants ***)

val treekem_invariant_remove:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  #l:nat -> #i:tree_index l ->
  t:treekem bytes l i -> li:leaf_index l i ->
  Lemma
  (requires treekem_invariant t)
  (ensures treekem_invariant (tree_remove t li))
let treekem_invariant_remove #bytes #cb #l #i t li =
  treekem_invariant_change_path t li None

val treekem_priv_invariant_remove:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  #l:nat -> #i:tree_index l -> #my_li:leaf_index l i ->
  t:treekem bytes l i -> p:treekem_priv bytes l i my_li -> li:leaf_index l i ->
  Lemma
  (requires
    my_li <> li /\
    treekem_priv_invariant t p
  )
  (ensures treekem_priv_invariant (tree_remove t li) p)
let treekem_priv_invariant_remove #bytes #cb #l #i #my_li t p li =
  treekem_priv_invariant_change_path t p li None

(*** Un-add invariants ***)

val unmerged_leaf_exists_un_add:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  #l:nat -> #i:tree_index l ->
  t:treekem bytes l i -> excluded_leaves:list nat ->
  x:nat ->
  Lemma
  (requires
    unmerged_leaf_exists t x /\
    ~(List.Tot.mem x excluded_leaves)
  )
  (ensures unmerged_leaf_exists (un_add t excluded_leaves) x)
let rec unmerged_leaf_exists_un_add #bytes #cb #l #i t excluded_leaves x =
  match t with
  | TLeaf _ -> ()
  | TNode _ left right -> (
    let x: leaf_index l i = x in
    if is_left_leaf x then (
      unmerged_leaf_exists_un_add left excluded_leaves x
    ) else (
      unmerged_leaf_exists_un_add right excluded_leaves x
    )
  )

val treekem_invariant_un_add:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  #l:nat -> #i:tree_index l ->
  t:treekem bytes l i -> excluded_leaves:list nat ->
  Lemma
  (requires treekem_invariant t)
  (ensures treekem_invariant (un_add t excluded_leaves))
let rec treekem_invariant_un_add #bytes #cb #l #i t excluded_leaves =
  match t with
  | TLeaf _ -> ()
  | TNode opn left right -> (
    treekem_invariant_un_add left excluded_leaves;
    treekem_invariant_un_add right excluded_leaves;
    match opn with
    | None -> ()
    | Some pn -> (
      Comparse.for_allP_eq (unmerged_leaf_exists t) pn.unmerged_leaves;
      Comparse.for_allP_eq (unmerged_leaf_exists (un_add t excluded_leaves)) (List.Tot.filter (excluded_pre excluded_leaves) pn.unmerged_leaves);
      FStar.Classical.forall_intro (mem_filter (excluded_pre excluded_leaves) pn.unmerged_leaves);
      FStar.Classical.forall_intro (FStar.Classical.move_requires (unmerged_leaf_exists_un_add t excluded_leaves))
    )
  )

val leaf_at_un_add:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  #l:nat -> #i:tree_index l ->
  t:treekem bytes l i -> excluded_leaves:list nat ->
  li:leaf_index l i ->
  Lemma (leaf_at (un_add t excluded_leaves) li = (if List.Tot.mem li excluded_leaves then None else leaf_at t li))
let rec leaf_at_un_add #bytes #cb #l #i t excluded_leaves li =
  match t with
  | TLeaf _ -> ()
  | TNode _ _ _ ->
    let (child, _) = get_child_sibling t li in
    leaf_at_un_add child excluded_leaves li

val treekem_priv_invariant_un_add:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  #l:nat -> #i:tree_index l -> #li:leaf_index l i ->
  t:treekem bytes l i -> p:treekem_priv bytes l i li -> excluded_leaves:list nat ->
  Lemma
  (requires
    ~(List.Tot.memP li excluded_leaves) /\
    treekem_priv_invariant t p
  )
  (ensures treekem_priv_invariant (un_add t excluded_leaves) p)
let treekem_priv_invariant_un_add #bytes #cb #l #i #li t p excluded_leaves =
  leaf_at_un_add t excluded_leaves li

(*** Apply path invariants ***)

val treekem_invariant_apply_path:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  #l:nat -> #i:tree_index l -> #li:leaf_index l i ->
  t:treekem bytes l i -> p:pathkem bytes l i li ->
  Lemma
  (requires treekem_invariant t)
  (ensures treekem_invariant (tree_apply_path t p))
let rec treekem_invariant_apply_path #bytes #cb #l #i #li t p =
  match t, p with
  | TLeaf _, PLeaf _ -> ()
  | TNode _ _ _, PNode _ p_next -> (
    let (child, _) = get_child_sibling t li in
    treekem_invariant_apply_path child p_next
  )

val leaf_at_tree_apply_path:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  #l:nat -> #i:tree_index l -> #li:leaf_index l i ->
  t:treekem bytes l i -> p:pathkem bytes l i li ->
  li':leaf_index l i ->
  Lemma (leaf_at (tree_apply_path t p) li' = (if li = li' then Some (get_path_leaf p) else leaf_at t li'))
let rec leaf_at_tree_apply_path #bytes #cb #l #i #li t p li' =
  match t, p with
  | TLeaf _, PLeaf _ -> ()
  | TNode _ left right, PNode _ p_next ->
    match is_left_leaf li, is_left_leaf li' with
    | true, true -> leaf_at_tree_apply_path left p_next li'
    | false, false -> leaf_at_tree_apply_path right p_next li'
    | _, _ -> ()

val treekem_priv_invariant_apply_path:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  #l:nat -> #i:tree_index l -> #my_li:leaf_index l i -> #li:leaf_index l i ->
  t:treekem bytes l i -> priv:treekem_priv bytes l i my_li -> p:pathkem bytes l i li ->
  path_secret:bytes -> path_node_level:path_secret_level l ->
  Lemma
  (requires treekem_priv_invariant t priv)
  (ensures (
    match path_apply_path (tree_apply_path t p) priv path_secret path_node_level with
    | Success (new_path, _) -> treekem_priv_invariant (tree_apply_path t p) new_path
    | _ -> True
  ))
let treekem_priv_invariant_apply_path #bytes #cb #l #i #my_li #li t priv p path_secret path_node_level =
  leaf_at_tree_apply_path t p my_li

(*** Create commit invariants ***)

val path_filtering_ok_generate_path_secrets:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  #l:nat -> #i:tree_index l ->
  t:treekem bytes l i ->
  leaf_sk:hpke_private_key bytes -> path_secret_0:bytes -> li:leaf_index l i ->
  Lemma (
    match generate_path_secrets t leaf_sk path_secret_0 li with
    | Success (res, _) -> path_filtering_ok t res
    | _ -> True
  )
let rec path_filtering_ok_generate_path_secrets #bytes #cb #l #i t leaf_sk path_secret_0 li =
  match generate_path_secrets t leaf_sk path_secret_0 li with
  | Success (res, _) -> (
    match t with
    | TLeaf _ -> ()
    | TNode _ _ _ -> (
      let (child, sibling) = get_child_sibling t li in
      path_filtering_ok_generate_path_secrets child leaf_sk path_secret_0 li
    )
  )
  | _ -> ()

#push-options "--z3rlimit 25"
// ref_t corresponds to the actual tree, which is used to compute filtered nodes
// t corresponds to the un-added tree, used to perform encryption
val path_filtering_ok_encrypt_path_secrets:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  #l:nat -> #i:tree_index l -> #li:leaf_index l i ->
  ref_t:treekem bytes l i ->
  t:treekem bytes l i{treekem_invariant t} -> p:path_secrets bytes l i li ->
  group_context:group_context_nt bytes ->
  rand:randomness bytes (encrypt_path_secrets_entropy_lengths t (forget_path_secrets p)) ->
  Lemma
  (requires path_filtering_ok ref_t p)
  (ensures (
    match encrypt_path_secrets t p group_context rand with
    | Success (res, _) -> path_filtering_ok ref_t res
    | _ -> True
  ))
let rec path_filtering_ok_encrypt_path_secrets #bytes #cb #l #i #li ref_t t p group_context rand =
  match encrypt_path_secrets t p group_context rand with
  | Success (res, _) -> (
    match t, p with
    | TLeaf _, PLeaf leaf_ikm -> ()
    | TNode _ _ _, PNode None p_next -> (
      let (child, _) = get_child_sibling t li in
      let (ref_child, _) = get_child_sibling ref_t li in
      path_filtering_ok_encrypt_path_secrets ref_child child p_next group_context rand
    )
    | TNode _ _ _, PNode (Some path_secret) p_next -> (
      let (child, sibling) = get_child_sibling t li in
      let (ref_child, _) = get_child_sibling ref_t li in
      let rand_cur, rand_next = split_randomness rand in
      let _ = multi_encrypt_with_label (tree_resolution sibling) "UpdatePathNode" (serialize _ group_context) path_secret rand_cur in
      path_filtering_ok_encrypt_path_secrets ref_child child p_next group_context rand_next
    )
  )
  | _ -> ()
#pop-options

val treekem_priv_invariant_encrypt_path_secrets:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  #l:nat -> #i:tree_index l -> #li:leaf_index l i ->
  ref_t:treekem bytes l i ->
  t:treekem bytes l i{treekem_invariant t} -> p:path_secrets bytes l i li ->
  group_context:group_context_nt bytes ->
  rand:randomness bytes (encrypt_path_secrets_entropy_lengths t (forget_path_secrets p)) ->
  Lemma (
    match encrypt_path_secrets t p group_context rand with
    | Success (res, new_priv) -> treekem_priv_invariant (tree_apply_path ref_t res) new_priv
    | _ -> True
  )
let treekem_priv_invariant_encrypt_path_secrets #bytes #cb #l #i #li ref_t t p group_context rand =
  match encrypt_path_secrets t p group_context rand with
  | Success (res, new_priv) -> (
    leaf_at_tree_apply_path ref_t res li
  )
  | _ -> ()
