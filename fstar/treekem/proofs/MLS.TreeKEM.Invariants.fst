module MLS.TreeKEM.Invariants

open Comparse
open MLS.Crypto
open MLS.Tree
open MLS.TreeCommon
open MLS.TreeKEM.Types

val unmerged_leaf_exists:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  #l:nat -> #i:tree_index l -> treekem bytes l i -> nat ->
  prop
let unmerged_leaf_exists #bytes #bl #l #i t li =
  leaf_index_inside l i li && Some? (leaf_at t li)

val treekem_invariant:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  #l:nat -> #i:tree_index l ->
  treekem bytes l i ->
  prop
let rec treekem_invariant #bytes #cb #l #i t =
  match t with
  | TLeaf oln ->
    True
  | TNode opn left right ->
    let node_ok =
      match opn with
      | Some pn ->
        Comparse.for_allP (unmerged_leaf_exists t) pn.unmerged_leaves
      | None -> True
    in
    node_ok /\ treekem_invariant left /\ treekem_invariant right

val treekem_priv_invariant:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  #l:nat -> #i:tree_index l -> #li:leaf_index l i ->
  treekem bytes l i -> treekem_priv bytes l i li ->
  prop
let rec treekem_priv_invariant #bytes #cb #l #i #li t p =
  match t, p with
  | TLeaf oln, PLeaf sk ->
    //TODO: and oln contains sk's public key?
    Some? oln
  | TNode opn _ _, PNode osk p_next ->
    let (child, _) = get_child_sibling t li in
    treekem_priv_invariant child p_next

val treekem_priv_invariant_leaf_at:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  #l:nat -> #i:tree_index l -> #li:leaf_index l i ->
  t:treekem bytes l i -> p:treekem_priv bytes l i li ->
  Lemma
  (requires treekem_priv_invariant t p)
  (ensures Some? (leaf_at t li))
let rec treekem_priv_invariant_leaf_at #bytes #cb #l #i #li t p =
  match t, p with
  | TLeaf oln, PLeaf sk -> ()
  | TNode opn _ _, PNode osk p_next ->
    let (child, _) = get_child_sibling t li in
    treekem_priv_invariant_leaf_at child p_next

/// Weaker variant of MLS.NetworkBinder.Properties.path_filtering_ok,
/// where a sibling can be empty but the corresponding path node is non-empty.
/// This is useful in TreeKEM,
/// where there might be path secrets with empty siblings,
/// because leaves added in the Commit are un-added before decrypting the path secret,
/// hence when before the path is "filtering_ok",
/// after un-adding the path becomes only "filtering_weak_ok".
/// Fortunately, this is strong enough as a precondition to decrypt the path secret.
val path_filtering_weak_ok:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  #l:nat -> #i:tree_index l -> #li:leaf_index l i ->
  treekem bytes l i -> pathkem bytes l i li ->
  prop
let rec path_filtering_weak_ok #bytes #bl #l #i #li t p =
  match t, p with
  | TLeaf oln, PLeaf new_oln ->
    True
  | TNode _ _ _, PNode new_opn p_next ->
    let (child, sibling) = get_child_sibling t li in
    let node_ok = new_opn == None ==> is_tree_empty sibling in
    node_ok /\ path_filtering_weak_ok child p_next
