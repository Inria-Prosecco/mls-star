module MLS.TreeSync.Invariants.UnmergedLeaves

open Comparse
open MLS.Tree
open MLS.TreeSync.NetworkTypes
open MLS.TreeSync.Types

#set-options "--fuel 1 --ifuel 1"

/// Check that the unmerged leaf li is in a non-blank leaf in t's subtree
val unmerged_leaf_exists:
  #bytes:Type0 -> {|bytes_like bytes|} -> #tkt:treekem_types bytes ->
  #l:nat -> #i:tree_index l -> treesync bytes tkt l i -> nat ->
  bool
let unmerged_leaf_exists #bytes #bl #tkt #l #i t li =
  leaf_index_inside l i li && Some? (leaf_at t li)

/// Check that the unmerged leaf li is unmerged everywhere it can be in t's subtree
val unmerged_leaf_consistent:
  #bytes:Type0 -> {|bytes_like bytes|} -> #tkt:treekem_types bytes ->
  #l:nat -> #i:tree_index l ->
  treesync bytes tkt l i -> nat_lbytes 4 ->
  bool
let rec unmerged_leaf_consistent #bytes #bl #tkt #l #i t li =
  match t with
  | TLeaf _ -> true
  | TNode opt_content left right ->
    (
      match opt_content with
      | None -> true
      | Some content ->
        // Read as: leaf_index_inside ... ==> List.Tot.mem ...
        (not (leaf_index_inside l i li)) || (List.Tot.mem li content.unmerged_leaves)
    ) &&
    unmerged_leaf_consistent left li &&
    unmerged_leaf_consistent right li

/// Check that the unmerged leaves are sorted
val unmerged_leaves_sorted: list (nat_lbytes 4) -> bool
let rec unmerged_leaves_sorted l =
  match l with
  | [] -> true
  | [_] -> true
  | x::y::t -> x < y && unmerged_leaves_sorted (y::t)

/// The unmerged leaves invariant:
/// every non-blank node has unmerged leaves satisfying the three properties above.
val unmerged_leaves_ok:
  #bytes:Type0 -> {|bytes_like bytes|} -> #tkt:treekem_types bytes ->
  #l:nat -> #i:tree_index l ->
  treesync bytes tkt l i ->
  bool
let rec unmerged_leaves_ok #bytes #bl #tkt #l #i t =
  match t with
  | TLeaf _ -> true
  | TNode opt_content left right ->
    let content_ok =
      match opt_content with
      | None -> true
      | Some content ->
        List.Tot.for_all (unmerged_leaf_exists t) content.unmerged_leaves &&
        List.Tot.for_all (unmerged_leaf_consistent t) content.unmerged_leaves &&
        unmerged_leaves_sorted content.unmerged_leaves
    in
    content_ok && unmerged_leaves_ok left && unmerged_leaves_ok right
