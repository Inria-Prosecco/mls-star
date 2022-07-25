module MLS.TreeSync.Level0.Invariants

open Comparse
open MLS.Tree
open MLS.TreeSync.NetworkTypes
open MLS.TreeSync.Level0.Types

#set-options "--fuel 1 --ifuel 1"

val unmerged_leaf_exists: #bytes:Type0 -> {|bytes_like bytes|} -> #tkt:treekem_types bytes -> #l:nat -> #i:tree_index l -> treesync bytes tkt l i -> nat -> bool
let unmerged_leaf_exists #bytes #bl #tkt #l #i t li =
  leaf_index_inside l i li && Some? (leaf_at t li)

val unmerged_leaves_sorted: list (nat_lbytes 4) -> bool
let rec unmerged_leaves_sorted l =
  match l with
  | [] -> true
  | [_] -> true
  | x::y::t -> x < y && unmerged_leaves_sorted (y::t)

val unmerged_leaves_ok: #bytes:Type0 -> {|bytes_like bytes|} -> #tkt:treekem_types bytes -> #l:nat -> #i:tree_index l -> treesync bytes tkt l i -> bool
let rec unmerged_leaves_ok #bytes #bl #tkt #l #i t =
  match t with
  | TLeaf _ -> true
  | TNode opt_content left right ->
    let content_ok =
      match opt_content with
      | None -> true
      | Some content ->
        List.Tot.for_all (unmerged_leaf_exists t) content.unmerged_leaves &&
        unmerged_leaves_sorted content.unmerged_leaves
    in
    content_ok && unmerged_leaves_ok left && unmerged_leaves_ok right
