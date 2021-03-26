module TreeSync.Lemmas

open Lib.Array
open TreeSync

///
/// Internal lemmas
///

let rec blank_path_lemma l i olp a t =
  match t with
  | Leaf _ _ ->
	 let t' = apply_path l i a t (blank_path l i olp) in
	 Seq.lemma_eq_intro (tree_membership l t') ((tree_membership l t).[i] <- olp)
  | Node _ _ left right ->
    let (j,dir) = child_index l i in
    let (child,sibling) = order_subtrees dir (left,right) in
    let p = PNode None (blank_path (l-1) j olp) in
    blank_path_lemma (l-1) j olp a child;
    let t' = apply_path l i a t (blank_path l i olp) in
    Seq.lemma_eq_intro (tree_membership l t') ((tree_membership l t).[i] <- olp)

///
/// API lemmas
///





(* val valid_credential_p: credential_t -> pred_p *)
(* let valid_credential_p c = validate_credential c *)

(* let initial_leaf_package_p (olp:option leaf_package_t) = *)
(*   match olp with *)
(*   | None -> True *)
(*   | Some lp -> valid_credential_p lp.leaf_credential /\ lp.leaf_version = 0 *)