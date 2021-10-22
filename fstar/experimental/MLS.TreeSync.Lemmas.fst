module MLS.TreeSync.Lemmas

open MLS.Lib.Array
open Lib.ByteSequence
open MLS.TreeSync

///
/// Internal lemmas
///

let create_tree_lemma l actor init = ()

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

let create_lemma gid sz init = ()

let apply_lemma st op = ()

let mk_operation_lemma st actor i p = ()

let add_lemma st actor i joiner = ()

let remove_lemma st actor i = ()
