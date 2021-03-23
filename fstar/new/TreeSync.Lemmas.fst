module TreeSync.Lemmas

open Lib.Array
open TreeSync

let rec blank_path_lemma (l:nat) (i:index_n l) (olp:option credential_t) (a:credential_t) (t:tree_t l) :
                    Lemma (let t' = apply_path l i a t (blank_path l i olp) in
                          membership_tree l t' == ((membership_tree l t).[i] <- olp)) =
    match t with
    | Leaf _ _ ->
	   let t' = apply_path l i a t (blank_path l i olp) in
	   Seq.lemma_eq_intro (membership_tree l t') ((membership_tree l t).[i] <- olp)
    | Node _ _ left right ->
      let (j,dir) = child_index l i in
      let (child,sibling) = order_subtrees dir (left,right) in
      let p = PNode None (blank_path (l-1) j olp) in
      blank_path_lemma (l-1) j olp a child;
      let t' = apply_path l i a t (blank_path l i olp) in
      Seq.lemma_eq_intro (membership_tree l t') ((membership_tree l t).[i] <- olp)


val mk_operation_lemma: st:state_t -> actor:credential_t
  -> i:index_t st -> p:path_t st.st_levels
  -> Tot (oop:option operation_t{
         match oop with
         | None -> True
         | Some op ->
         match apply st op with
         | None -> False
		   | Some st' -> group_id st' == group_id st
  		              /\ max_size st' == max_size st
			           /\ epoch st' == epoch st + 1
			           /\ (match op.op_path with
                      | PLeaf olp -> membership st' == membership st
                      | _ -> True)})
