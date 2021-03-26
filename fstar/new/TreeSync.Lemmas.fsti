module TreeSync.Lemmas

open Lib.Array
open TreeSync

///
/// Internal lemmas
///

val blank_path_lemma: l:nat -> i:index_n l -> olp:option credential_t -> a:credential_t -> t:tree_t l
  -> Lemma (let t' = apply_path l i a t (blank_path l i olp) in
                    tree_membership l t' == ((tree_membership l t).[i] <- olp))


///
/// API lemmas
///

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
