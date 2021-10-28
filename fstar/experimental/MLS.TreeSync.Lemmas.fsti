module MLS.TreeSync.Lemmas

open MLS.Lib.Array
open MLS.Lib.Maths
open MLS.TreeSync
open MLS.TreeSync.Helpers


///
/// Internal lemmas
///

val create_tree_lemma: l:level_n -> actor:credential_t -> init:member_array_t (pow2 l)
  -> Lemma (let t = create_tree l actor init in
           tree_membership l t == init)

val blank_path_lemma: l:nat -> i:index_n l -> olp:option credential_t -> a:credential_t -> t:tree_t l
  -> Lemma (let t' = apply_path l i a t (blank_path l i olp) in
           tree_membership l t' == ((tree_membership l t).[i] <- olp))

///
/// API lemmas
///

val create_lemma: gid:nat -> sz:pos{Some? (log2 sz)} -> init:member_array_t sz{Some? init.[0]}
  -> Lemma (match create gid sz init with
          | None -> True
          | Some st ->
          group_id st == gid
          /\ max_size st == sz
          /\ epoch st == 0
          /\ membership st == init)


val apply_lemma: st:state_t -> op:operation_t{op.op_levels = st.st_levels}
  -> Lemma ( match apply st op with
            | None -> True
            | Some st' ->
              let t' = apply_path op.op_levels op.op_index op.op_actor st.st_tree op.op_path in
              ( st'.st_group_id == st.st_group_id
              /\ st'.st_levels == st.st_levels
              /\ st'.st_version == st.st_version + 1
              /\ st'.st_tree == t'
              /\ st'.st_transcript == Seq.snoc st.st_transcript op))


val mk_operation_lemma: st:state_t -> actor:credential_t
  -> i:index_t st -> p:path_t st.st_levels
  -> Lemma (match mk_operation st actor i p with
           | None -> True
           | Some op ->
           match apply st op with
           | None -> True
           | Some st' -> group_id st' == group_id st
                      /\ max_size st' == max_size st
                      /\ epoch st' == epoch st + 1
                      /\ (match p with
                        | PNode _ _ -> True
                        | PLeaf olp -> (leaf_packages st') = ((leaf_packages st).[i] <- olp)))


val add_lemma: st:state_t -> actor:credential_t
  -> i:index_t st -> joiner:credential_t
  -> Lemma ( match add st actor i joiner with
            | None -> True
            | Some (op,st') ->
              let t' = apply_path op.op_levels op.op_index op.op_actor st.st_tree op.op_path in
              ( st'.st_levels = st.st_levels
              /\ st'.st_version = st.st_version + 1
              /\ st'.st_tree = t'
              /\ st'.st_transcript = Seq.snoc st.st_transcript op
              /\ ((membership st') = ((membership st).[i] <- (Some joiner)))))


val remove_lemma: st:state_t -> actor:credential_t -> i:index_t st
  -> Lemma ( match remove st actor i with
            | None -> True
            | Some (op,st') ->
              let t' = apply_path op.op_levels op.op_index op.op_actor st.st_tree op.op_path in
              ( st'.st_levels = st.st_levels
              /\ st'.st_version = st.st_version + 1
              /\ st'.st_tree = t'
              /\ st'.st_transcript = Seq.snoc st.st_transcript op
              /\ ((membership st') = ((membership st).[i] <- None))))