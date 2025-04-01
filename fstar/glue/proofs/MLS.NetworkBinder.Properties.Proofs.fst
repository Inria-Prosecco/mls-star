module MLS.NetworkBinder.Properties.Proofs

open FStar.List.Tot
open Comparse
open MLS.Crypto
open MLS.NetworkTypes
open MLS.TreeSync.NetworkTypes
open MLS.TreeKEM.NetworkTypes
open MLS.NetworkBinder
open MLS.NetworkBinder.Properties
open MLS.Tree
open MLS.TreeCommon
open MLS.Result
open MLS.MiscLemmas
open MLS.Symbolic.Parsers
open MLS.TreeSync.Symbolic.Parsers
open MLS.TreeKEM.Parsers
open MLS.TreeSync.Types
open MLS.TreeKEM.Types

#set-options "--fuel 1 --ifuel 1"

(*** Path filtering invariants ***)

val path_filtering_ok_uncompress_update_path_aux:
  #bytes:Type0 -> {|bytes_like bytes|} ->
  #leaf_t:Type -> #node_t:Type ->
  #l:nat -> #i:tree_index l ->
  li:leaf_index l i -> t:tree (option leaf_t) (option node_t) l i -> leaf_node:leaf_node_nt bytes tkt -> nodes:list (update_path_node_nt bytes) ->
  Lemma (
    match uncompress_update_path_aux li t (leaf_node, nodes) with
    | Success res -> path_filtering_ok t res
    | _ -> True
  )
let rec path_filtering_ok_uncompress_update_path_aux #bytes #bl #leaf_t #node_t #l #i li t leaf_node nodes =
  match t with
  | TLeaf _ -> (
    if not (List.length nodes = 0) then ()
    else ()
  )
  | TNode _ left right -> (
    let (child, sibling) = get_child_sibling t li in
    if is_tree_empty sibling then (
      path_filtering_ok_uncompress_update_path_aux (li <: leaf_index (l-1) _) child leaf_node nodes
    ) else (
      if not (List.length nodes > 0) then ()
      else (
        let (tail_nodes, head_nodes) = List.unsnoc nodes in
        path_filtering_ok_uncompress_update_path_aux (li <: leaf_index (l-1) _) child leaf_node tail_nodes
      )
    )
  )

val path_filtering_ok_uncompress_update_path:
  #bytes:Type0 -> {|bytes_like bytes|} ->
  #leaf_t:Type -> #node_t:Type ->
  #l:nat -> #i:tree_index l ->
  li:leaf_index l i -> t:tree (option leaf_t) (option node_t) l i -> update_path:update_path_nt bytes ->
  Lemma (
    match uncompress_update_path li t update_path with
    | Success res -> path_filtering_ok t res
    | _ -> True
  )
let path_filtering_ok_uncompress_update_path #bytes #bl #leaf_t #node_t #l #i li t update_path =
  path_filtering_ok_uncompress_update_path_aux li t update_path.leaf_node update_path.nodes

val path_filtering_ok_update_path_to_treesync:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  #leaf_t:Type -> #node_t:Type ->
  #l:nat -> #i:tree_index l -> #li:leaf_index l i ->
  t:tree (option leaf_t) (option node_t) l i ->
  p:sparse_update_path bytes l i li ->
  Lemma
  (requires path_filtering_ok t p)
  (ensures path_filtering_ok t (update_path_to_treesync p))
let rec path_filtering_ok_update_path_to_treesync #bytes #cb #leaf_t #node_t #l #i #li t p =
  match p with
  | PLeaf ln -> ()
  | PNode onp p_next -> (
    let (child, _) = get_child_sibling t li in
    path_filtering_ok_update_path_to_treesync child p_next
  )

val path_filtering_ok_set_path_leaf:
  #tree_leaf_t:Type -> #tree_node_t:Type ->
  #path_in_leaf_t:Type -> #path_out_leaf_t:Type -> #path_node_t:Type ->
  #l:nat -> #i:tree_index l -> #li:leaf_index l i ->
  t:tree (option tree_leaf_t) (option tree_node_t) l i ->
  p:path path_in_leaf_t (option path_node_t) l i li -> lp:path_out_leaf_t ->
  Lemma
  (requires path_filtering_ok t p)
  (ensures path_filtering_ok t (set_path_leaf p lp))
let rec path_filtering_ok_set_path_leaf #tree_leaf_t #tree_node_t #path_in_leaf_t #path_out_leaf_t #path_node_t #l #i #li t p lp =
  match p with
  | PLeaf _ -> ()
  | PNode _ p_next -> (
    let (child, _) = get_child_sibling t li in
    path_filtering_ok_set_path_leaf child p_next lp
  )

val path_filtering_ok_update_path_to_treekem:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  #tree_leaf_t:Type -> #tree_node_t:Type ->
  #l:nat -> #i:tree_index l -> #li:leaf_index l i ->
  t:tree (option tree_leaf_t) (option tree_node_t) l i ->
  p:sparse_update_path bytes l i li ->
  Lemma
  (requires path_filtering_ok t p)
  (ensures path_filtering_ok t (update_path_to_treekem p))
let path_filtering_ok_update_path_to_treekem #bytes #cb #tree_leaf_t #tree_node_t #l #i #li t p =
  path_filtering_ok_set_path_leaf t p (leaf_node_to_treekem (get_path_leaf p))

(*** Correctness of compression / decompression ***)

val compress_uncompress_update_path_aux:
  #bytes:Type0 -> {|bytes_like bytes|} ->
  #leaf_t:Type -> #node_t:Type ->
  #l:nat -> #i:tree_index l ->
  li:leaf_index l i -> t:tree (option leaf_t) (option node_t) l i -> update_path:(leaf_node_nt bytes tkt & list (update_path_node_nt bytes)) ->
  Lemma (
    match uncompress_update_path_aux li t update_path with
    | Success p -> compress_update_path_aux p == update_path
    | _ -> True
  )
let rec compress_uncompress_update_path_aux #bytes #bl #leaf_t #node_t #l #i li t (leaf_node, nodes) =
  match t with
  | TLeaf _ -> (
    if not (List.length nodes = 0) then ()
    else ()
  )
  | TNode _ left right -> (
    let (child, sibling) = get_child_sibling t li in
    if is_tree_empty sibling then (
      compress_uncompress_update_path_aux (li <: leaf_index (l-1) _) child (leaf_node, nodes)
    ) else (
      if not (List.length nodes > 0) then ()
      else (
        let (tail_nodes, head_nodes) = List.unsnoc nodes in
        compress_uncompress_update_path_aux (li <: leaf_index (l-1) _) child (leaf_node, tail_nodes)
      )
    )
  )

val compress_uncompress_update_path:
  #bytes:Type0 -> {|bytes_like bytes|} ->
  #leaf_t:Type -> #node_t:Type ->
  #l:nat -> #i:tree_index l ->
  li:leaf_index l i -> t:tree (option leaf_t) (option node_t) l i -> update_path:update_path_nt bytes ->
  Lemma (
    match uncompress_update_path li t update_path with
    | Success p -> compress_update_path p == Success update_path
    | _ -> True
  )
let compress_uncompress_update_path #bytes #bl #leaf_t #node_t #l #i li t update_path =
  compress_uncompress_update_path_aux li t (update_path.leaf_node, update_path.nodes)

val uncompress_compress_update_path_aux:
  #bytes:Type0 -> {|bytes_like bytes|} ->
  #leaf_t:Type -> #node_t:Type ->
  #l:nat -> #i:tree_index l -> #li:leaf_index l i ->
  t:tree (option leaf_t) (option node_t) l i ->
  p:sparse_update_path bytes l i li ->
  Lemma
  (requires path_filtering_ok t p)
  (ensures uncompress_update_path_aux li t (compress_update_path_aux p) == Success p)
let rec uncompress_compress_update_path_aux #bytes #bl #leaf_t #node_t #l #i #li t p =
  match p with
  | PLeaf ln -> ()
  | PNode p_opt_data p_next ->
    let (child, _) = get_child_sibling t li in
    uncompress_compress_update_path_aux child p_next

val uncompress_compress_update_path:
  #bytes:Type0 -> {|bytes_like bytes|} ->
  #leaf_t:Type -> #node_t:Type ->
  #l:nat -> #i:tree_index l -> #li:leaf_index l i ->
  t:tree (option leaf_t) (option node_t) l i ->
  p:sparse_update_path bytes l i li ->
  Lemma
  (requires path_filtering_ok t p)
  (ensures (
    match compress_update_path p with
    | Success update_path -> uncompress_update_path li t update_path == Success p
    | _ -> True
  ))
let uncompress_compress_update_path #bytes #bl #leaf_t #node_t #l #i #li t p =
  uncompress_compress_update_path_aux t p

(*** Well-formedness ***)

val ratchet_tree_l_pre_lemma:
  #a:Type ->
  n:nat -> x:a -> y:a ->
  Lemma
  (List.Tot.memP y (FStar.Seq.seq_to_list (FStar.Seq.create n x)) ==> x == y)
let rec ratchet_tree_l_pre_lemma #a n x y =
  if n = 0 then ()
  else (
    FStar.Seq.lemma_seq_to_list_cons x (FStar.Seq.create (n-1) x);
    assert(FStar.Seq.cons x (FStar.Seq.create (n-1) x) `FStar.Seq.equal` (FStar.Seq.create n x));
    ratchet_tree_l_pre_lemma (n-1) x y
  )

val ratchet_tree_l_pre:
  #bytes:Type0 -> {|bytes_like bytes|} -> #tkt:treekem_types bytes ->
  pre:bytes_compatible_pre bytes ->
  nodes:ratchet_tree_nt bytes tkt ->
  Lemma
  (requires
    for_allP (is_well_formed_prefix (ps_option (ps_node_nt tkt)) pre) nodes
  )
  (ensures (
    match ratchet_tree_l nodes with
    | Success (|new_nodes, l|) -> (
      for_allP (is_well_formed_prefix (ps_option (ps_node_nt tkt)) pre) new_nodes
    )
    | _ -> True
  ))
let ratchet_tree_l_pre #bytes #bl #tkt pre nodes =
  let n_nodes = List.length nodes in
  if n_nodes%2 = 0 then ()
  else (
    let n = (n_nodes+1)/2 in
    let l = (MLS.TreeMath.Internal.log2 n) in
    if n_nodes = (pow2 (l+1))-1 then ()
    else (
      let extra_nodes = FStar.Seq.seq_to_list (Seq.create ((pow2 (l+2))-1-n_nodes) None) in
      FStar.Classical.forall_intro (ratchet_tree_l_pre_lemma ((pow2 (l+2))-1-n_nodes) (None <: option (node_nt bytes tkt)));
      for_allP_eq (is_well_formed_prefix (ps_option (ps_node_nt tkt)) pre) nodes;
      for_allP_eq (is_well_formed_prefix (ps_option (ps_node_nt tkt)) pre) extra_nodes;
      FStar.Classical.forall_intro (FStar.List.Tot.append_memP nodes extra_nodes);
      for_allP_eq (is_well_formed_prefix (ps_option (ps_node_nt tkt)) pre) (nodes@extra_nodes)
    )
  )

val for_allP_splitAt:
  #a:Type ->
  pre:(a -> prop) -> n:nat -> l:list a ->
  Lemma (
    let (l1, l2) = FStar.List.Tot.splitAt n l in (
      for_allP pre l <==> (
        for_allP pre l1 /\
        for_allP pre l2
      )
    )
  )
let rec for_allP_splitAt #a pre n l =
  if n = 0 then ()
  else (
    match l with
    | [] -> ()
    | h::t -> (
      for_allP_splitAt pre (n-1) t
    )
  )

val for_allP_split3:
  #a:Type ->
  pre:(a -> prop) -> i:nat -> l:list a{i < FStar.List.Tot.length l} ->
  Lemma (
    let (left, mid, right) = FStar.List.Tot.split3 l i in (
      for_allP pre l <==> (
        for_allP pre left /\
        pre mid /\
        for_allP pre right
      )
    )
  )
let for_allP_split3 #a pre i l =
  for_allP_splitAt pre i l

#push-options "--ifuel 1 --fuel 2 --z3rlimit 50"
val ratchet_tree_to_treesync_aux_pre:
  #bytes:Type0 -> {|bytes_like bytes|} -> #tkt:treekem_types bytes ->
  pre:bytes_compatible_pre bytes ->
  l:nat -> i:tree_index l -> nodes:list (option (node_nt bytes tkt)){List.length nodes = (pow2 (l+1)-1)} ->
  Lemma
  (requires
    for_allP (is_well_formed_prefix (ps_option (ps_node_nt tkt)) pre) nodes
  )
  (ensures (
    match ratchet_tree_to_treesync_aux l i nodes with
    | Success treesync ->
      is_well_formed _ pre treesync
    | _ -> True
  ))
let rec ratchet_tree_to_treesync_aux_pre #bytes #bl #tkt pre l i nodes =
  if l = 0 then (
    assert(List.length nodes = 1);
    match nodes with
    | [Some (N_leaf kp)] -> ()
    | [Some _] -> ()
    | [None] -> ()
  ) else (
    let (left_nodes, my_node, right_nodes) = List.Tot.split3 nodes ((pow2 l) - 1) in
    for_allP_split3 (is_well_formed_prefix (ps_option (ps_node_nt tkt)) pre) ((pow2 l) - 1) nodes;
    FStar.List.Tot.lemma_splitAt_snd_length ((pow2 l) - 1) nodes;
    assert(for_allP (is_well_formed_prefix (ps_option (ps_node_nt tkt)) pre) left_nodes);
    assert(for_allP (is_well_formed_prefix (ps_option (ps_node_nt tkt)) pre) (my_node::right_nodes));
    assert((is_well_formed_prefix (ps_option (ps_node_nt tkt)) pre) my_node);
    assert(for_allP (is_well_formed_prefix (ps_option (ps_node_nt tkt)) pre) right_nodes);
    List.Pure.lemma_split3_length nodes ((pow2 l) - 1);
    ratchet_tree_to_treesync_aux_pre pre (l-1) (left_index i) left_nodes;
    ratchet_tree_to_treesync_aux_pre pre (l-1) (right_index i) right_nodes
  )
#pop-options

#push-options "--z3rlimit 25"
val ratchet_tree_to_treesync_pre:
  #bytes:Type0 -> {|bytes_like bytes|} -> #tkt:treekem_types bytes ->
  pre:bytes_compatible_pre bytes ->
  nodes:ratchet_tree_nt bytes tkt ->
  Lemma
  (requires
    is_well_formed _ pre nodes
  )
  (ensures (
    match ratchet_tree_to_treesync nodes with
    | Success (|l, treesync|) ->
      is_well_formed _ pre treesync
    | _ -> True
  ))
let ratchet_tree_to_treesync_pre #bytes #bl #tkt pre nodes =
  if not (Success? (ratchet_tree_to_treesync nodes)) then ()
  else (
    ratchet_tree_l_pre pre nodes;
    let Success (|new_nodes, l|) = ratchet_tree_l nodes in
    ratchet_tree_to_treesync_aux_pre pre l 0 new_nodes
  )
#pop-options

val for_allP_append:
  #a:Type ->
  pre:(a -> prop) -> l1:list a -> l2:list a ->
  Lemma
  (requires
    for_allP pre l1 /\
    for_allP pre l2
  )
  (ensures for_allP pre (l1@l2))
let rec for_allP_append #a pre l1 l2 =
  match l1 with
  | [] -> ()
  | h1::t1 -> for_allP_append pre t1 l2

#push-options "--fuel 2 --ifuel 1"
val treesync_to_ratchet_tree_aux_pre:
  #bytes:Type0 -> {|bytes_like bytes|} -> #tkt:treekem_types bytes ->
  #l:nat -> #i:tree_index l ->
  pre:bytes_compatible_pre bytes ->
  t:treesync bytes tkt l i ->
  Lemma
  (requires
    is_well_formed _ pre t
  )
  (ensures (
    match treesync_to_ratchet_tree_aux t with
    | Success nodes ->
      for_allP (is_well_formed_prefix (ps_option (ps_node_nt tkt)) pre) nodes
    | _ -> True
  ))
let rec treesync_to_ratchet_tree_aux_pre #bytes #bl #tkt #l #i pre t =
  if not (Success? (treesync_to_ratchet_tree_aux t)) then ()
  else (
    match t with
    | TLeaf None -> ()
    | TLeaf (Some lp) -> ()
    | TNode onp left right -> (
      let parent_node = (
        match onp with
        | None -> None
        | Some np -> Some (N_parent np)
      ) in
      let Success left_ratchet = treesync_to_ratchet_tree_aux left in
      let Success right_ratchet = treesync_to_ratchet_tree_aux right in
      treesync_to_ratchet_tree_aux_pre pre left;
      treesync_to_ratchet_tree_aux_pre pre right;
      for_allP_append (is_well_formed_prefix (ps_option (ps_node_nt tkt)) pre) [parent_node] right_ratchet;
      for_allP_append (is_well_formed_prefix (ps_option (ps_node_nt tkt)) pre) left_ratchet ([parent_node]@right_ratchet)
    )
  )
#pop-options

#push-options "--fuel 2 --ifuel 1"
val shrink_ratchet_tree_aux_pre:
  #bytes:Type0 -> {|bytes_like bytes|} -> #tkt:treekem_types bytes ->
  pre:bytes_compatible_pre bytes ->
  nodes:list (option (node_nt bytes tkt)) ->
  Lemma
  (requires for_allP (is_well_formed_prefix (ps_option (ps_node_nt tkt)) pre) nodes)
  (ensures (
    match shrink_ratchet_tree_aux nodes with
    | Some shrinked_nodes -> for_allP (is_well_formed_prefix (ps_option (ps_node_nt tkt)) pre) shrinked_nodes
    | None -> True
  ))
let rec shrink_ratchet_tree_aux_pre #bytes #bl #tkt pre l =
  match l with
  | [] -> ()
  | opt_h::t -> shrink_ratchet_tree_aux_pre pre t
#pop-options

val shrink_ratchet_tree_pre:
  #bytes:Type0 -> {|bytes_like bytes|} -> #tkt:treekem_types bytes ->
  pre:bytes_compatible_pre bytes ->
  nodes:list (option (node_nt bytes tkt)) ->
  Lemma
  (requires for_allP (is_well_formed_prefix (ps_option (ps_node_nt tkt)) pre) nodes)
  (ensures (
    match shrink_ratchet_tree nodes with
    | Success ratchet_tree -> is_well_formed _ pre ratchet_tree
    | _ -> True
  ))
let shrink_ratchet_tree_pre #bytes #bl #tkt pre nodes =
  shrink_ratchet_tree_aux_pre pre nodes;
  assert(for_allP (is_well_formed_prefix (ps_option (ps_node_nt tkt)) pre) [])

val treesync_to_ratchet_tree_pre:
  #bytes:Type0 -> {|bytes_like bytes|} -> #tkt:treekem_types bytes ->
  #l:nat -> #i:tree_index l ->
  pre:bytes_compatible_pre bytes ->
  t:treesync bytes tkt l i ->
  Lemma
  (requires
    is_well_formed _ pre t
  )
  (ensures (
    match treesync_to_ratchet_tree t with
    | Success ratchet_tree ->
      is_well_formed _ pre ratchet_tree
    | _ -> True
  ))
let treesync_to_ratchet_tree_pre #bytes #bl #tkt #l #i pre t =
  if not (Success? (treesync_to_ratchet_tree t)) then ()
  else (
    treesync_to_ratchet_tree_aux_pre pre t;
    let Success pre_ratchet_tree = treesync_to_ratchet_tree_aux t in
    shrink_ratchet_tree_pre pre pre_ratchet_tree
  )

#push-options "--ifuel 2 --fuel 2"
val for_allP_unsnoc:
  #a:Type ->
  pre:(a -> prop) -> l:list a{FStar.List.Tot.length l > 0} ->
  Lemma (
    let (init, last) = FStar.List.Tot.unsnoc l in
    for_allP pre l <==> (
      for_allP pre init /\
      pre last
    )
  )
let for_allP_unsnoc #a pre l =
  for_allP_splitAt pre (FStar.List.Tot.length l - 1) l;
  lemma_splitAt_snd_length (FStar.List.Tot.length l - 1) l
#pop-options

#push-options "--z3rlimit 25"
val uncompress_update_path_aux_pre:
  #bytes:Type0 -> {|bytes_like bytes|} ->
  #leaf_t:Type -> #node_t:Type ->
  #l:nat -> #i:tree_index l ->
  pre:bytes_compatible_pre bytes ->
  li:leaf_index l i -> t:tree (option leaf_t) (option node_t) l i -> update_path:(leaf_node_nt bytes tkt & list (update_path_node_nt bytes)) ->
  Lemma
  (requires
    is_well_formed_prefix (ps_leaf_node_nt tkt) pre (fst update_path) /\
    for_allP (is_well_formed_prefix ps_update_path_node_nt pre) (snd update_path)
  )
  (ensures (
    match uncompress_update_path_aux li t update_path with
    | Success p -> (
      is_well_formed_prefix (ps_path (ps_leaf_node_nt tkt) (ps_option ps_update_path_node_nt) l i li) pre p
    )
    | _ -> True
  ))
let rec uncompress_update_path_aux_pre #bytes #bl #leaf_t #node_t #l #i pre li t (leaf_node, nodes) =
  match t with
  | TLeaf _ -> ()
  | TNode _ left right -> (
    let (child, sibling) = get_child_sibling t li in
    if is_tree_empty sibling then (
      uncompress_update_path_aux_pre #_ #_ #_ #_ #(l-1) pre li child (leaf_node, nodes)
    ) else (
      if not (List.length nodes > 0) then ()
      else (
        let (tail_nodes, head_nodes) = List.unsnoc nodes in
        for_allP_unsnoc (is_well_formed_prefix ps_update_path_node_nt pre) nodes;
        uncompress_update_path_aux_pre #_ #_ #_ #_ #(l-1) pre li child (leaf_node, tail_nodes)
      )
    )
  )
#pop-options

val uncompress_update_path_pre:
  #bytes:Type0 -> {|bytes_like bytes|} ->
  #leaf_t:Type -> #node_t:Type ->
  #l:nat -> #i:tree_index l ->
  pre:bytes_compatible_pre bytes ->
  li:leaf_index l i -> t:tree (option leaf_t) (option node_t) l i -> update_path:update_path_nt bytes ->
  Lemma
  (requires
    is_well_formed_prefix ps_update_path_nt pre update_path
  )
  (ensures (
    match uncompress_update_path li t update_path with
    | Success p ->
      is_well_formed_prefix (ps_path (ps_leaf_node_nt tkt) (ps_option ps_update_path_node_nt) l i li) pre p
    | _ -> True
  ))
let uncompress_update_path_pre #bytes #bl #leaf_t #node_t #l #i pre li t update_path =
  uncompress_update_path_aux_pre pre li t (update_path.leaf_node, update_path.nodes)

val update_path_to_treesync_pre:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  #l:nat -> #i:tree_index l -> #li:leaf_index l i ->
  pre:bytes_compatible_pre bytes ->
  p:sparse_update_path bytes l i li ->
  Lemma
  (requires is_well_formed_prefix (ps_path (ps_leaf_node_nt tkt) (ps_option ps_update_path_node_nt) l i li) pre p)
  (ensures is_well_formed _ pre (update_path_to_treesync p))
let rec update_path_to_treesync_pre #bytes #cb #l #i #li pre p =
  match p with
  | PLeaf ln -> ()
  | PNode onp p_next -> (
    update_path_to_treesync_pre pre p_next
  )

val get_path_leaf_pre:
  #bytes:Type0 -> {|bytes_like bytes|} ->
  #leaf_t:Type0 -> #node_t:Type0 ->
  #l:nat -> #i:tree_index l -> #li:leaf_index l i ->
  ps_leaf_t:parser_serializer bytes leaf_t -> ps_node_t:parser_serializer_prefix bytes node_t ->
  pre:bytes_compatible_pre bytes ->
  p:path leaf_t node_t l i li ->
  Lemma
  (requires is_well_formed_prefix (ps_path ps_leaf_t ps_node_t l i li) pre p)
  (ensures is_well_formed_prefix ps_leaf_t pre (get_path_leaf p))
let rec get_path_leaf_pre #bytes #bl #leaf_t #node_t #l #i #li ps_leaf_t ps_node_t pre p =
  match p with
  | PLeaf _ -> ()
  | PNode _ p_next -> (
    get_path_leaf_pre ps_leaf_t ps_node_t pre p_next
  )

val set_path_leaf_pre:
  #bytes:Type0 -> {|bytes_like bytes|} ->
  #leaf_in_t:Type0 -> #leaf_out_t:Type0 -> #node_t:Type0 ->
  #l:nat -> #i:tree_index l -> #li:leaf_index l i ->
  ps_leaf_in_t:parser_serializer bytes leaf_in_t -> ps_leaf_out_t:parser_serializer bytes leaf_out_t -> ps_node_t:parser_serializer_prefix bytes node_t ->
  pre:bytes_compatible_pre bytes ->
  p:path leaf_in_t node_t l i li ->
  leaf:leaf_out_t ->
  Lemma
  (requires
    is_well_formed_prefix (ps_path ps_leaf_in_t ps_node_t l i li) pre p /\
    is_well_formed_prefix ps_leaf_out_t pre leaf
  )
  (ensures is_well_formed_prefix (ps_path ps_leaf_out_t ps_node_t l i li) pre (set_path_leaf p leaf))
let rec set_path_leaf_pre #bytes #bl #leaf_in_t #leaf_out_t #node_t #l #i #li ps_leaf_in_t ps_leaf_out_t ps_node_t pre p leaf =
  match p with
  | PLeaf _ -> ()
  | PNode _ p_next -> (
    set_path_leaf_pre ps_leaf_in_t ps_leaf_out_t ps_node_t pre p_next leaf
  )

val update_path_to_treekem_pre:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  #l:nat -> #i:tree_index l -> #li:leaf_index l i ->
  pre:bytes_compatible_pre bytes ->
  p:sparse_update_path bytes l i li ->
  Lemma
  (requires is_well_formed_prefix (ps_path (ps_leaf_node_nt tkt) (ps_option ps_update_path_node_nt) l i li) pre p)
  (ensures is_well_formed_prefix (ps_path (ps_treekem_leaf) (ps_option ps_update_path_node_nt) l i li) pre (update_path_to_treekem p))
let update_path_to_treekem_pre #bytes #cb #l #i #li pre p =
  get_path_leaf_pre (ps_leaf_node_nt tkt) (ps_option ps_update_path_node_nt) pre p;
  set_path_leaf_pre (ps_leaf_node_nt tkt) (ps_treekem_leaf) (ps_option ps_update_path_node_nt) pre p (leaf_node_to_treekem (get_path_leaf p))

#push-options "--fuel 2"
val compress_update_path_aux_pre:
  #bytes:Type0 -> {|bytes_like bytes|} ->
  #l:nat -> #i:tree_index l -> #li:leaf_index l i ->
  pre:bytes_compatible_pre bytes ->
  p:sparse_update_path bytes l i li ->
  Lemma
  (requires is_well_formed_prefix (ps_path (ps_leaf_node_nt tkt) (ps_option ps_update_path_node_nt) l i li) pre p)
  (ensures (
    let leaf_node, nodes = compress_update_path_aux p in
    is_well_formed_prefix (ps_leaf_node_nt tkt) pre leaf_node /\
    for_allP (is_well_formed_prefix ps_update_path_node_nt pre) nodes
  ))
let rec compress_update_path_aux_pre #bytes #bl #l #i #li pre p =
  match p with
  | PLeaf ln -> ()
  | PNode p_opt_data p_next ->
    compress_update_path_aux_pre pre p_next;
    let (ln, nodes) = compress_update_path_aux p_next in
    match p_opt_data with
    | None -> ()
    | Some p_data -> (
      for_allP_append (is_well_formed_prefix ps_update_path_node_nt pre) nodes [p_data]
    )
#pop-options

val compress_update_path_pre:
  #bytes:Type0 -> {|bytes_like bytes|} ->
  #l:nat -> #i:tree_index l -> #li:leaf_index l i ->
  pre:bytes_compatible_pre bytes ->
  p:sparse_update_path bytes l i li ->
  Lemma
  (requires is_well_formed_prefix (ps_path (ps_leaf_node_nt tkt) (ps_option ps_update_path_node_nt) l i li) pre p)
  (ensures (
    match compress_update_path p with
    | Success update_path -> is_well_formed_prefix ps_update_path_nt pre update_path
    | _ -> True
  ))
let compress_update_path_pre #bytes #bl #l #i #li pre p =
  compress_update_path_aux_pre pre p

val mls_star_paths_to_update_path_pre:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  #l:nat -> #i:tree_index l -> #li:leaf_index l i ->
  pre:bytes_compatible_pre bytes ->
  ps:pathsync bytes tkt l i li -> pk:pathkem bytes l i li ->
  Lemma
  (requires
    is_well_formed _ pre ps /\
    is_well_formed_prefix (ps_path (ps_treekem_leaf) (ps_option ps_update_path_node_nt) l i li) pre pk
  )
  (ensures is_well_formed_prefix (ps_path (ps_leaf_node_nt tkt) (ps_option ps_update_path_node_nt) l i li) pre (mls_star_paths_to_update_path ps pk))
let mls_star_paths_to_update_path_pre #bytes #cb #l #i #li pre psync pkem =
  get_path_leaf_pre (ps_leaf_node_nt tkt) (ps_option ps_hpke_public_key_nt) pre psync;
  set_path_leaf_pre ps_treekem_leaf (ps_leaf_node_nt tkt) (ps_option ps_update_path_node_nt) pre pkem (get_path_leaf psync)
