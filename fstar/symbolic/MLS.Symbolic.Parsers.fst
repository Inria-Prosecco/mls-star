module MLS.Symbolic.Parsers

open Comparse
open MLS.Tree
open FStar.Mul

#set-options "--fuel 1 --ifuel 1"

val ps_tree_index_pred: l:nat -> i:nat -> bool
let ps_tree_index_pred l i =
  (i / (pow2 l)) * (pow2 l) = i

[@@is_parser; is_parser_for (`%tree_index)]
val ps_tree_index:
  #bytes:Type0 -> {|bytes_like bytes|} ->
  l:nat ->
  parser_serializer bytes (tree_index l)
let ps_tree_index #bytes #bl l =
  mk_isomorphism
    (tree_index l)
    (refine ps_nat (ps_tree_index_pred l))
    (fun x -> x)
    (fun x ->
      eliminate exists k. x == k * (pow2 l)
      returns ps_tree_index_pred l x
      with _. (
        FStar.Math.Lemmas.cancel_mul_div k (pow2 l)
      );
      x
    )

[@@is_parser; is_parser_for (`%leaf_index)]
val ps_leaf_index:
  #bytes:Type0 -> {|bytes_like bytes|} ->
  l:nat -> i:tree_index l ->
  parser_serializer bytes (leaf_index l i)
let ps_leaf_index #bytes #bl l i =
  mk_trivial_isomorphism (refine ps_nat (leaf_index_inside l i))


noeq type tree_internal_node (bytes:Type0) {|bytes_like bytes|} (leaf_t:Type0) (node_t:Type0) (l:pos) (i:tree_index l) (ps_node_t:parser_serializer_prefix bytes node_t) (ps_left:parser_serializer bytes (tree leaf_t node_t (l-1) (left_index i))) (ps_right:parser_serializer bytes (tree leaf_t node_t (l-1) (right_index i))) = {
  [@@@ with_parser #bytes ps_left]
  left: tree leaf_t node_t (l-1) (left_index i);
  [@@@ with_parser #bytes ps_node_t]
  data: node_t;
  [@@@ with_parser #bytes ps_right]
  right: tree leaf_t node_t (l-1) (right_index i);
}

%splice [ps_tree_internal_node] (gen_parser (`tree_internal_node))
%splice [ps_tree_internal_node_is_well_formed] (gen_is_well_formed_lemma (`tree_internal_node))

[@@"opaque_to_smt"]
val ps_tree:
  #bytes:Type0 -> {|bytes_like bytes|} ->
  #leaf_t:Type0 -> #node_t:Type0 ->
  parser_serializer bytes leaf_t -> parser_serializer_prefix bytes node_t -> l:nat -> i:tree_index l ->
  parser_serializer bytes (tree leaf_t node_t l i)
let rec ps_tree #bytes #bl #leaf_t #node_t ps_leaf_t ps_node_t l i =
  if l = 0 then (
    mk_isomorphism
      (tree leaf_t node_t 0 i)
      ps_leaf_t
      (fun x -> TLeaf x)
      (fun (TLeaf x) -> x)
  ) else (
    mk_isomorphism
      (tree leaf_t node_t l i)
      (ps_tree_internal_node #bytes #bl leaf_t node_t l i ps_node_t (ps_tree ps_leaf_t ps_node_t (l-1) (left_index i)) (ps_tree ps_leaf_t ps_node_t (l-1) (right_index i)))
      (fun {left; data; right} -> TNode data left right)
      (fun (TNode data left right) -> {left; data; right})
  )

let reveal_rec_opaque (s: string) = norm_spec [delta_only [s]; zeta]

val ps_tree_is_well_formed:
  #bytes:Type0 -> {|bytes_like bytes|} -> #leaf_t:Type0 -> #node_t:Type0 ->
  ps_leaf_t:parser_serializer bytes leaf_t -> ps_node_t:parser_serializer_prefix bytes node_t -> l:nat -> i:tree_index l ->
  pre:bytes_compatible_pre bytes -> x:tree leaf_t node_t l i ->
  Lemma
  (is_well_formed_prefix (ps_tree ps_leaf_t ps_node_t l i) pre x <==> (
    match x with
    | TLeaf y -> is_well_formed_prefix ps_leaf_t pre y
    | TNode y left right -> is_well_formed_prefix ps_node_t pre y /\ is_well_formed_prefix (ps_tree ps_leaf_t ps_node_t (l-1) (left_index i)) pre left /\ is_well_formed_prefix (ps_tree ps_leaf_t ps_node_t (l-1) (right_index i)) pre right
  ))
  [SMTPat (is_well_formed_prefix (ps_tree ps_leaf_t ps_node_t l i) pre x)]
let ps_tree_is_well_formed #bytes #bl #leaf_t #node_t ps_leaf_t ps_node_t l i pre x =
  reveal_rec_opaque (`%ps_tree) (ps_tree ps_leaf_t ps_node_t l i)

[@@ can_be_unit]
noeq type path_internal_node (bytes:Type0) {|bytes_like bytes|} (leaf_t:Type0) (node_t:Type0) (l:pos) (i:tree_index l) (li:leaf_index l i) (ps_node_t:parser_serializer_prefix bytes node_t) (ps_next:parser_serializer_prefix bytes (path leaf_t node_t (l-1) (if is_left_leaf li then left_index i else right_index i) li)) = {
  [@@@ with_parser #bytes ps_node_t]
  data: node_t;
  // The full implicits must be given to work in lax mode (hence, in dependency loading)
  [@@@ with_parser #bytes #_ #(path leaf_t node_t (l-1) (if is_left_leaf li then left_index i else right_index i) li) ps_next]
  next: path leaf_t node_t (l-1) (if is_left_leaf li then left_index i else right_index i) li;
}

#push-options "--compat_pre_core 1"
%splice [ps_path_internal_node] (gen_parser (`path_internal_node))
%splice [ps_path_internal_node_is_well_formed] (gen_is_well_formed_lemma (`path_internal_node))
#pop-options

[@@"opaque_to_smt"]
val ps_path:
  #bytes:Type0 -> {|bytes_like bytes|} -> #leaf_t:Type0 -> #node_t:Type0 ->
  parser_serializer_prefix bytes leaf_t -> parser_serializer_prefix bytes node_t -> l:nat -> i:tree_index l -> li:leaf_index l i ->
  parser_serializer_prefix bytes (path leaf_t node_t l i li)
let rec ps_path #bytes #bl #leaf_t #node_t ps_leaf_t ps_node_t l i li =
  if l = 0 then (
    mk_isomorphism
      (path leaf_t node_t 0 i li)
      ps_leaf_t
      (fun x -> PLeaf x)
      (fun (PLeaf x) -> x)
  ) else (
    mk_isomorphism
      (path leaf_t node_t l i li)
      (ps_path_internal_node #bytes #bl leaf_t node_t l i li ps_node_t (ps_path ps_leaf_t ps_node_t (l-1) (if is_left_leaf li then left_index i else right_index i) li))
      (fun {data; next} -> PNode data next)
      (fun (PNode data next) -> {data; next;})
  )

val ps_path_is_well_formed:
  #bytes:Type0 -> {|bytes_like bytes|} -> #leaf_t:Type0 -> #node_t:Type0 ->
  ps_leaf_t:parser_serializer bytes leaf_t -> ps_node_t:parser_serializer_prefix bytes node_t -> l:nat -> i:tree_index l -> li:leaf_index l i ->
  pre:bytes_compatible_pre bytes -> x:path leaf_t node_t l i li ->
  Lemma
  (is_well_formed_prefix (ps_path ps_leaf_t ps_node_t l i li) pre x <==> (
    match x with
    | PLeaf y -> is_well_formed_prefix ps_leaf_t pre y
    | PNode y next -> is_well_formed_prefix ps_node_t pre y /\ is_well_formed_prefix (ps_path ps_leaf_t ps_node_t (l-1) (if is_left_leaf li then left_index i else right_index i) li) pre next
  ))
  [SMTPat (is_well_formed_prefix (ps_path ps_leaf_t ps_node_t l i li) pre x)]
let ps_path_is_well_formed #bytes #bl #leaf_t #node_t ps_leaf_t ps_node_t l i li pre x =
  reveal_rec_opaque (`%ps_path) (ps_path ps_leaf_t ps_node_t l i li)
