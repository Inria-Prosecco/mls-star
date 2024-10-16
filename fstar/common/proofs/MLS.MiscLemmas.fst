module MLS.MiscLemmas

open FStar.List.Tot
open Comparse

#set-options "--fuel 1 --ifuel 1"

val list_for_all_eq:
  #a:eqtype ->
  p:(a -> bool) -> l:list a ->
  Lemma
  (List.Tot.for_all p l <==> (forall x. List.Tot.mem x l ==> p x))
let rec list_for_all_eq #a p l =
  match l with
  | [] -> ()
  | h::t -> list_for_all_eq p t

val mem_filter:
  #a:eqtype ->
  p:(a -> bool) -> l:list a -> x:a ->
  Lemma
  (List.Tot.mem x (List.Tot.filter p l) <==> (p x /\ List.Tot.mem x l))
let rec mem_filter #a p l x =
  match l with
  | [] -> ()
  | h::t -> mem_filter p t x

#push-options "--fuel 2"
val bytes_length_unsnoc:
  #bytes:Type0 -> {|bytes_like bytes|} -> #a:Type ->
  ps_a:parser_serializer_prefix bytes a -> l:list a{List.Tot.length l > 0} ->
  Lemma (
    let (tl, hd) = List.Tot.unsnoc l in
    bytes_length ps_a l == bytes_length ps_a tl + (prefixes_length (ps_a.serialize hd))
  )
let rec bytes_length_unsnoc #bytes #bl #a ps_a l =
  match l with
  | [x] -> ()
  | h::t -> bytes_length_unsnoc ps_a t
#pop-options

val index_append:
  #a:Type ->
  l1:list a -> l2:list a -> i:nat{i < List.Tot.length (l1@l2)} ->
  Lemma (
    index (l1@l2) i == (
      if i < List.Tot.length l1 then
        List.Tot.index l1 i
      else
        List.Tot.index l2 (i - List.Tot.length l1)
    )
  )
let rec index_append #a l1 l2 i =
  match l1 with
  | [] -> ()
  | h1::t1 ->
    if i = 0 then ()
    else index_append t1 l2 (i-1)

val index_map:
  #a:Type -> #b:Type ->
  f:(a -> b) -> l:list a -> i:nat{i < List.Tot.length l} ->
  Lemma
  (index (map f l) i == f (index l i))
let rec index_map #a #b f l i =
  let h::t = l in
  if i = 0 then ()
  else index_map f t (i-1)

val bytes_length_filter:
  #bytes:Type0 -> {|bytes_like bytes|} -> #a:Type ->
  ps_a:parser_serializer_prefix bytes a -> pred:(a -> bool) -> l:list a ->
  Lemma
  (bytes_length #bytes ps_a (List.Tot.filter pred l) <= bytes_length #bytes ps_a l)
let rec bytes_length_filter #bytes #bl #a ps_a pred l =
  match l with
  | [] -> ()
  | h::t -> bytes_length_filter ps_a pred t

val filter_append:
  #a:Type ->
  p:(a -> bool) -> l1:list a -> l2:list a ->
  Lemma (List.Tot.filter p (l1@l2) == (List.Tot.filter p l1)@(List.Tot.filter p l2))
let rec filter_append #a p l1 l2 =
  match l1 with
  | [] -> ()
  | h::t -> filter_append p t l2

val sorted_filter_lemma:
  #a:Type ->
  lt:(a -> a -> bool) -> p:(a -> bool) -> l:list a ->
  Lemma
  (requires
    sorted lt l /\
    (forall x y z. x `lt` y /\ y `lt` z ==> x `lt` z)
  )
  (ensures (
    match l, List.Tot.filter p l with
    | h1::_, h2::_ -> lt h1 h2 \/ h1 == h2
    | _, _ -> True
  ))
let rec sorted_filter_lemma #a lt p l =
  match l with
  | [] -> ()
  | h::t -> sorted_filter_lemma lt p t

val sorted_filter:
  #a:Type ->
  lt:(a -> a -> bool) -> p:(a -> bool) -> l:list a ->
  Lemma
  (requires
    sorted lt l /\
    (forall x y z. x `lt` y /\ y `lt` z ==> x `lt` z)
  )
  (ensures sorted lt (filter p l))
let rec sorted_filter #a lt p l =
  match l with
  | [] -> ()
  | h::t ->
    sorted_filter lt p t;
    if p h then sorted_filter_lemma lt p t
    else ()

// `lt` is made to be a strict order (such as `(<)`),
// not necessarily anti-symetric (i.e. x < y \/ x == y \/ x > y)
#push-options "--fuel 2"
val sorted_append:
  #a:Type ->
  lt:(a -> a -> bool) -> cutoff:a -> l1:list a -> l2:list a ->
  Lemma
  (requires
    sorted lt l1 /\
    sorted lt l2 /\
    (forall x. List.Tot.memP x l1 ==> x `lt` cutoff) /\
    (forall x. List.Tot.memP x l2 ==> (forall y. y `lt` cutoff ==> y `lt` x)) /\
    (forall x y z. x `lt` y /\ y `lt` z ==> x `lt` z)
  )
  (ensures sorted lt (l1@l2))
let rec sorted_append #a lt cutoff l1 l2 =
  match l1 with
  | [] -> ()
  | [h] -> (
    match l2 with
    | [] -> ()
    | _::_ -> ()
  )
  | h::t -> sorted_append lt cutoff t l2
#pop-options

val sorted_lt_head:
  #a:Type ->
  lt:(a -> a -> bool) -> x:a -> l:list a ->
  Lemma
  (requires
    (match l with
    | [] -> True
    | h::t -> x `lt` h
    ) /\
    sorted lt l /\
    (forall x y z. x `lt` y /\ y `lt` z ==> x `lt` z)
  )
  (ensures forall y. List.Tot.memP y l ==> x `lt` y)
let rec sorted_lt_head #a lt x l =
  match l with
  | [] -> ()
  | h::t -> sorted_lt_head lt x t
