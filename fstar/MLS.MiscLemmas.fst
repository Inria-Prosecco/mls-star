module MLS.MiscLemmas

open Comparse

#push-options "--fuel 1 --ifuel 1"

val list_for_all_eq: #a:eqtype -> p:(a -> bool) -> l:list a -> Lemma
  (List.Tot.for_all p l <==> (forall x. List.Tot.mem x l ==> p x))
let rec list_for_all_eq #a p l =
  match l with
  | [] -> ()
  | h::t -> list_for_all_eq p t

val mem_filter: #a:eqtype -> p:(a -> bool) -> l:list a -> x:a -> Lemma
  (List.Tot.mem x (List.Tot.filter p l) <==> (p x /\ List.Tot.mem x l))
let rec mem_filter #a p l x =
  match l with
  | [] -> ()
  | h::t -> mem_filter p t x

#push-options "--fuel 2"
val bytes_length_unsnoc: #bytes:Type0 -> {|bytes_like bytes|} -> #a:Type -> ps_a:parser_serializer_unit bytes a -> l:list a{List.Tot.length l > 0} -> Lemma
  (let (tl, hd) = List.Tot.unsnoc l in bytes_length ps_a l == bytes_length ps_a tl + (prefixes_length (ps_a.serialize hd)))
let rec bytes_length_unsnoc #bytes #bl #a ps_a l =
  match l with
  | [x] -> ()
  | h::t -> bytes_length_unsnoc ps_a t
#pop-options
