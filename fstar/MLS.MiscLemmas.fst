module MLS.MiscLemmas

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
