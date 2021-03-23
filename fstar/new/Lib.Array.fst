module Lib.Array

(* Datastructures *)
let array a = Seq.seq a
let length a = Seq.length a
let empty = Seq.empty
let singleton x = Seq.create 1 x
let append x y = Seq.append x y

(* Infix operators *)
let op_String_Access x y = Seq.index x y
let op_String_Assignment x y z = Seq.upd x y z

(* Datastructures operators *)
let rec mapi (f:'a -> 'b) (x:array 'a) (i:nat{i <= length x}) : y:array 'b{length y = i} =
  if i = 0 then empty else Seq.snoc (mapi f x (i-1)) (f x.[i-1])

let map (f:'a -> 'b) (x:array 'a) = mapi f x (length x)


val lemma_singleton: x:array 'a{length x = 1} -> i:nat{i<length x} ->
  Lemma (singleton x.[i] == x)
	[SMTPat (singleton x.[i])]
let lemma_singleton x i = Seq.lemma_eq_intro (singleton x.[i]) x

val lemma_map_singleton: f:('a -> 'b) -> x:array 'a{length x = 1} ->
    Lemma (singleton (f (x.[0])) == map f x)
	  [SMTPatOr [
	    [SMTPat (singleton (f (x.[0])));
	     SMTPat (map f x)]]]
let lemma_map_singleton f x = admit()

val lemma_map_append: f:('a -> 'b) -> x:array 'a -> y:array 'a ->
    Lemma (append (map f x) (map f y) == map f (append x y))
	  [SMTPatOr [
	    [SMTPat (append (map f x) (map f y));
	     SMTPat (map f (append x y))]]]
let lemma_map_append f x y = admit()


let sub (x:array 'a) (i:nat{i < length x}) (l:nat{i+l <= length x}) = Seq.slice x i (i+l)

let split (x:array 'a) (i:nat{i < length x}): res:(array 'a * array 'a){let (y,z) = res in x == append y z /\ length y = i} =
  let s1 = sub x 0 i in
  let s2 = sub x i (length x - i) in
  Seq.lemma_eq_intro x (append s1 s2);
  (s1,s2)


let rec foldi (f:'a -> 'b -> 'a) (x:array 'b) (init:'a) (n:nat{n <= length x}) =
  if n = 0 then init
  else f (foldi f x init (n-1)) x.[n-1]

val fold: f:('a -> 'b -> 'a) -> array 'b -> 'a -> 'a
let fold f x a = foldi f x a (length x)
