module TreeSync

open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.HyperStack.All



val bytes_t: eqtype

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

val lemma_map_singleton: f:('a -> 'b) -> x:array 'a{length x = 1} ->
    Lemma (singleton (f (x.[0])) == map f x)
	  [SMTPatOr [
	    [SMTPat (singleton (f (x.[0])));
	     SMTPat (map f x)]]]
val lemma_map_append: f:('a -> 'b) -> x:array 'a -> y:array 'a ->
    Lemma (append (map f x) (map f y) == map f (append x y))
	  [SMTPatOr [
	    [SMTPat (append (map f x) (map f y));
	     SMTPat (map f (append x y))]]]


let sub (x:array 'a) (i:nat{i < length x}) (l:nat{i+l <= length x}) = Seq.slice x i (i+l)

let split (x:array 'a) (i:nat{i < length x}) :
	  res:(array 'a * array 'a){let (y,z) = res in x == append y z /\ length y = i} =
	  let s1 = sub x 0 i in
	  let s2 = sub x i (length x - i) in
	  Seq.lemma_eq_intro x (append s1 s2);
	  (s1,s2)

val fold: f:('a -> 'b -> 'a) -> array 'b -> 'a -> 'a


let pred_p = Type0
let datatype_t = eqtype


(* Cryptography*)
let sign_key_t = bytes_t
let verif_key_t = bytes_t


(* Identity and Credentials *)
val credential_t: eqtype
val name: credential_t -> string
val identity_key: credential_t -> verif_key_t
val valid_credential_p: credential_t -> pred_p

(* Public Information about a Group Member *)
type leaf_package_t = {
  leaf_version: nat;
  leaf_credential: credential_t;
}

(* Secrets belonging to a Group Member  *)
val leaf_secrets_t: datatype_t

(* Group State Data Structure *)
val state_t: datatype_t
val group_id: state_t -> nat
val max_size: state_t -> nat
val epoch: state_t -> nat

type index_t (g:state_t) = i:nat{i < max_size g}

type member_array_t (sz:nat) = a:array (option leaf_package_t){length a = sz}

val membership: g:state_t -> member_array_t (max_size g)

(* Create a new Group State *)
val create: gid:nat -> sz:pos -> init:member_array_t sz
	-> entropy:bytes_t	-> option state_t

(* Group Operation Data Structure *)
val operation_t: datatype_t

(* Apply an Operation to a Group *)
val apply: state_t -> operation_t -> option state_t

(* Create an Operation *)
val modify: s:state_t -> actor:index_t s
	-> i:index_t s -> option leaf_package_t
	-> option operation_t
