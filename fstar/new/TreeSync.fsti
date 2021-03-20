module TreeSync

open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.HyperStack.All


val bytes_t: eqtype

(* Datastructures *)
let length a = Seq.length a
let empty = Seq.empty
let singleton x = Seq.create 1 x
let append x y = Seq.append x y

let array a = Seq.seq a
let larray 'a sz = arr:array 'a{length arr == sz}


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
val member_secrets_t: datatype_t

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
val modify: g:state_t -> actor:index_t g
	-> i:index_t g -> mi':option leaf_package_t
	-> option operation_t

(* Group Secret shared by all Members *)
val group_secret_t: datatype_t

(* Calculate Group Secret *)
val calculate_group_secret: g:state_t -> i:index_t g
	-> ms:member_secrets_t -> option group_secret_t
	-> option group_secret_t

(* Protocol Messages *)
type msg =
     | AppMsg: ctr:nat -> m:bytes_t -> msg
     | Create: g:state_t -> msg
     | Modify: operation_t -> msg
     | Welcome: g:state_t -> i:index_t g
	      -> secrets:bytes_t -> msg
     | Goodbye: msg

(* Encrypt Protocol Message *)
val encrypt_msg: g:state_t -> gs:group_secret_t
	-> sender:index_t g -> ms:member_secrets_t -> m:msg
	-> entropy:bytes_t -> (bytes_t & group_secret_t)

(* Decrypt Initial Group State *)
val decrypt_initial: ms:member_secrets_t
	-> c:bytes_t -> option msg

(* Decrypt Protocol Message *)
val decrypt_msg: g:state_t -> gs:group_secret_t
	-> receiver:index_t g -> c:bytes_t
	-> option (msg & sender:index_t g & group_secret_t)

(* Retrieve credentials *)
let credential_array_t (sz:nat) = larray (option credential_t) sz
let cred x = x.leaf_credential



val modify_lemma: g:state_t -> actor:index_t g
                -> i:index_t g -> mi':option leaf_package_t
	             -> entropy:bytes_t -> Lemma
    (match modify g actor i mi' with
	   | None -> True
	   | Some o ->
	     (match apply g o with
		  | None -> False
		  | Some g' -> group_id g' == group_id g
  		            /\ max_size g' == max_size g
			         /\ epoch g' == epoch g + 1
			         /\ membership g' == ((membership g).[i] <- mi')))


let occupied (g:state_t) (i:index_t g) =
  (membership g).[i] =!= None

let append_only_array (t:Type) : Type = FStar.Monotonic.Seq.i_seq root t (fun _ -> True)


type principal_t = string

val label_t: datatype_t
val pub: label_t
val labeled: bytes_t -> label_t -> pred_p

noeq type usage_t =
  | AE | PKE | SIG | Nonce | KDF: f:(bytes_t -> label_t & usage_t) -> usage_t

(* noeq *)
(* (\*--- traceBegin ---*\) *)
(* type event = *)
(*  | GenRand: p:prin -> r:bytes -> l:label -> u:usage -> event *)
(*  | StoreState: p:prin -> vv:array nat *)
(* 	    -> st:array bytes{length st == length vv} -> event *)
(*  | Corrupt: id:pssid -> event *)
(*  | SendMsg: s:prin -> r:prin -> m:bytes -> event *)
(* val trace: append_only_array event *)
(* (\*--- traceEnd ---*\) *)



val valid_trace_p: mem -> Type0
val modifies_trace_p: mem -> mem -> Type0
val modifies_rng_p: mem -> mem -> Type0

val derived_label: label_t -> bytes_t -> label_t
val derived_usage: label_t -> bytes_t -> usage_t

val labeled_secret_t: bytes_t -> label_t -> usage_t -> pred_p
(* val secret_gen: is:array pssid -> rs:array pssid -> u:usage *)
(* 	      -> ST (s:bytes{labeled_secret s (sec is rs) u}) *)
(* (\*--- secretGenEnd ---*\) *)
(* 		   (requires (fun h0 -> valid_trace h0)) *)
(* 		   (ensures (fun h0 _ h1 -> modifies_trace h0 h1)) *)

val kdf: s:bytes_t -> ctx:bytes_t -> s':bytes_t

val labeled_enc_key: ek:bytes_t -> label_t -> Type0
val labeled_verif_key: ek:bytes_t -> label_t -> Type0

val sign_pred: label_t -> bytes_t -> Type0
val sign: sk:bytes_t -> m:bytes_t{forall kl. labeled_secret_t sk kl SIG
		              ==> sign_pred kl m}
	-> signed: bytes_t

val verify: vk:bytes_t -> signed:bytes_t -> option bytes_t

val send: p1:principal_t -> p2:principal_t
        -> m:bytes_t{labeled m pub} -> ST unit
	  (requires (fun st0 -> valid_trace_p st0))
	  (ensures (fun st0 _ st1 -> modifies_trace_p st0 st1))
