module TreeSync


(* Base datatypes *)
type bytes_t = Seq.seq nat
let empty_bytes = Seq.empty

let pred_p = Type0
let datatype_t = eqtype


(* Cryptography*)
let sign_key_t = bytes_t
let verif_key_t = bytes_t


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


type principal_t = string

(* Identity and Credentials *)
type credential_t: eqtype = {
  cred_name: principal_t;
  cred_sid: nat;
  cred_version: nat;
  cred_identity_key: verif_key_t;
  cred_issuer: principal_t;
  cred_signature: bytes_t;
}

val name: credential_t -> string
let name c = c.cred_name

val identity_key: credential_t -> verif_key_t
let identity_key c = c.cred_identity_key

assume val validate_: credential_t -> bool

val valid_credential_p: credential_t -> pred_p
let valid_credential_p c = validate_ c

(* Secrets associated to a leaf *)


type direction_t = | Left | Right

let dual (d:direction_t) : direction_t =
  match d with
  | Left -> Right
  | Right -> Left

(* Secrets belonging to a Group Member  *)
type leaf_secrets_t: eqtype = {
  identity_sig_key: sign_key_t;
}

(* Public Information about a Group Member *)
type leaf_package_t = {
  leaf_version: nat;
  leaf_credential: credential_t;
}

type node_package_t = {
  node_from : direction_t;
  node_content: bytes_t
}

type tree_t (lev:nat) =
 | Leaf: actor:credential_t{lev=0} -> olp:option leaf_package_t -> tree_t lev
 | Node: actor:credential_t{lev>0} -> onp:option node_package_t ->
         left:tree_t (lev - 1) -> right:tree_t (lev - 1) -> tree_t lev

type path_t (lev:nat) =
 | PLeaf: olp:option leaf_package_t{lev=0} -> path_t lev
 | PNode: onp:option node_package_t{lev>0} ->
	       next:path_t (lev-1) -> path_t lev

type state_t: eqtype = {
  st_group_id: nat;
  st_levels: nat;
  st_tree: tree_t st_levels;
  st_epoch: nat;
  st_transcript_hash: bytes_t;
}

let index_n (l:nat) = x:nat{x < pow2 l}

let group_id g = g.st_group_id
let max_size g = pow2 g.st_levels
let epoch g = g.st_epoch


(* Group State Data Structure *)
(* val state_t: datatype_t *)
(* val group_id: state_t -> nat *)
(* val max_size: state_t -> nat *)
(* val epoch: state_t -> nat *)

type index_t (g:state_t) = i:nat{i < max_size g}

type member_array_t (sz:nat) = a:array (option leaf_package_t){length a = sz}



let rec membership_tree (l:nat) (t:tree_t l): member_array_t (pow2 l) =
  match t with
  | Leaf _ mi -> singleton mi
  | Node _ _ left right -> append (membership_tree (l-1) left)
				 (membership_tree (l-1) right)

val membership: g:state_t -> member_array_t (max_size g)
let membership g = membership_tree g.st_levels g.st_tree

val log2: sz:pos -> option nat
let rec log2 sz =
  if sz = 1 then Some 0
  else if sz % 2 = 1 then None
       else match log2 (sz/2) with
	    | None -> None
	    | Some l -> Some (1+l)

let rec log2_lemma (sz:pos):
  Lemma (match log2 sz with
	 | None -> True
	 | Some l -> sz == pow2 l)
	 [SMTPat (log2 sz)] =
   if sz = 1 then ()
   else log2_lemma (sz/2)

val create_tree: l:nat -> c:credential_t ->
		 init:member_array_t (pow2 l) ->
		 t:tree_t l{membership_tree l t == init}

(* Create a new tree from a member array *)
let rec create_tree (l:nat) (c:credential_t) (init:member_array_t (pow2 l)) =
  if l = 0 then Leaf c init.[0]
  else let init_l,init_r = split init (pow2 (l-1)) in
    let left = create_tree (l-1) c init_l in
    let right = create_tree (l-1) c init_r in
    Node c None left right

(* Auxiliary tree functions *)
let child_index (l:pos) (i:index_n l) : index_n (l-1) & direction_t =
  if i < pow2 (l - 1) then (i, Left) else (i-pow2 (l-1), Right)

let order_subtrees dir (l,r) = if dir = Left then (l,r) else (r,l)

(* Apply a path to a tree *)
let rec apply_path (l:nat) (i:nat{i<pow2 l}) (a:credential_t)
                   (t:tree_t l) (p:path_t l) : tree_t l =
  match t,p with
  | Leaf _ m, PLeaf m' -> Leaf a m'
  | Node _ _ left right, PNode onp next ->
     let (j,dir) = child_index l i in
     if dir = Left
     then Node a onp (apply_path (l-1) j a left next) right
     else Node a onp left (apply_path (l-1) j a right next)

(* Create a blank path after modifying a leaf *)
let rec blank_path (l:nat) (i:index_n l) (olp:option leaf_package_t) : path_t l =
  if l = 0 then PLeaf olp
  else let (j,dir) = child_index l i in
    PNode None (blank_path (l-1) j olp)

let rec blank_path_lemma (l:nat) (i:index_n l) (olp:option leaf_package_t) (a:credential_t) (t:tree_t l) :
                    Lemma (let t' = apply_path l i a t (blank_path l i olp) in
                          membership_tree l t' == ((membership_tree l t).[i] <- olp)) =
    match t with
    | Leaf _ _ ->
	   let t' = apply_path l i a t (blank_path l i olp) in
	   Seq.lemma_eq_intro (membership_tree l t') ((membership_tree l t).[i] <- olp)
    | Node _ _ left right ->
      let (j,dir) = child_index l i in
      let (child,sibling) = order_subtrees dir (left,right) in
      let p = PNode None (blank_path (l-1) j olp) in
      blank_path_lemma (l-1) j olp a child;
      let t' = apply_path l i a t (blank_path l i olp) in
      Seq.lemma_eq_intro (membership_tree l t') ((membership_tree l t).[i] <- olp)

let initial_leaf_package (olp:option leaf_package_t) =
  match olp with
  | None -> True
  | Some lp -> valid_credential_p lp.leaf_credential /\ lp.leaf_version = 0

(* Create an update path from a leaf to the root *)
let rec update_path (l:nat) (t:tree_t l) (i:nat{i<pow2 l}) (lp_i:leaf_package_t) : option (path_t l) =
  match t with
  | Leaf _ None -> None
  | Leaf _ (Some mi) -> if name(mi.leaf_credential) = name(lp_i.leaf_credential)
                       then Some (PLeaf (Some lp_i))
                       else None
  | Node _ _ left right ->
     let (j,dir) = child_index l i in
     let (child,sibling) = order_subtrees dir (left,right) in
     match update_path (l-1) child j lp_i with
       | None -> None
       | Some next ->
         let np = {node_from = dir; node_content = empty_bytes} in // BB. TODO.
         Some (PNode (Some np) next)

let rec update_path_lemma (l:nat) (i:nat{i<pow2 l}) (a:credential_t) (t:tree_t l) (lp_i:leaf_package_t):
  Lemma (match update_path l t i lp_i with
		  | None -> True
		  | Some p ->
			 (match (membership_tree l t).[i] with
			 | None -> False
			 | Some mi_old -> name(mi_old.leaf_credential) == name(lp_i.leaf_credential) /\
					           (let t' = apply_path l i a t p in
					           membership_tree l t' = ((membership_tree l t).[i] <- Some lp_i)))) =
   match t with
   | Leaf _ None -> ()
   | Leaf _ (Some mi) ->
     if name(mi.leaf_credential) = name(lp_i.leaf_credential)
     then let p : path_t l = PLeaf (Some lp_i) in
	  let t' = apply_path l i a t p in
	  Seq.lemma_eq_intro (membership_tree l t')
	                     ((membership_tree l t).[i] <- Some lp_i)
     else ()
  | Node _ _ left right ->
     let (j,dir) = child_index l i in
     let (child,sibling) = order_subtrees dir (left,right) in
     match update_path (l-1) child j lp_i with
       | None -> ()
       | Some next ->
         update_path_lemma (l-1) j a child lp_i;
         let np = {node_from = dir; node_content = empty_bytes} in // BB. TODO.
         let p = PNode (Some np) next in
	      let t' = apply_path l i a t p in
	      Seq.lemma_eq_intro (membership_tree l t')
		                      ((membership_tree l t).[i] <- Some lp_i)


assume val hash_state: state_t -> bytes_t


(* Create a new group state *)
val create: gid:nat -> sz:pos -> init:member_array_t sz
          -> entropy:bytes_t	-> option state_t

let create gid sz init leaf_secret =
  match init.[0], log2 sz with
  | None,_ -> None
  | _,None -> None
  | Some c,Some l ->
    let t = create_tree l c.leaf_credential init in
    let mi' = {leaf_credential=c.leaf_credential; leaf_version=1} in
    (match update_path l t 0 mi' with
    | None -> None
    | Some p -> let t' = apply_path l 0 c.leaf_credential t p in
		   let g0 = {st_group_id=gid;
                   st_levels=l;
			          st_tree=t';
                   st_epoch=0;
			          st_transcript_hash = empty} in
		   let h0 = hash_state g0 in
		   Some ({g0 with st_transcript_hash = h0}))

val leaf_init: oc:option (c:credential_t) ->
  om:option leaf_package_t{
		      match oc,om with
		      | None,None -> True
		      | Some c,Some m -> m.leaf_credential == c
		      | _ -> False}

let leaf_init oc =
  match oc with
  | None -> None
  | Some c -> Some ({leaf_credential = c; leaf_version = 0})

val leaf_updated: sz:nat -> i:nat{i < sz} -> member_array_t sz -> member_array_t sz -> Type0
let leaf_updated sz i m1 m2 =
  match m1.[i] with
  | None -> False
  | Some mi -> (exists mi'. m2 == (m1.[i] <- Some mi') /\ name(mi'.leaf_credential) == name(mi.leaf_credential))

val create_lemma: gid:nat -> sz:pos -> init:member_array_t sz
	-> entropy:bytes_t	-> Lemma(
	     match create gid sz init entropy with
	     | None -> True
	     | Some g ->
		    group_id g == gid /\  max_size g == sz /\ epoch g == 0 /\
		    leaf_updated sz 0 init (membership g))

let create_lemma gid sz init leaf_secret =
  match init.[0], log2 sz with
  | None,_ -> ()
  | _,None -> ()
  | Some c,Some l ->
    let t = create_tree l c.leaf_credential init in
    let lp' = {leaf_credential = c.leaf_credential; leaf_version = 1} in
    (match update_path l t 0 lp' with
    | None -> ()
    | Some p -> (update_path_lemma l 0 c.leaf_credential t lp';
		   let t' = apply_path l 0 c.leaf_credential t p in
		   assert (membership_tree l t == init);
		   assert (membership_tree l t' == ((membership_tree  l t).[0] <- Some lp'));
		   assert (leaf_updated sz 0 (membership_tree l t) (membership_tree l t'))))


type operation_t : eqtype= {
  op_level: nat;
  op_index: index_n op_level;
  op_actor: credential_t;
  op_path: path_t op_level & path_t op_level
}


assume val hash_op: bytes_t -> operation_t -> bytes_t


(* Apply an operation to a state *)
val apply: state_t -> operation_t -> option state_t
let apply g o =
  if o.op_level <> g.st_levels then None
  else let p1,p2 = o.op_path in
       let t' = apply_path o.op_level o.op_index o.op_actor g.st_tree p1 in
       let t' = apply_path o.op_level o.op_index o.op_actor g.st_tree p2 in
       Some ({g with st_epoch = g.st_epoch + 1; st_tree = t';
  	     st_transcript_hash = hash_op g.st_transcript_hash o})

let update_leaf_package (lp:leaf_package_t) (nc:credential_t) = {
  lp with
  leaf_version = lp.leaf_version + 1;
  leaf_credential = nc
}

(* Create an operation that modifies the group state *)
val modify: s:state_t -> actor:index_t s
	-> i:index_t s -> option leaf_package_t
	-> option operation_t

let modify g actor i olp =
  match (membership g).[actor] with
  | None -> None
  | Some mi_a_old ->
    match olp with
    | None -> None
    | Some lp ->
      let mi_a = update_leaf_package mi_a_old lp.leaf_credential in
      let bp = blank_path g.st_levels i olp in
      let nt = apply_path g.st_levels i mi_a.leaf_credential g.st_tree bp in
      match update_path g.st_levels nt i mi_a with
      | None -> None
      | Some up -> Some ({op_level = g.st_levels; op_actor=mi_a.leaf_credential;
	                     op_index = i; op_path = (bp,up)})
