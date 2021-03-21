module TreeSync


(* Base datatypes *)
type bytes_t = Seq.seq nat
let empty_bytes = Seq.empty

(* Datastructures operators *)
val lemma_singleton: x:array 'a{length x = 1} -> i:nat{i<length x} ->
  Lemma (singleton x.[i] == x)
	[SMTPat (singleton x.[i])]
let lemma_singleton x i = Seq.lemma_eq_intro (singleton x.[i]) x
let lemma_map_singleton f x = admit()
let lemma_map_append f x y = admit()

let rec foldi (f:'a -> 'b -> 'a) (x:array 'b) (init:'a) (n:nat{n <= length x}) =
  if n = 0 then init
  else f (foldi f x init (n-1)) x.[n-1]

let fold f x a = foldi f x a (length x)


type principal_t = string

type credential_t : eqtype = {
  name: principal_t;
  sid: nat;
  version: nat;
  identity_key: verif_key_t;
  issuer: principal_t;
  signature: bytes_t;
}


let name c = c.name
let identity_key c = c.identity_key
assume val validate_: credential_t -> bool
let valid_credential_p c = validate_ c

(* Secrets associated to a leaf *)
type leaf_secrets_t : eqtype = {
  identity_sig_key: sign_key_t;
}

type direction_t = | Left | Right

type node_package_t = {
  node_from : direction_t;
  node_content: bytes_t
}

type tree_t (lev:nat) =
 | Leaf: actor:credential_t{lev=0} -> mi:option leaf_package_t -> tree_t lev
 | Node: actor:credential_t{lev>0} -> kp:option node_package_t ->
         left:tree_t (lev - 1) -> right:tree_t (lev - 1) -> tree_t lev

type path_t (lev:nat) =
 | PLeaf: mi:option leaf_package_t{lev=0} -> path_t lev
 | PNode: kp:option node_package_t{lev>0} ->
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

let rec membership_tree (l:nat) (t:tree_t l) : member_array_t (pow2 l) =
  match t with
  | Leaf _ mi -> singleton mi
  | Node _ _ left right -> append (membership_tree (l-1) left)
				 (membership_tree (l-1) right)

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
let rec create_tree (l:nat) (c:credential_t)
		    (init:member_array_t (pow2 l)) =
  if l = 0 then Leaf c init.[0]
  else let init_l,init_r = split init (pow2 (l-1)) in
    let left = create_tree (l-1) c init_l in
    let right = create_tree (l-1) c init_r in
    Node c None left right

(* Auxiliary tree functions *)
let child_index (l:pos) (i:index_n l) : index_n (l-1) & direction_t =
  if i < pow2 (l - 1) then (i,Left) else (i-pow2 (l-1),Right)

let order_subtrees dir (l,r) = if dir = Left then (l,r) else (r,l)

(* Apply a path to a tree *)
let rec apply_path (l:nat) (i:nat{i<pow2 l}) (a:credential_t)
                   (t:tree_t l) (p:path_t l) : tree_t l =
  match t,p with
  | Leaf _ m, PLeaf m' -> Leaf a m'
  | Node _ _ left right, PNode nk next ->
     let (j,dir) = child_index l i in
     if dir = Left
     then Node a nk (apply_path (l-1) j a left next) right
     else Node a nk left (apply_path (l-1) j a right next)

(* Create a blank path after modifying a leaf *)
let rec blank_path (l:nat) (i:index_n l) (mi:option leaf_package_t) : path_t l =
  if l = 0 then PLeaf mi
  else let (j,dir) = child_index l i in
    PNode None (blank_path (l-1) j mi)

let rec blank_path_lemma (l:nat) (i:index_n l) (mi:option leaf_package_t) (a:credential_t) (t:tree_t l) :
                    Lemma (let t' = apply_path l i a t (blank_path l i mi) in
                          membership_tree l t' == ((membership_tree l t).[i] <- mi)) =
    match t with
    | Leaf _ _ ->
	   let t' = apply_path l i a t (blank_path l i mi) in
	   Seq.lemma_eq_intro (membership_tree l t') ((membership_tree l t).[i] <- mi)
    | Node _ _ left right ->
      let (j,dir) = child_index l i in
      let (child,sibling) = order_subtrees dir (left,right) in
      let p = PNode None (blank_path (l-1) j mi) in
      blank_path_lemma (l-1) j mi a child;
      let t' = apply_path l i a t (blank_path l i mi) in
      Seq.lemma_eq_intro (membership_tree l t') ((membership_tree l t).[i] <- mi)

let initial_leaf_package (mi:option leaf_package_t) =
  match mi with
  | None -> True
  | Some mi -> valid_credential_p mi.leaf_credential /\ mi.leaf_version = 0

(* Create an update path from a leaf to the root *)
let rec update_path (l:nat) (t:tree_t l) (i:nat{i<pow2 l}) (mi_i:leaf_package_t) : option (path_t l) =
  match t with
  | Leaf _ None -> None
  | Leaf _ (Some mi) -> if name(mi.leaf_credential) = name(mi_i.leaf_credential)
                       then Some (PLeaf (Some mi_i))
                       else None
  | Node _ _ left right ->
     let (j,dir) = child_index l i in
     let (child,sibling) = order_subtrees dir (left,right) in
     match update_path (l-1) child j mi_i with
       | None -> None
       | Some next ->
         let np = {node_from = dir; node_content = empty_bytes} in // BB. TODO.
         Some (PNode (Some np) next)

let rec update_path_lemma (l:nat) (i:nat{i<pow2 l}) (a:credential_t) (t:tree_t l) (mi_i:leaf_package_t):
  Lemma (match update_path l t i mi_i with
		  | None -> True
		  | Some p ->
			 (match (membership_tree l t).[i] with
			 | None -> False
			 | Some mi_old -> name(mi_old.leaf_credential) == name(mi_i.leaf_credential) /\
					           (let t' = apply_path l i a t p in
					           membership_tree l t' = ((membership_tree l t).[i] <- Some mi_i)))) =
   match t with
   | Leaf _ None -> ()
   | Leaf _ (Some mi) ->
     if name(mi.leaf_credential) = name(mi_i.leaf_credential)
     then let p : path_t l = PLeaf (Some mi_i) in
	  let t' = apply_path l i a t p in
	  Seq.lemma_eq_intro (membership_tree l t')
	                     ((membership_tree l t).[i] <- Some mi_i)
     else ()
  | Node _ _ left right ->
     let (j,dir) = child_index l i in
     let (child,sibling) = order_subtrees dir (left,right) in
     match update_path (l-1) child j mi_i with
       | None -> ()
       | Some next ->
         update_path_lemma (l-1) j a child mi_i;
         let np = {node_from = dir; node_content = empty_bytes} in // BB. TODO.
         let p = PNode (Some np) next in
	 let t' = apply_path l i a t p in
	 Seq.lemma_eq_intro (membership_tree l t')
		                 ((membership_tree l t).[i] <- Some mi_i)

assume val hash_state: state_t -> bytes_t

(* Create a new group state *)
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
		    group_id g == gid /\  max_size g == sz /\
		    epoch g == 0      /\
		    leaf_updated sz 0 init (membership g))


let create_lemma gid sz init leaf_secret =
  match init.[0], log2 sz with
  | None,_ -> ()
  | _,None -> ()
  | Some c,Some l ->
    let t = create_tree l c.leaf_credential init in
    let mi' = {leaf_credential = c.leaf_credential; leaf_version = 1} in
    (match update_path l t 0 mi' with
    | None -> ()
    | Some p -> (update_path_lemma l 0 c.leaf_credential t mi';
		   let t' = apply_path l 0 c.leaf_credential t p in
		   assert (membership_tree l t == init);
		   assert (membership_tree l t' == ((membership_tree  l t).[0] <- Some mi'));
		   assert (leaf_updated sz 0 (membership_tree l t) (membership_tree l t'))))


type operation_t : eqtype= {
  op_level: nat;
  op_index: index_n op_level;
  op_actor: credential_t;
  op_path: path_t op_level & path_t op_level
}

assume val hash_op: bytes_t -> operation_t -> bytes_t


(* Apply an operation to a state *)
let apply g o =
  if o.op_level <> g.st_levels then None
  else let p1,p2 = o.op_path in
       let t' = apply_path o.op_level o.op_index o.op_actor g.st_tree p1 in
       let t' = apply_path o.op_level o.op_index o.op_actor g.st_tree p2 in
       Some ({g with st_epoch = g.st_epoch + 1; st_tree = t';
  	     st_transcript_hash = hash_op g.st_transcript_hash o})


let opt f x = match x with | None -> None | Some x -> Some (f x)
let update_leaf_package (lp:leaf_package_t) (nc:credential_t) = {
  lp with
  leaf_version = lp.leaf_version + 1;
  leaf_credential = nc
}

(* Create an operation that modifies the group state *)
let modify g actor i oleaf_package =
  match (membership g).[actor] with
  | None -> None
  | Some mi_a_old ->
    match oleaf_package with
    | None -> None
    | Some lp ->
      let mi_a = update_leaf_package mi_a_old lp.leaf_credential in
      let bp = blank_path g.st_levels i oleaf_package in
      let nt = apply_path g.st_levels i mi_a.leaf_credential g.st_tree bp in
      match update_path g.st_levels nt i mi_a with
      | None -> None
      | Some up -> Some ({op_level = g.st_levels; op_actor=mi_a.leaf_credential;
	                     op_index = i; op_path = (bp,up)})
