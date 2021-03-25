module TreeSync

open Lib.Array
open Lib.Maths


/// BB:
/// Are we missing an extend operation for the tree?


(* Base datatypes *)
type bytes_t = Seq.seq nat
let empty_bytes = Seq.empty

let pred_p = Type0
let datatype_t = eqtype


(* Cryptography *)
let sign_key_t = bytes_t
let verif_key_t = bytes_t

let enc_key_t = bytes_t
let dec_key_t = bytes_t


(* Identity and Credentials *)
type principal_t = string

type credential_t: eqtype = {
  cred_name: principal_t;
  cred_issuer: principal_t;
  cred_version: nat;
  cred_identity_key: verif_key_t;
  cred_signature: bytes_t;
  cred_enc_key: enc_key_t;
}

assume val validate_credential: credential_t -> bool

val valid_credential_p: credential_t -> pred_p
let valid_credential_p c = validate_credential c


(* Secrets belonging to a Group Member  *)
type leaf_secrets_t: eqtype = {
  identity_sig_key: sign_key_t;
}

(* Public Information about a Group Member *)
type leaf_package_t: eqtype = {
  leaf_credential: credential_t;
  leaf_version: nat;
  leaf_content: bytes_t;
}

let initial_leaf_package_p (olp:option leaf_package_t) =
  match olp with
  | None -> True
  | Some lp -> valid_credential_p lp.leaf_credential /\ lp.leaf_version = 0

let mk_initial_leaf_package (c:credential_t) =
  { leaf_credential = c;
    leaf_version = 0;
    leaf_content = empty_bytes;}


type node_package_t = {
  node_version: nat;
  node_content: bytes_t
}


type index_n (l:nat) = x:nat{x < pow2 l}
type level_n = n:nat{pow2 n < pow2 32}


(* Tree and Paths definitions*)
type tree_t (lev:nat) =
 | Leaf: actor:credential_t{lev=0} -> olp:option leaf_package_t -> tree_t lev
 | Node: actor:credential_t{lev>0} -> onp:option node_package_t ->
         left:tree_t (lev-1) -> right:tree_t (lev-1) -> tree_t lev

type path_t (lev:nat) =
 | PLeaf: olp:option leaf_package_t{lev=0} -> path_t lev
 | PNode: onp:option node_package_t{lev>0} ->
	       next:path_t (lev-1) -> path_t lev

(* Operations on the state *)
type operation_t: eqtype = {
  op_level: nat;
  op_index: index_n op_level;
  op_actor: credential_t;
  op_path: path_t op_level;
}

(* TreeSync state and accessors*)
type state_t: eqtype = {
  st_group_id: nat;
  st_levels: nat;
  st_tree: tree_t st_levels;
  st_version: nat;
  st_transcript: Seq.seq operation_t;
}

val mk_initial_state: gid:nat -> lvl:level_n -> tree_t lvl -> Tot state_t
let mk_initial_state gid lvl t = {
  st_group_id = gid; st_levels = lvl;
  st_tree = t; st_version = 0;
  st_transcript = empty}

val group_id: state_t -> nat
let group_id st = st.st_group_id

val max_size: state_t -> nat
let max_size st = pow2 st.st_levels

val epoch: state_t -> nat
let epoch st = st.st_version

type index_t (st:state_t) = i:nat{i < max_size st}


(* Membership *)
type member_array_t (sz:nat) = a:array (option credential_t){length a = sz}

let rec tree_membership (l:nat) (t:tree_t l): member_array_t (pow2 l) =
  match t with
  | Leaf _ olp ->
    (match olp with
    | None -> singleton None
    | Some lp -> singleton (Some lp.leaf_credential))
  | Node _ _ left right -> append (tree_membership (l-1) left)
				 (tree_membership (l-1) right)


val membership: st:state_t -> member_array_t (max_size st)
let membership st = tree_membership st.st_levels st.st_tree



(* Auxiliary tree functions *)
type direction_t = | Left | Right

let dual (d:direction_t) : direction_t =
  match d with
  | Left -> Right
  | Right -> Left

let child_index (l:pos) (i:index_n l) : index_n (l-1) & direction_t =
  if i < pow2 (l - 1) then (i, Left) else (i-pow2 (l-1), Right)

let order_subtrees dir (l,r) = if dir = Left then (l,r) else (r,l)



(* Create a new tree from a member array *)
val create_tree: l:nat -> actor:credential_t ->
		 init:member_array_t (pow2 l) ->
		 t:tree_t l{tree_membership l t == init}

let rec create_tree (l:nat) (actor:credential_t) (init:member_array_t (pow2 l)) =
  if l = 0 then
    match init.[0] with
    | None -> Leaf actor None
    | Some c -> Leaf actor (Some (mk_initial_leaf_package c))
  else
    let init_l,init_r = split init (pow2 (l-1)) in
    let left = create_tree (l-1) actor init_l in
    let right = create_tree (l-1) actor init_r in
    Node actor None left right


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
let rec blank_path (l:nat) (i:index_n l) (oc:option credential_t) : path_t l =
  if l = 0 then
    match oc with
    | None -> PLeaf None
    | Some c -> PLeaf (Some (mk_initial_leaf_package c)) // BB. This doesn't seem correct.
  else let (j,dir) = child_index l i in
    PNode None (blank_path (l-1) j oc)


let rec mk_path_aux (l:nat) (i:index_n l) (sonp:Seq.seq (option node_package_t){l <= length sonp+1})
                    (olp:option leaf_package_t): path_t l =
   if l = 0 then PLeaf olp
   else
     let (j,dir) = child_index l i in
     PNode None (mk_path_aux (l-1) j sonp olp)

///
/// API
///

(* Create a path for from a sequence of node packages *)
val mk_path: l:nat -> Seq.seq (option node_package_t) -> option leaf_package_t
  -> Tot (option (path_t l))

let rec mk_path l sonp olp =
  if l = 0 || length sonp + 1 <> l then None
  else Some (mk_path_aux l 0 sonp olp)


(* Create an operation that modifies the group state *)
val mk_operation: st:state_t -> actor:credential_t
  -> i:index_t st -> p:path_t st.st_levels
  -> Tot (option operation_t)

let mk_operation st actor i p =
  match (membership st).[i], (PLeaf?.olp p) with
  | _ -> None
  | Some mc, Some lp ->
  if mc = lp.leaf_credential then None
  else
    Some ({op_level = st.st_levels;
           op_index = i;
           op_actor = actor;
           op_path = p;})


(* Create a new group state *)
val create: gid:nat -> sz:pos -> init:member_array_t sz
  -> Tot (option state_t)

let create gid sz init =
  match init.[0], log2 sz with
  | _ -> None
  | Some actor,Some lvl ->
    let t = create_tree lvl actor init in
	 let st = mk_initial_state gid lvl t in
	 Some ({st with st_transcript = empty_bytes})


(* Apply an operation to a state *)
val apply: state_t -> operation_t
  -> Tot (option state_t)

let apply st op =
  if op.op_level <> st.st_levels then None
  else
    let nt = apply_path op.op_level op.op_index op.op_actor st.st_tree op.op_path in
    Some ({ st with st_version = st.st_version + 1; st_tree = nt;
            st_transcript = Seq.snoc st.st_transcript op})


(* Add a new joiner *)
val add: st:state_t -> actor:credential_t
  -> i:index_t st -> joiner:credential_t
  -> Tot (option (operation_t & state_t))

let add st actor i joiner =
  let p = blank_path st.st_levels i (Some joiner) in
  match mk_operation st actor i p with
  | None -> None
  | Some op ->
  match apply st op with
  | None -> None
  | Some st' -> Some (op,st')


(* Remove a member *)
val remove: st:state_t -> actor:credential_t -> i:index_t st
  -> Tot (option (operation_t & state_t))

let remove st actor i =
  let p = blank_path st.st_levels i None in
  match mk_operation st actor i p with
  | None -> None
  | Some op ->
  match apply st op with
  | None -> None
  | Some st' -> Some (op,st')

