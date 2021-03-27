module TreeSync

open Lib.Array
open Lib.Maths
open Lib.ByteSequence


(* Cryptography *)
let sign_key_t = bytes_t
let verif_key_t = pub_bytes_t

let enc_key_t = pub_bytes_t
let dec_key_t = bytes_t


(* Identity and Credentials *)
type principal_t = string

type credential_t = {
  cred_name: principal_t;
  cred_issuer: principal_t;
  cred_version: nat;
  cred_identity_key: verif_key_t;
  cred_signature: pub_bytes_t;
  cred_enc_key: enc_key_t;
}

assume val validate_credential: credential_t -> bool


(* Secrets belonging to a Group Member  *)
noeq type leaf_secrets_t = {
  identity_sig_key: sign_key_t;
}

(* Public Information about a Group Member *)
type leaf_package_t = {
  leaf_credential: credential_t;
  leaf_version: nat;
  leaf_content: pub_bytes_t;
}

let mk_initial_leaf_package (c:credential_t) =
  { leaf_credential = c;
    leaf_version = 0;
    leaf_content = pub_bytes_empty;}

type node_package_t = {
  node_version: nat;
  node_content: pub_bytes_t;
}


(* Tree and Paths definitions*)
type index_n (l:nat) = x:nat{x < pow2 l}
type level_n = nat

type tree_t (l:level_n) =
 | Leaf: actor:credential_t{l=0} -> olp:option leaf_package_t -> tree_t l
 | Node: actor:credential_t{l>0} -> onp:option node_package_t ->
         left:tree_t (l-1) -> right:tree_t (l-1) -> tree_t l

type path_t (l:level_n) =
 | PLeaf: olp:option leaf_package_t{l=0} -> path_t l
 | PNode: onp:option node_package_t{l>0} ->
	       next:path_t (l-1) -> path_t l

(* Operations on the state *)
type operation_t = {
  op_level: level_n;
  op_index: index_n op_level;
  op_actor: credential_t;
  op_path: path_t op_level;
}

(* TreeSync state and accessors*)
type state_t = {
  st_group_id: nat;
  st_levels: level_n;
  st_tree: tree_t st_levels;
  st_version: nat;
  st_initial_tree: tree_t st_levels;
  st_transcript: Seq.seq operation_t;
}

val mk_initial_state: gid:nat -> l:level_n -> tree_t l -> Tot state_t
let mk_initial_state gid l t = {
  st_group_id = gid; st_levels = l;
  st_tree = t; st_version = 0;
  st_initial_tree = t;
  st_transcript = empty;}

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
val create_tree: l:level_n -> actor:credential_t ->
		 init:member_array_t (pow2 l) ->
		 t:tree_t l{tree_membership l t == init}

let rec create_tree (l:level_n) (actor:credential_t) (init:member_array_t (pow2 l)) =
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
let rec apply_path (l:level_n) (i:nat{i<pow2 l}) (a:credential_t)
                   (t:tree_t l) (p:path_t l) : tree_t l =
  match t,p with
  | Leaf _ m, PLeaf m' -> Leaf a m'
  | Node _ _ left right, PNode onp next ->
     let (j,dir) = child_index l i in
     if dir = Left
     then Node a onp (apply_path (l-1) j a left next) right
     else Node a onp left (apply_path (l-1) j a right next)


(* Create a blank path after modifying a leaf *)
let rec blank_path (l:level_n) (i:index_n l) (oc:option credential_t) : path_t l =
  if l = 0 then
    match oc with
    | None -> PLeaf None
    | Some c -> PLeaf (Some (mk_initial_leaf_package c))
  else let (j,dir) = child_index l i in
    PNode None (blank_path (l-1) j oc)


///
/// API
///

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
  | Some actor,Some l ->
    let t = create_tree l actor init in
    let st = mk_initial_state gid l t in
    Some ({st with st_initial_tree = t;
                   st_transcript = bytes_empty})


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

