module MLS.TreeSync

open MLS.Lib.Array
open MLS.Lib.Maths
open Lib.ByteSequence
open MLS.Utils
open MLS.Tree

//Theophile: these types are needed on my computer
let bytes_t = bytes
let pub_bytes_t = pub_bytes
let pub_bytes_empty: pub_bytes = Seq.empty

(** Cryptography *)
let sign_key_t = bytes_t
let verif_key_t = pub_bytes_t

let enc_key_t = pub_bytes_t
let dec_key_t = bytes_t


(** Identity and Credentials *)
type principal_t = string

type credential_t = {
  cred_version: nat;
  cred_identity: pub_bytes;
  cred_signature_key: verif_key_t;
}

assume val validate_credential: credential_t -> bool


(** Secrets belonging to a Group member  *)
noeq type leaf_secrets_t = {
  identity_sig_key: sign_key_t;
}

(** Definition of a Leaf package *)
type leaf_package_t = {
  lp_credential: credential_t;
  lp_version: nat;
  lp_content: pub_bytes_t;
  lp_extensions: pub_bytes_t;
  lp_signature: pub_bytes_t;
}

let mk_initial_leaf_package (c:credential_t) =
  { lp_credential = c;
    lp_version = 0;
    lp_content = pub_bytes_empty;
    lp_extensions = pub_bytes_empty;
    lp_signature = admit();}


(** Definition of a Node package *)
//type direction_t = | Left | Right
type node_package_t = {
  np_version: nat;
  np_content_dir: direction;
  np_unmerged_leafs: list nat;
  np_parent_hash: pub_bytes_t;
  np_content: pub_bytes_t;
}


(** Tree and Paths definitions *)
//type index_n (l:nat) = x:nat{x < pow2 l}
type level_n = nat

type treesync (l:level_n) (n:tree_size l) = tree l n (credential_t & option leaf_package_t) (credential_t & option node_package_t)
type pathsync (l:level_n) (n:tree_size l) (i:leaf_index n) = path l n i (option leaf_package_t) (option node_package_t)
//type tree_t (l:level_n) =
// | Leaf: actor:credential_t{l=0} -> olp:option leaf_package_t -> tree_t l
// | Node: actor:credential_t{l>0} -> onp:option node_package_t ->
//         left:tree_t (l-1) -> right:tree_t (l-1) -> tree_t l

//type path_t (l:level_n) =
// | PLeaf: olp:option leaf_package_t{l=0} -> path_t l
// | PNode: onp:option node_package_t{l>0} ->
//	       next:path_t (l-1) -> path_t l

(** Operations on the state *)
type operation_t = {
  op_levels: level_n;
  op_treesize: tree_size op_levels;
  op_index: leaf_index op_treesize;
  op_actor: credential_t;
  op_path: pathsync op_levels op_treesize op_index;
}

(** TreeSync state and accessors *)
type state_t = {
  st_group_id: nat;
  st_levels: level_n;
  st_treesize: tree_size st_levels;
  st_tree: treesync st_levels st_treesize;
  st_version: nat;
  st_initial_tree: treesync st_levels st_treesize;
  st_transcript: Seq.seq operation_t;
}

val mk_initial_state: gid:nat -> l:level_n -> n:tree_size l -> treesync l n -> Tot state_t
let mk_initial_state gid l n t = {
  st_group_id = gid; st_levels = l;
  st_treesize = n;
  st_tree = t; st_version = 0;
  st_initial_tree = t;
  st_transcript = empty;}

val group_id: state_t -> nat
let group_id st = st.st_group_id

val max_size: state_t -> nat
let max_size st = pow2 st.st_levels

val epoch: state_t -> nat
let epoch st = st.st_version

type index_t (st:state_t) = i:nat{i < st.st_treesize}


(** Membership *)
type member_array_t (sz:nat) = a:array (option credential_t){length a = sz}

let rec tree_membership (#l:nat) (#n:tree_size l) (t:treesync l n): member_array_t n =
  match t with
  | TLeaf (_, olp) ->
    (match olp with
    | None -> singleton None
    | Some lp -> singleton (Some lp.lp_credential))
  | TSkip _ t' -> tree_membership t'
  | TNode (_,_) left right -> append (tree_membership left)
				 (tree_membership right)

val membership: st:state_t -> member_array_t (st.st_treesize)
let membership st = tree_membership st.st_tree


(** Auxiliary tree functions *)
let dual (d:direction) : direction =
  match d with
  | Left -> Right
  | Right -> Left

//let child_index (l:pos) (i:index_n l) : index_n (l-1) & direction_t =
//  if i < pow2 (l - 1) then (i, Left) else (i-pow2 (l-1), Right)

//let order_subtrees dir (l,r) = if dir = Left then (l,r) else (r,l)


(** Create a new tree from a member array *)
val create_tree: l:level_n -> n:tree_size l -> actor:credential_t ->
		 init:member_array_t n ->
		 t:treesync l n{tree_membership t == init}

let rec create_tree (l:level_n) (n:tree_size l) (actor:credential_t) (init:member_array_t n) =
  if l = 0 then
    match init.[0] with
    | None -> TLeaf (actor, None)
    | Some c -> TLeaf (actor, (Some (mk_initial_leaf_package c)))
  else
    if n <= (pow2 (l-1)) then
      TSkip _ (create_tree (l-1) n actor init)
    else
      let init_l,init_r = split init (pow2 (l-1)) in
      let left = create_tree (l-1) (pow2 (l-1)) actor init_l in
      let right = create_tree (l-1) (n - pow2 (l-1)) actor init_r in
      TNode (actor, None) left right


(** Apply a path to a tree *)
let rec apply_path (#l:level_n) (#n:tree_size l) (#i:leaf_index n) (a:credential_t)
                   (t:treesync l n) (p:pathsync l n i) : treesync l n =
  match t,p with
  | TLeaf (_, m), PLeaf m' -> TLeaf (a, m')
  | TSkip _ t', PSkip _ p' -> TSkip _ (apply_path a t' p')
  | TNode (_, _) left right, PNode onp next ->
     let (|dir,_|) = child_index l i in
     if dir = Left
     then TNode (a, onp) (apply_path a left next) right
     else TNode (a, onp) left (apply_path a right next)


(** Create a blank path after modifying a leaf *)
let rec blank_path (l:level_n) (n:tree_size l) (i:leaf_index n) (oc:option credential_t) : pathsync l n i =
  if l = 0 then
    match oc with
    | None -> PLeaf None
    | Some c -> PLeaf (Some (mk_initial_leaf_package c))
  else if n <= pow2 (l-1) then
    PSkip _ (blank_path (l-1) n i oc)
  else
    let (|dir,j|) = child_index l i in
    PNode None (blank_path (l-1) (if dir = Left then (pow2 (l-1)) else (n - (pow2 (l-1)))) j oc)

let rec unmerged_path (#l:level_n) (#n:tree_size l) (leaf_index:leaf_index n) (t:treesync l n) (cred:credential_t): pathsync l n leaf_index =
  match t with
  | TLeaf (_, _) ->
    PLeaf (Some (mk_initial_leaf_package cred))
  | TSkip _ t' -> PSkip _ (unmerged_path leaf_index t' cred)
  | TNode (_, onp) left right ->
    let (|dir, new_leaf_index|) = child_index l leaf_index in
    let (child, _) = order_subtrees dir (left, right) in
    let path_next = unmerged_path new_leaf_index child cred in
    match onp with
    | None ->
      PNode None path_next
    | Some np ->
      PNode (Some (
        {np with np_unmerged_leafs = insert_sorted leaf_index np.np_unmerged_leafs}
      )) path_next

///
/// API
///

(** Create an operation that modifies the group state *)
val mk_operation: st:state_t -> actor:credential_t
  -> i:index_t st -> p:pathsync st.st_levels st.st_treesize i
  -> Tot (option operation_t)

let mk_operation st actor i p =
  match (membership st).[i], (PLeaf?.data p) with
  | _ -> None
  | Some mc, Some lp ->
  if mc = lp.lp_credential then None
  else
    Some ({op_levels = st.st_levels;
           op_treesize = st.st_treesize;
           op_index = i;
           op_actor = actor;
           op_path = p;})


(** Create a new group state *)
val create: gid:nat -> sz:pos -> init:member_array_t sz
  -> Tot (option state_t)

let create gid sz init =
  match init.[0], log2 sz with
  | _ -> None
  | Some actor,Some l ->
    let t = create_tree l sz actor init in
    let st = mk_initial_state gid l sz t in
    Some ({st with st_initial_tree = t;
                   st_transcript = bytes_empty})


(** Apply an operation to a state *)
val apply: state_t -> operation_t
  -> Tot (option state_t)

let apply st op =
  if op.op_levels <> st.st_levels || op.op_treesize <> st.st_treesize then None
  else
    let nt = apply_path op.op_actor st.st_tree op.op_path in
    Some ({ st with st_version = st.st_version + 1; st_tree = nt;
            st_transcript = Seq.snoc st.st_transcript op})


(** Add a new joiner *)
val add: st:state_t -> actor:credential_t
  -> i:index_t st -> joiner:credential_t
  -> Tot (option (operation_t & state_t))

let add st actor i joiner =
  let p = unmerged_path i st.st_tree joiner in
  match mk_operation st actor i p with
  | None -> None
  | Some op ->
  match apply st op with
  | None -> None
  | Some st' -> Some (op,st')


(** Remove a member *)
val remove: st:state_t -> actor:credential_t -> i:index_t st
  -> Tot (option (operation_t & state_t))

let remove st actor i =
  let p = blank_path st.st_levels st.st_treesize i None in
  match mk_operation st actor i p with
  | None -> None
  | Some op ->
  match apply st op with
  | None -> None
  | Some st' -> Some (op,st')

