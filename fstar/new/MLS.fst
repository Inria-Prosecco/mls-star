module MLS

open FStar.Mul
open Lib.IntTypes
open Lib.Sequence
open Lib.ByteSequence
open Lib.Result

open Crypto


type entropy_t
type principal_t
type pub_key_t = pub_bytes
type priv_key_t = bytes
type kem_t
type kdf_t
type aead_t
type enc_key_t = pub_bytes
type dec_key_t = bytes
type ciphersuite_t = kem_t & kdf_t & aead_t


type direction_t = | Left | Right

let dual (d:direction_t) : direction_t =
  match d with
  | Left -> Right
  | Right -> Left

val mk_kdf_context:
    label: string
  -> salt: bytes
  -> sk_me: bytes
  -> pkl: Seq.seq pub_bytes
  -> dir: direction_t ->
  Tot bytes

let mk_kdf_context label salt sk_me pkl dir = empty_bytes

assume val secret_derive:
    s: bytes
  -> ctx: bytes ->
  Tot (result bytes)


val mpke_encrypt_secret:
    pks: Seq.seq pub_bytes
  -> s: bytes ->
  Tot (result (Seq.seq pub_bytes))
  (decreases (Seq.length pks))

let rec mpke_encrypt_secret pks s =
  if Seq.length pks = 0 then Success Seq.empty else (
  if Seq.length pks = 0 then Success Seq.empty else (
    e1 <-- pke_enc (Seq.index pks 0) s;
    es <-- mpke_encrypt_secret (Seq.slice pks 1 (Seq.length pks)) s;
    Success (Seq.cons e1 es)))

(** PKE Decryption of one secret from a sequence of PKE encryptions *)
val mpke_decrypt_secret:
  sk: bytes
  -> cl: Seq.seq pub_bytes
  -> i: nat{i < Seq.length cl} ->
  Tot (result bytes)

let mpke_decrypt_secret sk l i =
  pke_dec sk (Seq.index l i)


type credential_t = pub_bytes

type client_t = principal_t
type actor_t = principal_t
type gid_s

type key_package_t

assume val generate_key_package: client_t -> Tot key_package_t


assume val is_member: client_t -> gid_s -> Tot bool

type member_info_r = {
  member: credential_t;
  version: nat;
  leaf_pk: pub_key_t;
}


let level_n = n:nat{pow2 n < max_size_t}
let index_l (lev:nat) = n:nat{n < pow2 lev}



type node_content_r = {
  pk: pub_key_t;
  from: direction_t;
  esk: Seq.seq enc_key_t;
}


type actor_info_t = pub_bytes

noeq type tree (lvl:level_n) =
  | Tleaf: actor_info:actor_info_t -> member_info:option member_info_r{lvl = 0} -> tree lvl
  | Tnode: actor_info:actor_info_t -> content:option node_content_r{lvl > 0} ->
	        left:tree (lvl - 1) -> right:tree (lvl - 1) -> tree lvl

let member_array (lvl:level_n) = lseq (option member_info_r) (pow2 lvl)

let rec membership (#lvl:level_n) (t:tree lvl) : member_array lvl =
  match t with
  | Tleaf a i -> create 1 i
  | Tnode a k l r -> (membership l) @| (membership r)


let has_member (#lvl:level_n) (t:tree lvl) (i:index_l lvl) =
  Some? (membership t).[i]

let member (#lvl:level_n) (t:tree lvl) (i:index_l lvl{has_member t i}): member_info_r =
  Some?.v (membership t).[i]

let rec pub_keys (#lvl:level_n) (t:tree lvl) :
	pks:Seq.seq pub_key_t{Seq.length pks <= pow2 lvl} =
  match t with
  | Tleaf _ None -> Seq.empty
  | Tleaf _ (Some m) -> Seq.create 1 (m.leaf_pk)
  | Tnode _ None l r -> Seq.append (pub_keys l) (pub_keys r)
  | Tnode _ (Some k) l r -> Seq.create 1 (k.pk)

noeq type path (lvl:level_n) =
  | Pleaf: actor_info:actor_info_t -> member_info:option member_info_r{lvl = 0} -> path lvl
  | Pnode: actor_info:actor_info_t -> content:option node_content_r{lvl > 0} -> path (lvl - 1) -> path lvl

noeq type proposal_t (lvl:level_n) =
  | Add of path lvl
  | Update of path lvl
  | Remove of path lvl

type commit_t = lvl:level_n & seq (proposal_t lvl) & entropy_t

noeq type msg_i =
  | Welcome
  | Proposal of lvl:level_n & proposal_t lvl
  | Commit of commit_t



let child_index (#lvl:level_n{lvl > 0}) (i:index_l lvl) : index_l (lvl - 1) & direction_t =
  let mid = pow2 (lvl - 1) in
  if i < mid then (i,Left)
  else (i-mid,Right)

let parent_key_index (#lvl:level_n) (i:index_l lvl) (sibling:tree lvl) (dir:direction_t) : index_l (lvl + 1) =
  if dir = Left then i
  else i + Seq.length (pub_keys sibling)

let swap_children (#lvl:level_n{lvl > 0}) (i:index_l lvl) (l:tree (lvl - 1)) (r:tree (lvl - 1))
  : (index_l (lvl - 1) & direction_t & tree (lvl-1) & tree (lvl-1)) =
  let (j,dir) = child_index i in
  if dir = Left then (j,dir,l,r)
  else (j,dir,r,l)

val seq_split: #a:Type -> s:seq a -> n:nat -> r:(seq a & seq a){
  let s1,s2 = r in
  if n >= Seq.length s then
  (s1 == s /\ s2 == Seq.empty)
  else ((s1,s2) == Seq.split s n)}

let seq_split #a s n =
  if n >= Seq.length s then
    (Seq.Base.append_empty_r s;
    (s,Seq.empty))
  else if n = 0 then
    ( Seq.Base.append_empty_l s;
      (Seq.empty,  s))
  else (let s1,s2 = Seq.split s n in
	Seq.Properties.lemma_split s n;
	(s1,s2))


val create_tree:
    lvl: level_n
  -> actor: actor_info_t
  -> mis: seq (option member_info_r){Seq.length mis <= pow2 lvl} ->
  Tot (tree lvl)

let rec create_tree lvl actor ps =
  if lvl = 0 then
    if Seq.length ps = 0 then Tleaf actor None
    else (
      let opi = Seq.index ps 0 in
      match opi with
      | None -> Tleaf actor None
      | Some mi -> Tleaf actor (Some ({member = mi.member; version = 0; leaf_pk = mi.leaf_pk})))
  else
    let mid = pow2 (lvl - 1) in
    let (x, y) = seq_split ps mid in
    let l = create_tree (lvl - 1) actor x in
    let r = create_tree (lvl - 1) actor y in
    Tnode actor None l r

val apply_path: #lvl:level_n -> tree lvl -> i:index_l lvl -> path lvl -> Tot (tree lvl)
let rec apply_path #lvl t i p =
  match t,p with
  | Tleaf _ m, Pleaf a m' -> Tleaf a m'
  | Tnode _ _ l r, Pnode a nk next ->
     let (j,dir) = child_index i in
     if dir = Left
     then Tnode a nk (apply_path l j next) r
     else Tnode a nk l (apply_path r j next)


#push-options "--z3rlimit 500"

val calculate_secret:
  #lev: level_n
  -> t: tree lev
  -> i: index_l lev{has_member t i}
  -> leaf_sk: bytes ->
  Tot (result (bytes & index_l lev))

let rec calculate_secret #lev t i leaf_sk =
  match t with
  | Tleaf _ (Some info) -> Success (leaf_sk, 0)
  | Tnode _ None l r ->
    let (j,dir,me,sibling) = swap_children i l r in
    ski <-- calculate_secret me j leaf_sk;
    let (sk,i) = ski in
    Success (sk, parent_key_index i sibling dir)
  | Tnode _ (Some nc) l r -> (
    let (j,dir,me,sibling) = swap_children i l r in
    let i0: index_l lev = 0 in
    ski <-- calculate_secret me j leaf_sk;
    let (sk_me,i) = ski in
    let pk_me = pub_keys me in
    let pk_sibling = pub_keys sibling in
    if nc.from = dir then
	   if Seq.length pk_me = 1 then
	     let ctx = mk_kdf_context "node secret" empty_bytes sk_me pk_sibling nc.from in
	     sk' <-- secret_derive sk_me ctx;
	     Success (sk', i0)
	   else Error "Cannot calculate_secret"
    else (
      if Seq.length nc.esk <= i then Error "Not enough ciphertexts" else (
	   let ctx = mk_kdf_context "decryption key" empty_bytes sk_me Seq.empty Left in
	   dk <-- secret_derive sk_me ctx;
	   sk' <-- mpke_decrypt_secret dk nc.esk i;
	   Success (sk',i0))))

val update_path :
  #lvl: level_n
  -> t: tree lvl
  -> i: index_l lvl
  -> m: member_info_r
  -> leaf_sk: bytes ->
  Tot (result (path lvl & bytes & pub_bytes))

let rec update_path #lev t i m leaf_sk =
  match t with
  | Tleaf _ None -> Error "0: Could not update_path"
  | Tleaf _ (Some info) ->
    if m.member = info.member &&
       m.version > info.version then
	   Success (Pleaf m.member (Some m), leaf_sk, m.leaf_pk)
    else Error "1: Could not update_path"
  | Tnode _ k l r ->
    let (i,from,send,recv) = swap_children i l r in
    psk <-- update_path send i m leaf_sk;
    let ( p, sk, pk ) = psk in
    let pk_r = pub_keys recv in
    if (Seq.length pk_r = 0) then (
	   let p': path lev =
	     Pnode m.member (Some ({
		     from = from;
		     pk = pk;
		     esk = Seq.empty})) p in
	   Success (p', sk, pk))
    else (
	   let ctx = mk_kdf_context "node secret" empty_bytes sk (pub_keys recv)  from in
	   s' <-- secret_derive sk ctx;
 	   let ctx' = mk_kdf_context "decryption key" empty_bytes s' Seq.empty Left in
	   dk <-- secret_derive s' ctx';
	   ek <-- secret_to_public dk;
	   c <-- mpke_encrypt_secret (pub_keys recv) s';
	   let p': path lev =
	     Pnode m.member (Some ({
		            from = from;
		            pk = ek;
		            esk = c})) p in
	   Success (p', s', ek))


val blank_path:
    #lev: level_n
  -> t: tree lev
  -> a: actor_info_t
  -> i: index_l lev
  -> m: option member_info_r ->
  Tot (result (path lev))

let rec blank_path #lev t a i m =
  match t,m with
  | Tleaf _ info, None -> Success (Pleaf a None)
  | Tleaf _ None, Some info -> Success (Pleaf a (Some info))
  | Tnode _ k l r, m ->
    let (i,from,send,recv) = swap_children i l r in
    p <-- blank_path send a i m;
    let p': path lev = Pnode a None p in
    Success (p')
  | _ -> Error "Could not blank_path"


val modify_paths:
    #lev: level_n
  -> t: tree lev
  -> sender_index: index_l lev
  -> new_sender: member_info_r
  -> new_sender_leaf_secret: dec_key_t
  -> member_index: index_l lev
  -> new_member:option member_info_r ->
  Tot (result (list (path lev)))

let modify_paths #lev t si s leaf_sk i m =
  if si = i then
    match m with
    | None ->
      (psk <-- update_path t si s leaf_sk;
       let (p,sk,pk) = psk in
       Success [p])
    | _ -> Error "Could not modify_path"
  else (
    p1 <-- blank_path t s.member i m;
    let t' = apply_path t i p1 in
    psk <-- update_path t si s leaf_sk;
    let (p2,sk,pk) = psk in
    Success [p1; p2])

