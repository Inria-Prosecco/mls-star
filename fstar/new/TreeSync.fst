module TreeSync

#set-options "--z3rlimit 50"


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



type result 'a = | Success of 'a | Error of string

type secret = bytes_t
type dec_key_t = bytes_t
type principal_t = string


type credential_t :eqtype = {
  name: principal_t;
  sid:nat;
  version:nat;
  identity_key: verif_key_t;
  issuer: principal_t;
  signature: bytes_t;
}


let name c = c.name
let identity_key c = c.identity_key
assume val validate_: credential_t -> bool
let valid_credential_p c = validate_ c

(* Definition of the main data structures in TreeKEM_B *)
type member_secrets_t :eqtype=   {
     identity_sig_key: sign_key_t;
     leaf_secret:secret;
     current_dec_key: dec_key_t
}

type direction = | Left | Right
type node_package_t = {
  node_from : direction;
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


(* let rec pub_keys (l:nat) (t:tree_t l) : *)
(* 	pks:array enc_key_t{length pks <= pow2 l} = *)
(*   match t with *)
(*   | Leaf _ None -> empty *)
(*   | Leaf _ (Some m) -> singleton (current_enc_key m) *)
(*   | Node _ (Some k) left right -> singleton k.node_enc_key *)
(*   | Node _ None left right -> append (pub_keys (l-1) left) *)
(* 				    (pub_keys (l-1) right) *)

type state_t: eqtype = {
  group_id: nat;
  levels: nat;
  tree: tree_t levels;
  epoch: nat;
  transcript_hash: bytes_t
}

let index_n (l:nat) = x:nat{x < pow2 l}

let group_id g = g.group_id
let max_size g = pow2 g.levels
let epoch g = g.epoch

let rec membership_tree (l:nat) (t:tree_t l) : member_array_t (pow2 l) =
  match t with
  | Leaf _ mi -> singleton mi
  | Node _ _ left right -> append (membership_tree (l-1) left)
				 (membership_tree (l-1) right)
let membership g = membership_tree g.levels g.tree

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
let child_index (l:pos) (i:index_n l) : index_n (l-1) & direction =
  if i < pow2 (l - 1) then (i,Left) else (i-pow2 (l-1),Right)

(* let key_index (l:nat) (i:index_n l) (sib:tree_t l) dir : index_n (l+1) = *)
(*   if dir = Left then i else i + length (pub_keys l sib) *)

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


(* assume val node_kdf: secret -> direction -> array enc_key -> secret *)
(* assume val mpke_enc: secret -> array enc_key -> bytes *)
(* assume val mpke_dec: secret -> i:nat -> eks:array enc_key{i < length eks} -> bytes -> option secret *)
(* assume val pk: secret -> enc_key *)
  
(* val node_encap: secret -> direction -> ekr:array enc_key -> (key_package & secret) *)

(* (\*--- nodeEncapBegin ---*\) *)
(* let node_encap child_secret dir ekr = *)
(*   let secret = node_kdf child_secret dir ekr in *)
(*   let ciphertext = mpke_enc secret ekr in *)
(*   let ek = pk secret in *)
(*   {from = dir; *)
(*    node_enc_key = ek; *)
(*    node_ciphertext = ciphertext}, *)
(*   secret *)
(* (\*--- nodeEncapEnd ---*\) *)

(* val node_decap: secret -> i:nat -> dir:direction -> *)
(* 		kp:key_package -> ekr:array enc_key{dir <> kp.from ==> i < length ekr} -> *)
(* 		option secret *)

(* (\*--- nodeDecapBegin ---*\) *)
(* let node_decap child_secret i dir kp ekr = *)
(*   if dir = kp.from then *)
(*     if i <> 0 then None *)
(*     else Some (node_kdf child_secret dir ekr) *)
(*   else *)
(*     mpke_dec child_secret i ekr kp.node_ciphertext *)
(* (\*--- nodeDecapEnd ---*\) *)


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
		   let g0 = {group_id=gid; levels=l;
			     tree=t'; epoch=0;
			     transcript_hash = empty} in
		   let h0 = hash_state g0 in
		   Some ({g0 with transcript_hash = h0}))

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
  | Some mi -> (exists mi'. m2 == (m1.[i] <- Some mi') /\ name(mi'.leaf_credential) = name(mi.leaf_credential))

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
  if o.op_level <> g.levels then None
  else let p1,p2 = o.op_path in
       let t' = apply_path o.op_level o.op_index o.op_actor g.tree p1 in
       let t' = apply_path o.op_level o.op_index o.op_actor g.tree p2 in
       Some ({g with epoch = g.epoch + 1; tree = t';
  	     transcript_hash = hash_op g.transcript_hash o})


let opt f x = match x with | None -> None | Some x -> Some (f x)
let update_leaf_package (lp:leaf_package_t) (nc:credential_t) = {
  lp with
  leaf_version = lp.leaf_version + 1;
  leaf_credential = nc
}

(* Create an operation that modifies the group state *)
let modify g actor i mi_i oleaf_package =
    match (membership g).[actor] with
    | None -> None
    | Some mi_a_old ->
      match oleaf_package with
      | None -> None
      | Some lp ->
      let mi_a = update_leaf_package mi_a_old lp.leaf_credential in
      let bp = blank_path g.levels i mi_i in
      let nt = apply_path g.levels i mi_a.leaf_credential g.tree bp in
      match update_path g.levels nt i mi_a with
      | None -> None
      | Some up -> Some ({op_level = g.levels; op_actor= mi_a.leaf_credential;
	                     op_index = i; op_path = (bp,up)})



val root_secret: l:nat -> t:tree l -> i:index_l l -> leaf_secret:secret
		    -> option (secret & j:nat{j < length (pub_keys l t)})
(*--- rootSecretBegin ---*)
(* Calculate the subgroup secret for the root of a tree *)
let rec root_secret (l:nat) (t:tree l) (i:index_l l) (leaf_secret:bytes)
	: option (secret & j:nat{j < length (pub_keys l t)}) =
  match t with
  | Leaf _ None -> None
  | Leaf _ (Some mi) -> Some (leaf_secret, 0)
  | Node _ (Some kp) left right ->
    let (j,dir) = child_index l i in
    let (child,_) = order_subtrees dir (left,right) in
    (match root_secret (l-1) child j leaf_secret with
    | None -> None
    | Some (cs,i_cs) ->
      let (_,recipients) = order_subtrees kp.from (left,right) in
      let ek_r = pub_keys (l-1) recipients in
      (match node_decap cs i_cs dir kp ek_r with
       | Some k -> Some (k,0)
       | None -> None))
  | Node _ None left right ->
    let (j,dir) = child_index l i in
    let (child,sib) = order_subtrees dir (left,right) in
    match root_secret (l-1) child j leaf_secret with
    | None -> None
    | Some (cs,i_cs) -> Some (cs,key_index (l-1) i_cs sib dir)
(*--- rootSecretEnd ---*)

(*--- groupSecretBegin ---*)
type group_secret :eqtype = {
     init_secret: secret; hs_secret: secret; sd_secret: secret;
     app_secret: secret; app_generation: nat}
(*--- groupSecretEnd ---*)

assume val derive_epoch_secrets: is:secret -> us:secret -> tx:bytes -> (secret & secret & secret &secret)
assume val derive_epoch_secret: is:secret -> us:secret -> tx:bytes -> secret

(*--- calculateSecretBegin ---*)
(* Calculate the current group secret *)
let calculate_group_secret g i ms gs =
  match root_secret g.levels g.tree i ms.leaf_secret with
  | None -> None
  | Some (rs,_) ->
    let prev_is = if gs = None then empty_bytes
		  else (Some?.v gs).init_secret in
    let (apps,hs,sds,is') =
	 derive_epoch_secrets prev_is rs g.transcript_hash in
    Some ({init_secret = is';hs_secret = hs; sd_secret = sds;
	     app_secret = apps; app_generation = 0})
(*--- calculateSecretEnd ---*)
type content_type = | App | HS | W
type sd_t = | SD: sender:nat -> generation:nat -> sd_t
            | ESD: bytes -> sd_t
type header_t = | HDR: gid:nat -> ep:nat -> cty:content_type -> sd_nonce: bytes -> sd:sd_t -> header_t


let sender_data sender generation = SD sender generation
let header gid epn ct sd_nonce sd = HDR gid epn ct sd_nonce sd
let enc_header gid epn ct sd_nonce sd = HDR gid epn ct sd_nonce (ESD sd)

assume val derive_app_key: es:secret -> sender:nat -> generation:nat -> ae_key & bytes
assume val derive_hs_key: hss:secret -> sender:nat -> ae_key & bytes
assume val derive_hdr_key: hds:secret -> ae_key

assume val wire_message: header_t -> smsg:bytes -> bytes
assume val parse_wire_message: bytes -> option (header_t & bytes)

assume val sign_msg: sign_key -> hdr:header_t -> m:msg -> signed:bytes
assume val signed_content: bytes -> option msg
assume val verify_msg: verif_key -> hdr:header_t -> signed:bytes -> option msg
assume val aead_enc_msg: ae_key -> bytes -> header_t -> bytes -> bytes
assume val aead_dec_msg: ae_key -> bytes -> header_t -> bytes -> option bytes
assume val ae_enc_sd: ae_key -> bytes -> sd_t -> bytes
assume val ae_dec_sd: ae_key -> bytes -> option sd_t
assume val pkaead_enc_msg: enc_key -> bytes -> header_t -> bytes
assume val pkaead_dec_msg: secret -> bytes -> header_t -> option bytes

(*--- encryptAppMsgBegin ---*)
let encrypt_app_message g sender ms gs msg sd_nonce =
  let n = gs.app_generation in
  let sign_key = ms.identity_sig_key in
  let sd = sender_data sender n in
  let plain_hdr = header g.group_id g.epoch App sd_nonce sd in
  let signed_msg = sign_msg sign_key plain_hdr msg in
  let sd_key = derive_hdr_key gs.sd_secret in
  let enc_sd = ae_enc_sd sd_key sd_nonce sd in
  let hdr = enc_header g.group_id g.epoch App sd_nonce enc_sd in
  let content_key,content_nonce = derive_app_key gs.app_secret sender n in
  let enc_msg = aead_enc_msg content_key content_nonce hdr signed_msg in
  (wire_message hdr enc_msg,
   {gs with app_generation = n + 1})
(*--- encryptAppMsgEnd ---*)

val decrypt_app_message: g:group_state -> receiver: index g -> gs:group_secret ->
			 ehdr:header_t -> emsg: bytes -> option (msg & index g & group_secret)
let decrypt_app_message g receiver gs ehdr emsg =
  match ehdr with
  | HDR gid epoch cty sd_nonce (ESD esd) ->
    if gid <> g.group_id || epoch <> g.epoch || cty <> App then None else
    let sd_key = derive_hdr_key gs.sd_secret in
    (match ae_dec_sd sd_key esd with
     | Some (SD sender n) ->
       if sender >= max_size g then None else
       (match (membership g).[sender] with
        | None -> None
	| Some mi ->
	  let verif_key = mi.cred.identity_key in
	  let content_key, content_nonce = derive_app_key gs.app_secret sender n in
	  let hdr = HDR gid epoch App sd_nonce (SD sender n) in
	  (match aead_dec_msg content_key content_nonce hdr emsg with
	   | None -> None
	   | Some signed_msg ->
	     (match verify_msg verif_key hdr signed_msg with
	      | Some (AppMsg n' m) ->
		if n <> n' then None
		else Some (AppMsg n m,sender,gs)
	      | _ -> None)))
      | _ -> None)
  | _ -> None


let encrypt_msg g gs sender keys m sd_nonce =
  match m with
  | AppMsg _ _ -> encrypt_app_message g sender keys gs m sd_nonce
  | Modify o ->
      let sign_key = keys.identity_sig_key in
      let sd = sender_data sender 0 in
      let hdr = header g.group_id g.epoch HS sd_nonce sd in
      let signed_msg = sign_msg sign_key hdr m in
      let content_key,content_nonce = derive_hs_key gs.hs_secret sender in
      let sd_key = derive_hdr_key gs.sd_secret in
      let enc_msg = aead_enc_msg content_key content_nonce hdr signed_msg in
      let enc_sd = ae_enc_sd sd_key sd_nonce sd in
      let enc_hdr = enc_header g.group_id g.epoch HS sd_nonce enc_sd in
      (wire_message enc_hdr enc_msg, gs)
  | Welcome g i s ->
    (match (membership g).[i] with
     | None -> empty_bytes, gs
     | Some mi ->
       let sign_key = keys.identity_sig_key in
       let sd = sender_data sender 0 in
       let hdr = header g.group_id g.epoch W sd_nonce sd in
       let signed_msg = sign_msg sign_key hdr m in
       let c = pkaead_enc_msg (current_enc_key mi) signed_msg hdr in
       (wire_message hdr c, gs))
  | _ ->
      let sign_key = keys.identity_sig_key in
      let sd = sender_data sender 0 in
      let hdr = header g.group_id g.epoch HS sd_nonce sd in
      let signed_msg = sign_msg sign_key hdr m in
      (wire_message hdr signed_msg, gs)

let receive_initial keys c =
  match parse_wire_message c with
  | None -> None
  | Some (hdr,emsg) ->
   (match hdr with
    | HDR gid epoch W sd_nonce (SD sender 0) ->
      (match pkaead_dec_msg keys.leaf_secret emsg hdr with
       | None -> None
       | Some signed_msg ->
	 (match signed_content signed_msg with
	  | None -> None
	  | Some msg ->
	    (match msg with
	     | Welcome g _ _ ->
	       if sender >= max_size g then None else
	       (match (membership g).[sender] with
	        | None -> None
		| Some mi ->
		  let verif_key = mi.cred.identity_key in
		  verify_msg verif_key hdr signed_msg)
            | _ -> None)))
    | HDR gid 0 HS sd_nonce (SD sender 0) ->
      (match signed_content emsg with
       | None -> None
       | Some msg ->
         (match msg with
 	  | Create g ->
  	    if sender >= max_size g then None else
	    (match (membership g).[sender] with
 	     | None -> None
 	     | Some mi ->
	       let verif_key = mi.cred.identity_key in
	       verify_msg verif_key hdr emsg)
          | _ -> None))
    | _ -> None)

