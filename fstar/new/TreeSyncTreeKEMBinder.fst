module TreeSyncTreeKEMBinder

open Lib.ByteSequence
open Crypto
open NetworkTypes
open Parser
module TS = TreeSync
module TK = TreeKEM
open Lib.Result

//TODO I guess this is somewhere in the standard library
val pub_to_secret: pb:pub_bytes -> b:bytes{Seq.length b == Seq.length pb}
let pub_to_secret pb =
  let open Lib.IntTypes in
  Seq.seq_of_list (List.Tot.map (fun x -> u8 (v x)) (Seq.seq_to_list pb))

//TODO this shouldn't exist if the rest of the code (parsers, treekem) was written correctly
val secret_to_pub: b:bytes -> pb:pub_bytes{Seq.length b == Seq.length pb}
let secret_to_pub b =
  let open Lib.IntTypes in
  Seq.seq_of_list (List.Tot.map (fun x -> byte (v x)) (Seq.seq_to_list b))

//TODO They should be the same type
let dir_ts_to_tk (dir:TS.direction_t) =
  match dir with
  | TS.Left -> TK.Left
  | TS.Right -> TK.Right
let dir_tk_to_ts (dir:TK.direction) =
  match dir with
  | TK.Left -> TS.Left
  | TK.Right -> TS.Right

let encrypted_path_secret_nt_to_tk (cs:ciphersuite) (x:hpke_ciphertext_nt): result (TK.path_secret_ciphertext cs) =
  if not (Seq.length x.hcn_kem_output = hpke_kem_output_length cs) then
    fail "encrypted_path_secret_nt_to_tk: kem_output has wrong length"
  else
    return ({
      TK.kem_output = x.hcn_kem_output;
      TK.ciphertext = x.hcn_ciphertext;
    })

let nat_to_index_l (l:nat) (x:nat): result (TK.index_l l) =
  if not (x < pow2 l) then
    fail "nat_to_index_l: unmerged leaf index is too big"
  else
    return x

val treesync_to_treekem: #l:nat -> cs:ciphersuite -> TS.tree_t l -> result (TK.tree cs l)
let rec treesync_to_treekem #l cs t =
  match t with
  | TS.Leaf _ None ->
    return (TK.Leaf None)
  | TS.Leaf _ (Some lp) ->
    pk <-- from_option "treesync_to_treekem: Couldn't parse HPKEPublicKey"
      ((ps_to_pse ps_hpke_public_key).parse_exact (pub_to_secret lp.TS.lp_content));
    if Seq.length pk = hpke_public_key_length cs then
      return (TK.Leaf (Some ({TK.mi_public_key = pk; TK.mi_version = lp.TS.lp_version})))
    else
      fail "treesync_to_treekem: public key has wrong length"
  | TS.Node _ onp left right -> begin
    tk_left <-- treesync_to_treekem cs left;
    tk_right <-- treesync_to_treekem cs right;
    match onp with
    | None ->
      return (TK.Node None tk_left tk_right)
    | Some np ->
      content <-- from_option "treesync_to_treekem: Couldn't parse UpdatePathNode"
        ((ps_to_pse ps_update_path_node).parse_exact (pub_to_secret np.TS.np_content));
      path_secret_ciphertext <-- mapM (encrypted_path_secret_nt_to_tk cs) (Seq.seq_to_list content.upnn_encrypted_path_secret);
      unmerged_leafs <-- mapM (nat_to_index_l l) (np.TS.np_unmerged_leafs);
      if not (Seq.length content.upnn_public_key = hpke_public_key_length cs) then
        fail ""
      else (
        let kp: TK.key_package cs l = {
          TK.kp_public_key = content.upnn_public_key;
          TK.kp_version = np.TS.np_version;
          TK.kp_unmerged_leafs = unmerged_leafs;
          TK.kp_path_secret_from = dir_ts_to_tk (np.TS.np_content_dir);
          TK.kp_path_secret_ciphertext = path_secret_ciphertext;
        } in
        return (TK.Node (Some kp) tk_left tk_right)
      )
  end

let encrypted_path_secret_tk_to_nt (#cs:ciphersuite) (x:TK.path_secret_ciphertext cs): result (hpke_ciphertext_nt) =
  if not (Seq.length x.TK.kem_output < pow2 16) then
    fail "encrypted_path_secret_tk_to_nt: kem_output too long"
  else if not (Seq.length x.TK.ciphertext < pow2 16) then
    fail "encrypted_path_secret_tk_to_nt: ciphertext too long"
  else
    return ({
      hcn_kem_output = x.TK.kem_output;
      hcn_ciphertext = x.TK.ciphertext;
    })


val treekem_to_treesync: #l:nat -> #cs:ciphersuite -> TS.credential_t -> TK.path cs l -> result (TS.path_t l)
let rec treekem_to_treesync #l #cs cred p =
  match p with
  | TK.PLeaf mi ->
    return (TS.PLeaf (Some ({
      TS.lp_credential = cred;
      TS.lp_version = mi.TK.mi_version;
      TS.lp_content = secret_to_pub (ps_hpke_public_key.serialize mi.TK.mi_public_key);
    })))
  | TK.PNode kp p_next ->
    next <-- treekem_to_treesync cred p_next;
    ciphertexts <-- mapM encrypted_path_secret_tk_to_nt kp.TK.kp_path_secret_ciphertext;
    if not (byte_length ps_hpke_ciphertext ciphertexts < pow2 16) then
      fail "treekem_to_treesync: ciphertexts too long"
    else begin
      Seq.lemma_list_seq_bij ciphertexts;
      let np_content = ps_update_path_node.serialize ({
        upnn_public_key = kp.TK.kp_public_key;
        upnn_encrypted_path_secret = Seq.seq_of_list ciphertexts;
      }) in
      let np = ({
        TS.np_version = kp.TK.kp_version;
        TS.np_content_dir = dir_tk_to_ts kp.TK.kp_path_secret_from;
        TS.np_unmerged_leafs = List.Tot.map (fun (x:TK.index_l l) -> (x<:nat)) kp.TK.kp_unmerged_leafs;
        TS.np_content = secret_to_pub np_content;
      }) in
      return (TS.PNode (Some np) next)
    end
