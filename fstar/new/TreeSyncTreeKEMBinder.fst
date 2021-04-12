module TreeSyncTreeKEMBinder

open Lib.ByteSequence
open Crypto
open NetworkTypes
open Parser
module TS = TreeSync
module TK = TreeKEM
open Lib.Result

//TODO I guess this is somewhere in the standard library
assume val pub_to_secret: pb:pub_bytes -> b:bytes{Seq.length b == Seq.length pb}

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
    fail "kem_output has wrong length"
  else
    Success ({
      TK.kem_output = x.hcn_kem_output;
      TK.ciphertext = x.hcn_ciphertext;
    })

val treesync_to_treekem: #l:nat -> cs:ciphersuite -> TS.tree_t l -> result (TK.tree cs l)
let rec treesync_to_treekem #l cs t =
  match t with
  | TS.Leaf _ None ->
    return (TK.Leaf None)
  | TS.Leaf _ (Some lp) ->
    let pk = lp.TS.lp_credential.TS.cred_enc_key in
    if Seq.length pk = hpke_public_key_length cs then
      return (TK.Leaf (Some ({TK.mi_public_key = pub_to_secret pk})))
    else
      fail "cred_enc_key has wrong length"
  | TS.Node _ onp left right -> begin
    tk_left <-- treesync_to_treekem cs left;
    tk_right <-- treesync_to_treekem cs right;
    match onp with
    | None ->
      return (TK.Node None tk_left tk_right)
    | Some np ->
      content <-- from_option "Couldn't parse UpdatePathNode"
        ((ps_to_pse ps_update_path_node).parse_exact (pub_to_secret np.TS.np_content));
      path_secret_ciphertext <-- mapM (encrypted_path_secret_nt_to_tk cs) (Seq.seq_to_list content.upnn_encrypted_path_secret);
      if not (Seq.length content.upnn_public_key = hpke_public_key_length cs) then
        fail ""
      else (
        let kp: TK.key_package cs l = {
          TK.kp_public_key = content.upnn_public_key;
          TK.unmerged_leafs = admit(); //TODO
          TK.path_secret_from = dir_ts_to_tk (np.TS.np_content_dir);
          TK.path_secret_ciphertext = path_secret_ciphertext;
        } in
        admit()
      )
  end
