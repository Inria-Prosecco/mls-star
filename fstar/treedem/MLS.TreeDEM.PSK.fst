module MLS.TreeDEM.PSK

open Comparse
open MLS.Crypto
open MLS.TreeDEM.NetworkTypes
open MLS.Result

#set-options "--fuel 0 --ifuel 0"

// Compute psk_secret[i+1] given psk[i], psk_label[i] and psk_secret[i]
val compute_psk_secret_step:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  psk_label_nt bytes -> bytes -> bytes ->
  result bytes
let compute_psk_secret_step #bytes #cb label psk prev_psk_secret =
    let? psk_extracted = kdf_extract (zero_vector #bytes) psk in
    let? psk_input = expand_with_label #bytes psk_extracted "derived psk" (serialize (psk_label_nt bytes) label) (kdf_length #bytes) in
    let? new_psk_secret = kdf_extract psk_input prev_psk_secret in
    return (new_psk_secret <: bytes)

// Compute psk_secret[n] given psk_secret[ind]
val compute_psk_secret_aux:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  l:list (pre_shared_key_id_nt bytes & bytes) -> ind:nat{ind <= List.Tot.length l} -> bytes ->
  Tot (result bytes)
  (decreases (List.Tot.length l - ind))
let rec compute_psk_secret_aux #bytes #cb l ind psk_secret_ind =
  if ind = List.Tot.length l then
    return psk_secret_ind
  else (
    let (id, psk) = List.Tot.index l ind in
    let? index = mk_nat_lbytes ind "compute_psk_secret_aux" "index" in
    let? count = mk_nat_lbytes (List.Tot.length l) "compute_psk_secret_aux" "index" in
    let label = ({
      id;
      index;
      count;
    }) in
    let? next_psk_secret = compute_psk_secret_step label psk psk_secret_ind in
    compute_psk_secret_aux l (ind+1) next_psk_secret
  )

val compute_psk_secret:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  list (pre_shared_key_id_nt bytes & bytes) ->
  result bytes
let compute_psk_secret #bytes #cb l =
  compute_psk_secret_aux l 0 (zero_vector #bytes)
