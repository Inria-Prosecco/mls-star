module MLS.TreeDEM.KeyPackageRef

open Comparse
open MLS.NetworkTypes
open MLS.TreeSync.NetworkTypes
open MLS.TreeKEM.NetworkTypes
open MLS.TreeDEM.NetworkTypes
open MLS.Crypto
open MLS.Result

val compute_key_package_ref:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  key_package_nt bytes tkt ->
  result (key_package_ref_nt bytes)
let compute_key_package_ref #bytes #cb kp =
  let kp_bytes: bytes = serialize (key_package_nt bytes tkt) kp in
  let? res = make_keypackage_ref kp_bytes in
  return (res <: mls_bytes bytes)
