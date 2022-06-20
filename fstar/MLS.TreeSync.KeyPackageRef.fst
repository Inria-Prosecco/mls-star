module MLS.TreeSync.KeyPackageRef

open Comparse
open MLS.Utils
open MLS.Tree
open MLS.TreeSync.Types
open MLS.NetworkTypes
open MLS.NetworkBinder
open MLS.Crypto
open MLS.Result

val compute_key_package_ref: #bytes:Type0 -> {|crypto_bytes bytes|} -> key_package_nt bytes -> result (key_package_ref_nt bytes)
let compute_key_package_ref #bytes #cb kp =
  let kp_bytes: bytes = serialize (key_package_nt bytes) kp in
  make_keypackage_ref kp_bytes
