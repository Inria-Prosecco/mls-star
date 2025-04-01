module MLS.TreeKEM.Symbolic.Traceful.AllInvariants

open DY.Core
open MLS.TreeKEM.NetworkTypes
open MLS.TreeSync.Symbolic.API
open MLS.Bootstrap.Symbolic.State.InitKey
open MLS.Bootstrap.Symbolic.KeyPackage
open MLS.Bootstrap.Symbolic.GroupInfo
open MLS.Bootstrap.Symbolic.State.KeyPackageStore
open MLS.Bootstrap.Symbolic.Welcome
open MLS.TreeKEM.Symbolic.State.EpochSecrets
open MLS.TreeKEM.Symbolic.State.NodeKey
open MLS.TreeKEM.Symbolic.State.ProposalCache
open MLS.TreeKEM.Symbolic.State.UpdateCache
open MLS.TreeKEM.Symbolic.State.API
open MLS.TreeKEM.Symbolic.Tree.Labels
open MLS.TreeKEM.Symbolic.Tree.Operations
open MLS.TreeKEM.Symbolic.EpochEvent
open MLS.TreeKEM.Symbolic.KeySchedule
open MLS.TreeKEM.Symbolic.State.OnePSKStore
open MLS.TreeKEM.Symbolic.State.PSKStore

val has_treesync_and_treekem_invariants:
  {|protocol_invariants|} ->
  prop
let has_treesync_and_treekem_invariants #invs =
  has_mls_keyschedule_invariants /\
  has_key_package_invariant /\
  has_treesync_treekem_link_invariants /\
  has_bootstrap_init_key_state_invariant /\
  has_bootstrap_key_package_store_state_invariant /\
  has_bootstrap_crypto_invariants /\
  has_i_am_in_group_invariant /\
  has_group_info_tbs_invariant /\
  has_treesync_treekem_state_invariant /\
  has_treekem_epoch_secret_state_invariant /\
  has_treekem_node_keys_state_invariant /\
  has_proposal_cache_invariant /\
  has_update_cache_invariant /\
  has_one_psk_state_invariant /\
  has_psk_store_invariant /\
  has_mls_treekem_invariants /\
  has_treesync_invariants tkt
