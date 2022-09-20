module MLS.TreeSync.Symbolic.API.GroupManager

open Comparse
open MLS.NetworkTypes
open ComparseGlue
open GlobalRuntimeLib
open LabeledRuntimeAPI
open MLS.Symbolic
open MLS.Symbolic.MapSession

(*** Group manager types & invariants ***)

type group_manager_value (bytes:Type0) {|bytes_like bytes|} = {
  [@@@ with_parser #bytes ps_nat]
  si_public: nat;
  [@@@ with_parser #bytes ps_nat]
  si_private: nat;
}

%splice [ps_group_manager_value] (gen_parser (`group_manager_value))
%splice [ps_group_manager_value_is_valid] (gen_is_valid_lemma (`group_manager_value))

val group_manager_types: map_types dy_bytes
let group_manager_types = {
  key = mls_bytes dy_bytes;
  ps_key = ps_mls_bytes;
  value = group_manager_value dy_bytes;
  ps_value = ps_group_manager_value;
}

val group_manager_pred: map_predicate group_manager_types
let group_manager_pred = {
  pred = (fun gu time (group_id:group_manager_types.key) value ->
    is_publishable gu time group_id
  );
  pred_later = (fun gu time0 time1 key value -> ());
  pred_is_msg = (fun gu time key value -> ());
}

val group_manager_label: string
let group_manager_label = "MLS.TreeSync.GroupManager"

val has_group_manager_invariant: preds -> prop
let has_group_manager_invariant pr =
  has_map_session_invariant group_manager_types group_manager_pred group_manager_label pr

(*** Group manager API ***)

let initialize_group_manager = initialize_map group_manager_types group_manager_pred group_manager_label
let add_new_group_sessions = add_key_value group_manager_types group_manager_pred group_manager_label
let find_group_sessions = find_value group_manager_types group_manager_pred group_manager_label
