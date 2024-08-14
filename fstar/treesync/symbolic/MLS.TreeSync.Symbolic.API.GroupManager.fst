module MLS.TreeSync.Symbolic.API.GroupManager

open Comparse
open DY.Core
open DY.Lib
open MLS.NetworkTypes
open MLS.Symbolic

(*** Group manager types & invariants ***)

[@@ with_bytes dy_bytes]
type group_manager_key  = {
  group_id: mls_bytes dy_bytes;
}

%splice [ps_group_manager_key] (gen_parser (`group_manager_key))
%splice [ps_group_manager_key_is_well_formed] (gen_is_well_formed_lemma (`group_manager_key))

[@@ with_bytes dy_bytes]
type group_manager_value  = {
  si_public: state_id;
  si_private: state_id;
}

%splice [ps_group_manager_value] (gen_parser (`group_manager_value))
%splice [ps_group_manager_value_is_well_formed] (gen_is_well_formed_lemma (`group_manager_value))

instance group_manager_types: map_types group_manager_key group_manager_value = {
  tag = "MLS.TreeSync.GroupManager";
  ps_key_t = ps_group_manager_key;
  ps_value_t = ps_group_manager_value;
}

val group_manager_pred: {|crypto_invariants|} -> map_predicate group_manager_key group_manager_value #_
let group_manager_pred #ci = {
  pred = (fun tr prin state_id key value ->
    is_publishable tr key.group_id
  );
  pred_later = (fun tr1 tr2 prin state_id key value -> ());
  pred_knowable = (fun tr prin state_id key value -> ());
}

val has_group_manager_invariant: {|protocol_invariants|} -> prop
let has_group_manager_invariant #invs =
  has_map_session_invariant group_manager_pred

val group_manager_tag_and_invariant: {|crypto_invariants|} -> string & local_bytes_state_predicate
let group_manager_tag_and_invariant #ci = (group_manager_types.tag, local_state_predicate_to_local_bytes_state_predicate (map_session_invariant group_manager_pred))

(*** Group manager API ***)

let initialize_group_manager = initialize_map group_manager_key group_manager_value
let add_new_group_sessions = add_key_value #group_manager_key #group_manager_value
let find_group_sessions = find_value #group_manager_key #group_manager_value
