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

// When upgrading F* from commit 7ae4850a7e24f011a572ab4097fe1045babab48c to commit eb911fc41d5ba730c15f2ac296ffc5ebf7b46560,
// We get a failure in the `gen_parser` tactic:
// Goal: (bytes: Type0), (_: Comparse.Bytes.Typeclass.bytes_like bytes), (x: Prims.nat) |- _ : Prims.squash (forall (y: Prims.nat). (| x, y |) == (| x, y |))
// Comparse.Tactic.GenerateParser.fst(293,8-293,85): (Error 228) user tactic failed: `apply_lemma: Cannot instantiate lemma FStar.Tactics.Logic.fa_intro_lem (with postcondition: Prims.squash (forall (x: Prims.nat). (| (*?u383*) _, (*?u379*) _ |) == (*?u371*) _)) to match goal (Prims.squash (forall (y: Prims.nat). (| x, y |) == (| x, y |)))` (see also FStar.Tactics.Logic.fst(50,4-50,31))
// It does not happen in interactive mode, only when compiling using `make`.
// Very difficult to minimize, modifying functions *after* the tactic call would make the error dissappear.
// I noticed that adding a dummy function before is fixing the problem.
// Another option would have been to spend hours minimizing, filing an issue in F* and hope it would be fixed, but I don't have that time right now.
// This is why there is this horrible hack.
private let __do_not_remove_me__ (bytes:Type0) = ()

%splice [ps_group_manager_value] (gen_parser (`group_manager_value))
%splice [ps_group_manager_value_is_well_formed] (gen_is_well_formed_lemma (`group_manager_value))

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
