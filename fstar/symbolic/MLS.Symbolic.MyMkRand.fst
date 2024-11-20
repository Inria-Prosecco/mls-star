module MLS.Symbolic.MyMkRand

open DY.Core

#set-options "--fuel 0 --ifuel 0"

[@@ "opaque_to_smt"]
val my_mk_rand: usg:usage -> lab:(bytes -> label) -> len:nat{len <> 0} -> traceful bytes
let my_mk_rand usg lab len =
  let* time = get_time in
  let result = (Rand len time) in
  add_entry (RandGen usg (lab result) len);*
  return result

/// Generating a random bytestrings always preserve the trace invariant.

#push-options "--z3rlimit 25 --fuel 1 --ifuel 1"
val my_mk_rand_trace_invariant:
  {|protocol_invariants|} ->
  usg:usage -> lab:(bytes -> label) -> len:nat{len <> 0} -> tr:trace ->
  Lemma
  (requires trace_invariant tr)
  (ensures (
    let (b, tr_out) = my_mk_rand usg lab len tr in
    trace_invariant tr_out /\
    1 <= DY.Core.Trace.Base.length tr_out /\
    rand_generated_at tr_out (DY.Core.Trace.Base.length tr_out - 1) b
  ))
  [SMTPat (my_mk_rand usg lab len tr); SMTPat (trace_invariant tr)]
let my_mk_rand_trace_invariant #invs usg lab len tr =
  let result = (Rand len (DY.Core.Trace.Base.length tr)) in
  add_entry_invariant (RandGen usg (lab result) len) tr;
  reveal_opaque (`%my_mk_rand) (my_mk_rand)
#pop-options

/// Random bytestrings satisfy the bytes invariant.

#push-options "--fuel 1 --ifuel 1"
val my_mk_rand_bytes_invariant:
  {|protocol_invariants|} ->
  usg:usage -> lab:(bytes -> label) -> len:nat{len <> 0} -> tr:trace ->
  Lemma
  (ensures (
    let (b, tr_out) = my_mk_rand usg lab len tr in
    bytes_invariant tr_out b
  ))
  // We need a way for the SMT pattern to know the value of `invs`
  // This is done using `trace_invariant`, although it is not necessary for the theorem to hold,
  // it is certainly around in the context
  [SMTPat (my_mk_rand usg lab len tr); SMTPat (trace_invariant tr)]
let my_mk_rand_bytes_invariant #invs usg lab len tr =
  reveal_opaque (`%my_mk_rand) (my_mk_rand);
  normalize_term_spec bytes_invariant
#pop-options

/// Label of random bytestrings.

#push-options "--fuel 1 --ifuel 1"
val my_mk_rand_get_label:
  {|protocol_invariants|} ->
  usg:usage -> lab:(bytes -> label) -> len:nat{len <> 0} -> tr:trace ->
  Lemma
  (ensures (
    let (b, tr_out) = my_mk_rand usg lab len tr in
    get_label tr_out b == lab b
  ))
  [SMTPat (my_mk_rand usg lab len tr); SMTPat (trace_invariant tr)]
let my_mk_rand_get_label #invs usg lab len tr =
  reveal_opaque (`%my_mk_rand) (my_mk_rand);
  normalize_term_spec get_label
#pop-options

/// Usage of random bytestrings.

#push-options "--fuel 1 --ifuel 1"
val my_mk_rand_has_usage:
  {|protocol_invariants|} ->
  usg:usage -> lab:(bytes -> label) -> len:nat{len <> 0} -> tr:trace ->
  Lemma
  (ensures (
    let (b, tr_out) = my_mk_rand usg lab len tr in
    b `has_usage tr_out` usg
  ))
  [SMTPat (my_mk_rand usg lab len tr); SMTPat (trace_invariant tr)]
let my_mk_rand_has_usage #invs usg lab len tr =
  normalize_term_spec my_mk_rand;
  normalize_term_spec has_usage
#pop-options
