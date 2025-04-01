module MLS.Symbolic.Lemmas

open DY.Core

#push-options "--fuel 1 --ifuel 1"
val trace_invariant_before:
  {|protocol_invariants|} ->
  tr1:trace -> tr2:trace ->
  Lemma
  (requires trace_invariant tr2 /\ tr1 <$ tr2)
  (ensures trace_invariant tr1)
  (decreases tr2)
let rec trace_invariant_before #invs tr1 tr2 =
  norm_spec [zeta; delta_only [`%trace_invariant]] (trace_invariant);
  norm_spec [zeta; delta_only [`%prefix]] (prefix #label);
  reveal_opaque (`%grows) (grows #label);
  if trace_length tr1 = trace_length tr2 then ()
  else (
    let Snoc init2 last2 = tr2 in
    trace_invariant_before tr1 init2
  )
#pop-options

val is_minimum_corrupt_trace_for_label:
  l:label -> tr:trace ->
  prop
let is_minimum_corrupt_trace_for_label l tr =
  is_corrupt tr l /\
  forall tr_smaller. (
    tr_smaller <$ tr /\
    is_corrupt tr_smaller l ==>
    tr_smaller == tr
  )

#push-options "--fuel 1 --ifuel 1"
val exists_minimum_trace:
  tr:trace -> l:label ->
  Lemma
  (requires is_corrupt tr l)
  (ensures exists tr_min.
    tr_min <$ tr /\
    is_minimum_corrupt_trace_for_label l tr_min
  )
let rec exists_minimum_trace tr l =
  norm_spec [zeta; delta_only [`%prefix]] (prefix #label);
  reveal_opaque (`%grows) (grows #label);
  match tr with
  | Nil -> ()
  | Snoc init last -> (
    eliminate is_corrupt init l \/ ~(is_corrupt init l)
    returns exists tr_min. tr_min <$ tr /\ is_minimum_corrupt_trace_for_label l tr_min
    with _. (
      exists_minimum_trace init l
    ) and _. (
      assert(tr <$ tr /\ is_minimum_corrupt_trace_for_label l tr)
    )
  )
#pop-options
