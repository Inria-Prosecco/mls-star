module MLS.Symbolic.Labels.Prop

open DY.Core

#set-options "--fuel 0 --ifuel 0"

val prop_to_label: prop -> label
let prop_to_label p = mk_label {
  is_corrupt = (fun tr -> p);
  is_corrupt_later = (fun tr1 tr2 -> ());
}

val is_corrupt_prop_to_label:
  tr:trace -> p:prop ->
  Lemma
  (is_corrupt tr (prop_to_label p) <==> p)
  [SMTPat (is_corrupt tr (prop_to_label p))]
let is_corrupt_prop_to_label tr p =
  reveal_opaque (`%is_corrupt) (is_corrupt)

val prop_to_label_equal:
  p1:prop -> p2:prop ->
  Lemma
  (requires p1 <==> p2)
  (ensures prop_to_label p1 == prop_to_label p2)
let prop_to_label_equal p1 p2 =
  intro_label_equal (prop_to_label p1) (prop_to_label p2) (fun tr ->
    reveal_opaque (`%can_flow) (can_flow)
  )

val prop_to_label_true:
  p:prop ->
  Lemma
  (requires p)
  (ensures prop_to_label p == public)
let prop_to_label_true p =
  intro_label_equal (prop_to_label p) (public) (fun tr ->
    reveal_opaque (`%can_flow) (can_flow)
  )

val prop_to_label_false:
  p:prop ->
  Lemma
  (requires ~p)
  (ensures prop_to_label p == secret)
let prop_to_label_false p =
  intro_label_equal (prop_to_label p) (secret) (fun tr ->
    reveal_opaque (`%can_flow) (can_flow)
  )

