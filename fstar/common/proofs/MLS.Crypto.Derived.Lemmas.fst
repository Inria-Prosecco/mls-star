module MLS.Crypto.Derived.Lemmas

open MLS.Crypto.Derived

#push-options "--fuel 0 --ifuel 0"

val get_mls_label_inj:
  l1:valid_label -> l2:valid_label ->
  Lemma
  (requires get_mls_label l1 == get_mls_label l2)
  (ensures l1 == l2)
let get_mls_label_inj l1 l2 =
  String.concat_injective "MLS 1.0 " "MLS 1.0 " l1 l2
