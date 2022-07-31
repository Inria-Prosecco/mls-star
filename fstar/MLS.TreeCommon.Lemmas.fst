module MLS.TreeCommon.Lemmas

open MLS.TreeCommon

#set-options "--fuel 0 --ifuel 0"

#push-options "--ifuel 2 --fuel 2"
val mem_insert_sorted: #a:eqtype{a `subtype_of` int} -> x:a -> l:list a -> elem:a -> Lemma
  (List.Tot.mem elem (insert_sorted x l) <==> elem == x \/ List.Tot.mem elem l)
let rec mem_insert_sorted x l elem =
  match l with
  | [] -> ()
  | [y] -> ()
  | y::z::t ->
    if x < y then ()
    else if x = y then ()
    else mem_insert_sorted x (z::t) elem
#pop-options
