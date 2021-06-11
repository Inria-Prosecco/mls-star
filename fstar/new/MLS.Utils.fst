module MLS.Utils

type nat_less (m:nat) = n:nat{n<m}

val find_index: #a:eqtype -> a -> l:list a -> option (nat_less (List.Tot.length l))
let rec find_index #a x l =
  match l with
  | [] -> None
  | h::t ->
    if x=h then (
      Some 0
    ) else (
      match find_index x t with
      | Some res -> Some (res+1)
      | None -> None
    )

val insert_sorted: nat -> list nat -> list nat
let rec insert_sorted x l =
  match l with
  | [] -> [x]
  | h::t ->
    if x < h then
      x::l
    else if x = h then
      l
    else
      h::(insert_sorted x t)

