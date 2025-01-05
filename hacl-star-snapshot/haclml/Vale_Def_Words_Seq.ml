open Prims
let (pow2_24 : Prims.int) = (Prims.parse_int "16777216")
let rec (base_to_nat :
  Prims.pos -> unit Vale_Def_Words_s.natN Prims.list -> Prims.nat) =
  fun base ->
    fun cs ->
      match cs with
      | [] -> Prims.int_zero
      | c::cs' -> c + ((base_to_nat base cs') * base)