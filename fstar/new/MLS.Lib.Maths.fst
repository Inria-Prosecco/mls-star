module MLS.Lib.Maths

val log2: sz:pos -> option nat
let rec log2 sz =
  if sz = 1 then Some 0
  else if sz % 2 = 1 then None
       else match log2 (sz/2) with
	    | None -> None
	    | Some l -> Some (1+l)

let rec log2_lemma (sz:pos):
  Lemma (match log2 sz with
	 | None -> True
	 | Some l -> sz == pow2 l)
	 [SMTPat (log2 sz)] =
   if sz = 1 then ()
   else log2_lemma (sz/2)
