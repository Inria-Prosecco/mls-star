module MLS.Test.Bench.Time

open FStar.All

val time: Type0

val tic: unit -> ML time
val tac: time -> ML string
