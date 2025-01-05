open Prims
let (get_ith_bit : Prims.nat -> Prims.nat -> Prims.nat -> Prims.int) =
  fun bBits -> fun b -> fun i -> (b / (Prims.pow2 i)) mod (Prims.of_int (2))
let exp_rl_f :
  't .
    't Lib_Exponentiation_Definition.comm_monoid ->
      Prims.nat -> Prims.nat -> Prims.nat -> ('t * 't) -> ('t * 't)
  =
  fun k ->
    fun bBits ->
      fun b ->
        fun i ->
          fun uu___ ->
            match uu___ with
            | (acc, c) ->
                let acc1 =
                  if (get_ith_bit bBits b i) = Prims.int_zero
                  then acc
                  else
                    (match k with
                     | { Lib_Exponentiation_Definition.one = one;
                         Lib_Exponentiation_Definition.mul = mul;
                         Lib_Exponentiation_Definition.lemma_one = lemma_one;
                         Lib_Exponentiation_Definition.lemma_mul_assoc =
                           lemma_mul_assoc;
                         Lib_Exponentiation_Definition.lemma_mul_comm =
                           lemma_mul_comm;_}
                         -> mul acc c) in
                let c1 =
                  match k with
                  | { Lib_Exponentiation_Definition.one = one;
                      Lib_Exponentiation_Definition.mul = mul;
                      Lib_Exponentiation_Definition.lemma_one = lemma_one;
                      Lib_Exponentiation_Definition.lemma_mul_assoc =
                        lemma_mul_assoc;
                      Lib_Exponentiation_Definition.lemma_mul_comm =
                        lemma_mul_comm;_}
                      -> mul c c in
                (acc1, c1)
let exp_rl :
  't .
    't Lib_Exponentiation_Definition.comm_monoid ->
      't -> Prims.nat -> Prims.nat -> 't
  =
  fun k ->
    fun a ->
      fun bBits ->
        fun b ->
          let uu___ =
            Lib_LoopCombinators.repeati bBits (exp_rl_f k bBits b)
              ((match k with
                | { Lib_Exponentiation_Definition.one = one;
                    Lib_Exponentiation_Definition.mul = mul;
                    Lib_Exponentiation_Definition.lemma_one = lemma_one;
                    Lib_Exponentiation_Definition.lemma_mul_assoc =
                      lemma_mul_assoc;
                    Lib_Exponentiation_Definition.lemma_mul_comm =
                      lemma_mul_comm;_}
                    -> one), a) in
          match uu___ with | (acc, c) -> acc
let (b_acc : Prims.pos -> Prims.nat -> Prims.nat -> Prims.nat -> Prims.nat) =
  fun l ->
    fun bBits ->
      fun b -> fun i -> b / (Prims.pow2 ((bBits - (bBits mod l)) - (l * i)))
let exp_lr_f :
  't .
    't Lib_Exponentiation_Definition.comm_monoid ->
      't -> Prims.nat -> Prims.nat -> Prims.nat -> 't -> 't
  =
  fun k ->
    fun a ->
      fun bBits ->
        fun b ->
          fun i ->
            fun acc ->
              let acc1 =
                match k with
                | { Lib_Exponentiation_Definition.one = one;
                    Lib_Exponentiation_Definition.mul = mul;
                    Lib_Exponentiation_Definition.lemma_one = lemma_one;
                    Lib_Exponentiation_Definition.lemma_mul_assoc =
                      lemma_mul_assoc;
                    Lib_Exponentiation_Definition.lemma_mul_comm =
                      lemma_mul_comm;_}
                    -> mul acc acc in
              let acc2 =
                if
                  (get_ith_bit bBits b ((bBits - Prims.int_one) - i)) =
                    Prims.int_zero
                then acc1
                else
                  (match k with
                   | { Lib_Exponentiation_Definition.one = one;
                       Lib_Exponentiation_Definition.mul = mul;
                       Lib_Exponentiation_Definition.lemma_one = lemma_one;
                       Lib_Exponentiation_Definition.lemma_mul_assoc =
                         lemma_mul_assoc;
                       Lib_Exponentiation_Definition.lemma_mul_comm =
                         lemma_mul_comm;_}
                       -> mul acc1 a) in
              acc2
let exp_lr :
  't .
    't Lib_Exponentiation_Definition.comm_monoid ->
      't -> Prims.nat -> Prims.nat -> 't
  =
  fun k ->
    fun a ->
      fun bBits ->
        fun b ->
          Lib_LoopCombinators.repeati bBits (exp_lr_f k a bBits b)
            (match k with
             | { Lib_Exponentiation_Definition.one = one;
                 Lib_Exponentiation_Definition.mul = mul;
                 Lib_Exponentiation_Definition.lemma_one = lemma_one;
                 Lib_Exponentiation_Definition.lemma_mul_assoc =
                   lemma_mul_assoc;
                 Lib_Exponentiation_Definition.lemma_mul_comm =
                   lemma_mul_comm;_}
                 -> one)
let exp_mont_ladder_f :
  't .
    't Lib_Exponentiation_Definition.comm_monoid ->
      Prims.nat -> Prims.nat -> Prims.nat -> ('t * 't) -> ('t * 't)
  =
  fun k ->
    fun bBits ->
      fun b ->
        fun i ->
          fun uu___ ->
            match uu___ with
            | (r0, r1) ->
                if
                  (get_ith_bit bBits b ((bBits - Prims.int_one) - i)) =
                    Prims.int_zero
                then
                  (((match k with
                     | { Lib_Exponentiation_Definition.one = one;
                         Lib_Exponentiation_Definition.mul = mul;
                         Lib_Exponentiation_Definition.lemma_one = lemma_one;
                         Lib_Exponentiation_Definition.lemma_mul_assoc =
                           lemma_mul_assoc;
                         Lib_Exponentiation_Definition.lemma_mul_comm =
                           lemma_mul_comm;_}
                         -> mul r0 r0)),
                    ((match k with
                      | { Lib_Exponentiation_Definition.one = one;
                          Lib_Exponentiation_Definition.mul = mul;
                          Lib_Exponentiation_Definition.lemma_one = lemma_one;
                          Lib_Exponentiation_Definition.lemma_mul_assoc =
                            lemma_mul_assoc;
                          Lib_Exponentiation_Definition.lemma_mul_comm =
                            lemma_mul_comm;_}
                          -> mul r1 r0)))
                else
                  (((match k with
                     | { Lib_Exponentiation_Definition.one = one;
                         Lib_Exponentiation_Definition.mul = mul;
                         Lib_Exponentiation_Definition.lemma_one = lemma_one;
                         Lib_Exponentiation_Definition.lemma_mul_assoc =
                           lemma_mul_assoc;
                         Lib_Exponentiation_Definition.lemma_mul_comm =
                           lemma_mul_comm;_}
                         -> mul r0 r1)),
                    ((match k with
                      | { Lib_Exponentiation_Definition.one = one;
                          Lib_Exponentiation_Definition.mul = mul;
                          Lib_Exponentiation_Definition.lemma_one = lemma_one;
                          Lib_Exponentiation_Definition.lemma_mul_assoc =
                            lemma_mul_assoc;
                          Lib_Exponentiation_Definition.lemma_mul_comm =
                            lemma_mul_comm;_}
                          -> mul r1 r1)))
let exp_mont_ladder :
  't .
    't Lib_Exponentiation_Definition.comm_monoid ->
      't -> Prims.nat -> Prims.nat -> 't
  =
  fun k ->
    fun a ->
      fun bBits ->
        fun b ->
          let uu___ =
            Lib_LoopCombinators.repeati bBits (exp_mont_ladder_f k bBits b)
              ((match k with
                | { Lib_Exponentiation_Definition.one = one;
                    Lib_Exponentiation_Definition.mul = mul;
                    Lib_Exponentiation_Definition.lemma_one = lemma_one;
                    Lib_Exponentiation_Definition.lemma_mul_assoc =
                      lemma_mul_assoc;
                    Lib_Exponentiation_Definition.lemma_mul_comm =
                      lemma_mul_comm;_}
                    -> one), a) in
          match uu___ with | (r0, r1) -> r0
let cswap : 't . Prims.nat -> 't -> 't -> ('t * 't) =
  fun sw ->
    fun r0 -> fun r1 -> if sw = Prims.int_one then (r1, r0) else (r0, r1)
let exp_mont_ladder_swap2_f :
  't .
    't Lib_Exponentiation_Definition.comm_monoid ->
      Prims.nat -> Prims.nat -> Prims.nat -> ('t * 't) -> ('t * 't)
  =
  fun k ->
    fun bBits ->
      fun b ->
        fun i ->
          fun uu___ ->
            match uu___ with
            | (r0, r1) ->
                let bit = get_ith_bit bBits b ((bBits - Prims.int_one) - i) in
                let uu___1 = cswap bit r0 r1 in
                (match uu___1 with
                 | (r01, r11) ->
                     let uu___2 =
                       ((match k with
                         | { Lib_Exponentiation_Definition.one = one;
                             Lib_Exponentiation_Definition.mul = mul;
                             Lib_Exponentiation_Definition.lemma_one =
                               lemma_one;
                             Lib_Exponentiation_Definition.lemma_mul_assoc =
                               lemma_mul_assoc;
                             Lib_Exponentiation_Definition.lemma_mul_comm =
                               lemma_mul_comm;_}
                             -> mul r01 r01),
                         (match k with
                          | { Lib_Exponentiation_Definition.one = one;
                              Lib_Exponentiation_Definition.mul = mul;
                              Lib_Exponentiation_Definition.lemma_one =
                                lemma_one;
                              Lib_Exponentiation_Definition.lemma_mul_assoc =
                                lemma_mul_assoc;
                              Lib_Exponentiation_Definition.lemma_mul_comm =
                                lemma_mul_comm;_}
                              -> mul r11 r01)) in
                     (match uu___2 with
                      | (r02, r12) ->
                          let uu___3 = cswap bit r02 r12 in
                          (match uu___3 with | (r03, r13) -> (r03, r13))))
let exp_mont_ladder_swap2 :
  't .
    't Lib_Exponentiation_Definition.comm_monoid ->
      't -> Prims.nat -> Prims.nat -> 't
  =
  fun k ->
    fun a ->
      fun bBits ->
        fun b ->
          let uu___ =
            Lib_LoopCombinators.repeati bBits
              (exp_mont_ladder_swap2_f k bBits b)
              ((match k with
                | { Lib_Exponentiation_Definition.one = one;
                    Lib_Exponentiation_Definition.mul = mul;
                    Lib_Exponentiation_Definition.lemma_one = lemma_one;
                    Lib_Exponentiation_Definition.lemma_mul_assoc =
                      lemma_mul_assoc;
                    Lib_Exponentiation_Definition.lemma_mul_comm =
                      lemma_mul_comm;_}
                    -> one), a) in
          match uu___ with | (r0, r1) -> r0
let exp_mont_ladder_swap_f :
  't .
    't Lib_Exponentiation_Definition.comm_monoid ->
      Prims.nat ->
        Prims.nat ->
          Prims.nat -> ('t * 't * Prims.nat) -> ('t * 't * Prims.nat)
  =
  fun k ->
    fun bBits ->
      fun b ->
        fun i ->
          fun uu___ ->
            match uu___ with
            | (r0, r1, privbit) ->
                let bit = get_ith_bit bBits b ((bBits - Prims.int_one) - i) in
                let sw = (bit + privbit) mod (Prims.of_int (2)) in
                let uu___1 = cswap sw r0 r1 in
                (match uu___1 with
                 | (r01, r11) ->
                     let uu___2 =
                       ((match k with
                         | { Lib_Exponentiation_Definition.one = one;
                             Lib_Exponentiation_Definition.mul = mul;
                             Lib_Exponentiation_Definition.lemma_one =
                               lemma_one;
                             Lib_Exponentiation_Definition.lemma_mul_assoc =
                               lemma_mul_assoc;
                             Lib_Exponentiation_Definition.lemma_mul_comm =
                               lemma_mul_comm;_}
                             -> mul r01 r01),
                         (match k with
                          | { Lib_Exponentiation_Definition.one = one;
                              Lib_Exponentiation_Definition.mul = mul;
                              Lib_Exponentiation_Definition.lemma_one =
                                lemma_one;
                              Lib_Exponentiation_Definition.lemma_mul_assoc =
                                lemma_mul_assoc;
                              Lib_Exponentiation_Definition.lemma_mul_comm =
                                lemma_mul_comm;_}
                              -> mul r11 r01)) in
                     (match uu___2 with | (r02, r12) -> (r02, r12, bit)))
let exp_mont_ladder_swap :
  't .
    't Lib_Exponentiation_Definition.comm_monoid ->
      't -> Prims.nat -> Prims.nat -> 't
  =
  fun k ->
    fun a ->
      fun bBits ->
        fun b ->
          let uu___ =
            Lib_LoopCombinators.repeati bBits
              (exp_mont_ladder_swap_f k bBits b)
              ((match k with
                | { Lib_Exponentiation_Definition.one = one;
                    Lib_Exponentiation_Definition.mul = mul;
                    Lib_Exponentiation_Definition.lemma_one = lemma_one;
                    Lib_Exponentiation_Definition.lemma_mul_assoc =
                      lemma_mul_assoc;
                    Lib_Exponentiation_Definition.lemma_mul_comm =
                      lemma_mul_comm;_}
                    -> one), a, Prims.int_zero) in
          match uu___ with
          | (r0, r1, sw) ->
              let uu___1 = cswap sw r0 r1 in
              (match uu___1 with | (r01, r11) -> r01)
let exp_pow2 :
  't . 't Lib_Exponentiation_Definition.comm_monoid -> 't -> Prims.nat -> 't
  =
  fun k ->
    fun a ->
      fun b ->
        Lib_LoopCombinators.repeat b (Lib_Exponentiation_Definition.sqr k) a
let (get_ith_lbits :
  Prims.nat -> Prims.nat -> Prims.nat -> Prims.pos -> Prims.int) =
  fun bBits ->
    fun b -> fun i -> fun l -> (b / (Prims.pow2 i)) mod (Prims.pow2 l)
let (get_bits_l :
  Prims.nat -> Prims.nat -> Prims.pos -> Prims.nat -> Prims.nat) =
  fun bBits ->
    fun b ->
      fun l ->
        fun i ->
          get_ith_lbits bBits b (((bBits - (bBits mod l)) - (l * i)) - l) l
let mul_acc_pow_a_bits_l :
  't .
    't Lib_Exponentiation_Definition.comm_monoid ->
      't -> Prims.nat -> Prims.nat -> Prims.pos -> Prims.nat -> 't -> 't
  =
  fun k ->
    fun a ->
      fun bBits ->
        fun b ->
          fun l ->
            fun i ->
              fun acc ->
                let bits_l = get_bits_l bBits b l i in
                (match k with
                 | { Lib_Exponentiation_Definition.one = one;
                     Lib_Exponentiation_Definition.mul = mul;
                     Lib_Exponentiation_Definition.lemma_one = lemma_one;
                     Lib_Exponentiation_Definition.lemma_mul_assoc =
                       lemma_mul_assoc;
                     Lib_Exponentiation_Definition.lemma_mul_comm =
                       lemma_mul_comm;_}
                     -> mul) acc
                  (Lib_Exponentiation_Definition.pow k a bits_l)
let exp_fw_f :
  't .
    't Lib_Exponentiation_Definition.comm_monoid ->
      't -> Prims.nat -> Prims.nat -> Prims.pos -> Prims.nat -> 't -> 't
  =
  fun k ->
    fun a ->
      fun bBits ->
        fun b ->
          fun l ->
            fun i ->
              fun acc ->
                let acc1 = exp_pow2 k acc l in
                mul_acc_pow_a_bits_l k a bBits b l i acc1
let exp_fw_acc0 :
  't .
    't Lib_Exponentiation_Definition.comm_monoid ->
      't -> Prims.nat -> Prims.nat -> Prims.pos -> 't
  =
  fun k ->
    fun a ->
      fun bBits ->
        fun b ->
          fun l ->
            let bits_c = get_ith_lbits bBits b ((bBits / l) * l) l in
            Lib_Exponentiation_Definition.pow k a bits_c
let exp_fw :
  't .
    't Lib_Exponentiation_Definition.comm_monoid ->
      't -> Prims.nat -> Prims.nat -> Prims.pos -> 't
  =
  fun k ->
    fun a ->
      fun bBits ->
        fun b ->
          fun l ->
            let acc0 =
              if (bBits mod l) = Prims.int_zero
              then
                match k with
                | { Lib_Exponentiation_Definition.one = one;
                    Lib_Exponentiation_Definition.mul = mul;
                    Lib_Exponentiation_Definition.lemma_one = lemma_one;
                    Lib_Exponentiation_Definition.lemma_mul_assoc =
                      lemma_mul_assoc;
                    Lib_Exponentiation_Definition.lemma_mul_comm =
                      lemma_mul_comm;_}
                    -> one
              else exp_fw_acc0 k a bBits b l in
            let res =
              Lib_LoopCombinators.repeati (bBits / l)
                (exp_fw_f k a bBits b l) acc0 in
            res
let exp_double_fw_f :
  't .
    't Lib_Exponentiation_Definition.comm_monoid ->
      't ->
        Prims.nat ->
          Prims.nat -> 't -> Prims.nat -> Prims.pos -> Prims.nat -> 't -> 't
  =
  fun k ->
    fun a1 ->
      fun bBits ->
        fun b1 ->
          fun a2 ->
            fun b2 ->
              fun l ->
                fun i ->
                  fun acc ->
                    let acc1 = exp_fw_f k a2 bBits b2 l i acc in
                    mul_acc_pow_a_bits_l k a1 bBits b1 l i acc1
let exp_double_fw_acc0 :
  't .
    't Lib_Exponentiation_Definition.comm_monoid ->
      't -> Prims.nat -> Prims.nat -> 't -> Prims.nat -> Prims.pos -> 't
  =
  fun k ->
    fun a1 ->
      fun bBits ->
        fun b1 ->
          fun a2 ->
            fun b2 ->
              fun l ->
                let acc_a1 = exp_fw_acc0 k a1 bBits b1 l in
                let acc_a2 = exp_fw_acc0 k a2 bBits b2 l in
                match k with
                | { Lib_Exponentiation_Definition.one = one;
                    Lib_Exponentiation_Definition.mul = mul;
                    Lib_Exponentiation_Definition.lemma_one = lemma_one;
                    Lib_Exponentiation_Definition.lemma_mul_assoc =
                      lemma_mul_assoc;
                    Lib_Exponentiation_Definition.lemma_mul_comm =
                      lemma_mul_comm;_}
                    -> mul acc_a1 acc_a2
let exp_double_fw :
  't .
    't Lib_Exponentiation_Definition.comm_monoid ->
      't -> Prims.nat -> Prims.nat -> 't -> Prims.nat -> Prims.pos -> 't
  =
  fun k ->
    fun a1 ->
      fun bBits ->
        fun b1 ->
          fun a2 ->
            fun b2 ->
              fun l ->
                let acc0 =
                  if (bBits mod l) = Prims.int_zero
                  then
                    match k with
                    | { Lib_Exponentiation_Definition.one = one;
                        Lib_Exponentiation_Definition.mul = mul;
                        Lib_Exponentiation_Definition.lemma_one = lemma_one;
                        Lib_Exponentiation_Definition.lemma_mul_assoc =
                          lemma_mul_assoc;
                        Lib_Exponentiation_Definition.lemma_mul_comm =
                          lemma_mul_comm;_}
                        -> one
                  else exp_double_fw_acc0 k a1 bBits b1 a2 b2 l in
                Lib_LoopCombinators.repeati (bBits / l)
                  (exp_double_fw_f k a1 bBits b1 a2 b2 l) acc0
let exp_four_fw_f :
  't .
    't Lib_Exponentiation_Definition.comm_monoid ->
      't ->
        Prims.nat ->
          Prims.nat ->
            't ->
              Prims.nat ->
                't ->
                  Prims.nat ->
                    't -> Prims.nat -> Prims.pos -> Prims.nat -> 't -> 't
  =
  fun k ->
    fun a1 ->
      fun bBits ->
        fun b1 ->
          fun a2 ->
            fun b2 ->
              fun a3 ->
                fun b3 ->
                  fun a4 ->
                    fun b4 ->
                      fun l ->
                        fun i ->
                          fun acc ->
                            let acc1 = exp_fw_f k a4 bBits b4 l i acc in
                            let acc2 =
                              mul_acc_pow_a_bits_l k a3 bBits b3 l i acc1 in
                            let acc3 =
                              mul_acc_pow_a_bits_l k a2 bBits b2 l i acc2 in
                            let acc4 =
                              mul_acc_pow_a_bits_l k a1 bBits b1 l i acc3 in
                            acc4
let exp_four_fw_acc0 :
  't .
    't Lib_Exponentiation_Definition.comm_monoid ->
      't ->
        Prims.nat ->
          Prims.nat ->
            't ->
              Prims.nat ->
                't -> Prims.nat -> 't -> Prims.nat -> Prims.pos -> 't
  =
  fun k ->
    fun a1 ->
      fun bBits ->
        fun b1 ->
          fun a2 ->
            fun b2 ->
              fun a3 ->
                fun b3 ->
                  fun a4 ->
                    fun b4 ->
                      fun l ->
                        let acc_a12 =
                          exp_double_fw_acc0 k a1 bBits b1 a2 b2 l in
                        let acc_a34 =
                          exp_double_fw_acc0 k a3 bBits b3 a4 b4 l in
                        match k with
                        | { Lib_Exponentiation_Definition.one = one;
                            Lib_Exponentiation_Definition.mul = mul;
                            Lib_Exponentiation_Definition.lemma_one =
                              lemma_one;
                            Lib_Exponentiation_Definition.lemma_mul_assoc =
                              lemma_mul_assoc;
                            Lib_Exponentiation_Definition.lemma_mul_comm =
                              lemma_mul_comm;_}
                            -> mul acc_a12 acc_a34
let exp_four_fw :
  't .
    't Lib_Exponentiation_Definition.comm_monoid ->
      't ->
        Prims.nat ->
          Prims.nat ->
            't ->
              Prims.nat ->
                't -> Prims.nat -> 't -> Prims.nat -> Prims.pos -> 't
  =
  fun k ->
    fun a1 ->
      fun bBits ->
        fun b1 ->
          fun a2 ->
            fun b2 ->
              fun a3 ->
                fun b3 ->
                  fun a4 ->
                    fun b4 ->
                      fun l ->
                        let acc0 =
                          if (bBits mod l) = Prims.int_zero
                          then
                            match k with
                            | { Lib_Exponentiation_Definition.one = one;
                                Lib_Exponentiation_Definition.mul = mul;
                                Lib_Exponentiation_Definition.lemma_one =
                                  lemma_one;
                                Lib_Exponentiation_Definition.lemma_mul_assoc
                                  = lemma_mul_assoc;
                                Lib_Exponentiation_Definition.lemma_mul_comm
                                  = lemma_mul_comm;_}
                                -> one
                          else
                            exp_four_fw_acc0 k a1 bBits b1 a2 b2 a3 b3 a4 b4
                              l in
                        Lib_LoopCombinators.repeati (bBits / l)
                          (exp_four_fw_f k a1 bBits b1 a2 b2 a3 b3 a4 b4 l)
                          acc0