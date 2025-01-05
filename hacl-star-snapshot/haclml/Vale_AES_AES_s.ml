open Prims
let (mix_columns_LE : Vale_Def_Types_s.quad32 -> Vale_Def_Types_s.quad32) =
  fun q -> failwith "Not yet implemented: Vale.AES.AES_s.mix_columns_LE"
let (inv_mix_columns_LE : Vale_Def_Types_s.quad32 -> Vale_Def_Types_s.quad32)
  =
  fun q -> failwith "Not yet implemented: Vale.AES.AES_s.inv_mix_columns_LE"
let (shift_rows_LE : Vale_Def_Types_s.quad32 -> Vale_Def_Types_s.quad32) =
  fun q -> failwith "Not yet implemented: Vale.AES.AES_s.shift_rows_LE"
let (inv_shift_rows_LE : Vale_Def_Types_s.quad32 -> Vale_Def_Types_s.quad32)
  = fun q -> failwith "Not yet implemented: Vale.AES.AES_s.inv_shift_rows_LE"
let (rot_word_LE : Vale_Def_Words_s.nat32 -> Vale_Def_Words_s.nat32) =
  fun w -> failwith "Not yet implemented: Vale.AES.AES_s.rot_word_LE"
type ('alg, 's) is_aes_key_LE = unit
type 'alg aes_key_LE = Vale_Def_Words_s.nat32 FStar_Seq_Base.seq
let (eval_round :
  Vale_Def_Types_s.quad32 ->
    Vale_Def_Types_s.quad32 -> Vale_Def_Types_s.quad32)
  =
  fun state ->
    fun round_key ->
      let s = Vale_AES_AES_common_s.sub_bytes state in
      let s1 = shift_rows_LE s in
      let s2 = mix_columns_LE s1 in
      let s3 = Vale_Def_Types_s.quad32_xor s2 round_key in s3
let rec (eval_rounds_def :
  Vale_Def_Types_s.quad32 ->
    Vale_Def_Types_s.quad32 FStar_Seq_Base.seq ->
      Prims.nat -> Vale_Def_Types_s.quad32)
  =
  fun init ->
    fun round_keys ->
      fun n ->
        if n = Prims.int_zero
        then init
        else
          eval_round (eval_rounds_def init round_keys (n - Prims.int_one))
            (FStar_Seq_Base.index round_keys n)
let (eval_rounds :
  Vale_Def_Types_s.quad32 ->
    Vale_Def_Types_s.quad32 FStar_Seq_Base.seq ->
      Prims.nat -> Vale_Def_Types_s.quad32)
  = Vale_Def_Opaque_s.opaque_make eval_rounds_def
let (eval_cipher_def :
  Vale_AES_AES_common_s.algorithm ->
    Vale_Def_Types_s.quad32 ->
      Vale_Def_Types_s.quad32 FStar_Seq_Base.seq -> Vale_Def_Types_s.quad32)
  =
  fun alg ->
    fun input ->
      fun round_keys ->
        let state =
          Vale_Def_Types_s.quad32_xor input
            (FStar_Seq_Base.index round_keys Prims.int_zero) in
        let state1 =
          eval_rounds_def state round_keys
            ((match alg with
              | Vale_AES_AES_common_s.AES_128 -> (Prims.of_int (10))
              | Vale_AES_AES_common_s.AES_192 -> (Prims.of_int (12))
              | Vale_AES_AES_common_s.AES_256 -> (Prims.of_int (14))) -
               Prims.int_one) in
        let state2 = Vale_AES_AES_common_s.sub_bytes state1 in
        let state3 = shift_rows_LE state2 in
        let state4 =
          Vale_Def_Types_s.quad32_xor state3
            (FStar_Seq_Base.index round_keys
               (match alg with
                | Vale_AES_AES_common_s.AES_128 -> (Prims.of_int (10))
                | Vale_AES_AES_common_s.AES_192 -> (Prims.of_int (12))
                | Vale_AES_AES_common_s.AES_256 -> (Prims.of_int (14)))) in
        state4
let (eval_cipher :
  Vale_AES_AES_common_s.algorithm ->
    Vale_Def_Types_s.quad32 ->
      Vale_Def_Types_s.quad32 FStar_Seq_Base.seq -> Vale_Def_Types_s.quad32)
  = Vale_Def_Opaque_s.opaque_make eval_cipher_def
let rec (expand_key_def :
  Vale_AES_AES_common_s.algorithm ->
    unit aes_key_LE -> Prims.nat -> Vale_Def_Words_s.nat32 FStar_Seq_Base.seq)
  =
  fun alg ->
    fun key ->
      fun size ->
        if size = Prims.int_zero
        then FStar_Seq_Base.empty ()
        else
          (let w = expand_key_def alg key (size - Prims.int_one) in
           let i = size - Prims.int_one in
           if
             (Prims.int_zero <= i) &&
               (i <
                  (match alg with
                   | Vale_AES_AES_common_s.AES_128 -> (Prims.of_int (4))
                   | Vale_AES_AES_common_s.AES_192 -> (Prims.of_int (6))
                   | Vale_AES_AES_common_s.AES_256 -> (Prims.of_int (8))))
           then
             FStar_Seq_Base.append w
               (FStar_Seq_Base.create Prims.int_one
                  (FStar_Seq_Base.index key i))
           else
             (let temp =
                if
                  (i mod
                     (match alg with
                      | Vale_AES_AES_common_s.AES_128 -> (Prims.of_int (4))
                      | Vale_AES_AES_common_s.AES_192 -> (Prims.of_int (6))
                      | Vale_AES_AES_common_s.AES_256 -> (Prims.of_int (8))))
                    = Prims.int_zero
                then
                  Vale_Def_Types_s.ixor (Prims.parse_int "0x100000000")
                    (Vale_AES_AES_common_s.sub_word
                       (rot_word_LE
                          (FStar_Seq_Base.index w (i - Prims.int_one))))
                    (Vale_AES_AES_common_s.aes_rcon
                       ((i /
                           (match alg with
                            | Vale_AES_AES_common_s.AES_128 ->
                                (Prims.of_int (4))
                            | Vale_AES_AES_common_s.AES_192 ->
                                (Prims.of_int (6))
                            | Vale_AES_AES_common_s.AES_256 ->
                                (Prims.of_int (8))))
                          - Prims.int_one))
                else
                  if
                    ((match alg with
                      | Vale_AES_AES_common_s.AES_128 -> (Prims.of_int (4))
                      | Vale_AES_AES_common_s.AES_192 -> (Prims.of_int (6))
                      | Vale_AES_AES_common_s.AES_256 -> (Prims.of_int (8)))
                       > (Prims.of_int (6)))
                      &&
                      ((i mod
                          (match alg with
                           | Vale_AES_AES_common_s.AES_128 ->
                               (Prims.of_int (4))
                           | Vale_AES_AES_common_s.AES_192 ->
                               (Prims.of_int (6))
                           | Vale_AES_AES_common_s.AES_256 ->
                               (Prims.of_int (8))))
                         = (Prims.of_int (4)))
                  then
                    Vale_AES_AES_common_s.sub_word
                      (FStar_Seq_Base.index w (i - Prims.int_one))
                  else FStar_Seq_Base.index w (i - Prims.int_one) in
              FStar_Seq_Base.append w
                (FStar_Seq_Base.create Prims.int_one
                   (Vale_Def_Types_s.ixor (Prims.parse_int "0x100000000")
                      (FStar_Seq_Base.index w
                         (i -
                            (match alg with
                             | Vale_AES_AES_common_s.AES_128 ->
                                 (Prims.of_int (4))
                             | Vale_AES_AES_common_s.AES_192 ->
                                 (Prims.of_int (6))
                             | Vale_AES_AES_common_s.AES_256 ->
                                 (Prims.of_int (8))))) temp))))
let (expand_key :
  Vale_AES_AES_common_s.algorithm ->
    unit aes_key_LE -> Prims.nat -> Vale_Def_Words_s.nat32 FStar_Seq_Base.seq)
  = Vale_Def_Opaque_s.opaque_make expand_key_def
let rec (key_schedule_to_round_keys :
  Prims.nat ->
    Vale_Def_Words_s.nat32 FStar_Seq_Base.seq ->
      Vale_Def_Types_s.quad32 FStar_Seq_Base.seq)
  =
  fun rounds ->
    fun w ->
      if rounds = Prims.int_zero
      then FStar_Seq_Base.empty ()
      else
        (let round_keys =
           key_schedule_to_round_keys (rounds - Prims.int_one) w in
         let rk =
           {
             Vale_Def_Words_s.lo0 =
               (FStar_Seq_Base.index w
                  (((Prims.of_int (4)) * rounds) - (Prims.of_int (4))));
             Vale_Def_Words_s.lo1 =
               (FStar_Seq_Base.index w
                  (((Prims.of_int (4)) * rounds) - (Prims.of_int (3))));
             Vale_Def_Words_s.hi2 =
               (FStar_Seq_Base.index w
                  (((Prims.of_int (4)) * rounds) - (Prims.of_int (2))));
             Vale_Def_Words_s.hi3 =
               (FStar_Seq_Base.index w
                  (((Prims.of_int (4)) * rounds) - Prims.int_one))
           } in
         FStar_Seq_Base.append round_keys
           (FStar_Seq_Base.create Prims.int_one rk))
let (key_to_round_keys_LE :
  Vale_AES_AES_common_s.algorithm ->
    Vale_Def_Words_s.nat32 FStar_Seq_Base.seq ->
      Vale_Def_Types_s.quad32 FStar_Seq_Base.seq)
  =
  fun alg ->
    fun key ->
      key_schedule_to_round_keys
        ((match alg with
          | Vale_AES_AES_common_s.AES_128 -> (Prims.of_int (10))
          | Vale_AES_AES_common_s.AES_192 -> (Prims.of_int (12))
          | Vale_AES_AES_common_s.AES_256 -> (Prims.of_int (14))) +
           Prims.int_one)
        (expand_key alg key
           (Vale_AES_AES_common_s.nb *
              ((match alg with
                | Vale_AES_AES_common_s.AES_128 -> (Prims.of_int (10))
                | Vale_AES_AES_common_s.AES_192 -> (Prims.of_int (12))
                | Vale_AES_AES_common_s.AES_256 -> (Prims.of_int (14))) +
                 Prims.int_one)))
let (aes_encrypt_LE_def :
  Vale_AES_AES_common_s.algorithm ->
    Vale_Def_Words_s.nat32 FStar_Seq_Base.seq ->
      Vale_Def_Types_s.quad32 -> Vale_Def_Types_s.quad32)
  =
  fun alg ->
    fun key ->
      fun input_LE ->
        eval_cipher_def alg input_LE (key_to_round_keys_LE alg key)
let (aes_encrypt_LE :
  Vale_AES_AES_common_s.algorithm ->
    Vale_Def_Words_s.nat32 FStar_Seq_Base.seq ->
      Vale_Def_Types_s.quad32 -> Vale_Def_Types_s.quad32)
  = Vale_Def_Opaque_s.opaque_make aes_encrypt_LE_def
let (key_to_round_keys :
  Vale_AES_AES_common_s.algorithm ->
    unit Vale_AES_AES_common_s.aes_key ->
      Vale_Def_Words_s.nat8 FStar_Seq_Base.seq)
  =
  fun alg ->
    fun key ->
      let key_LE = Vale_Def_Words_Seq_s.seq_nat8_to_seq_nat32_LE key in
      Vale_Def_Types_s.le_seq_quad32_to_bytes
        (key_to_round_keys_LE alg key_LE)
let (aes_encrypt :
  Vale_AES_AES_common_s.algorithm ->
    unit Vale_AES_AES_common_s.aes_key ->
      Vale_Def_Words_s.nat8 Vale_Def_Words_Seq_s.seq16 ->
        Vale_Def_Words_s.nat8 Vale_Def_Words_Seq_s.seq16)
  =
  fun alg ->
    fun key ->
      fun input ->
        let key_LE = Vale_Def_Words_Seq_s.seq_nat8_to_seq_nat32_LE key in
        let input_LE = Vale_Def_Types_s.le_bytes_to_quad32 input in
        Vale_Def_Types_s.le_quad32_to_bytes
          (aes_encrypt_LE alg key_LE input_LE)