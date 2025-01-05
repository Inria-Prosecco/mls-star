open Prims
type ('alg, 'key, 'roundukeys, 'keysub, 'keyuptr, 'heap0, 'layout) aes_reqs =
  unit
let (va_code_Aes_round_4way :
  Vale_X64_Machine_s.reg_xmm ->
    (Vale_X64_Decls.ins, Vale_X64_Decls.ocmp) Vale_X64_Machine_s.precode)
  =
  fun round_key ->
    Vale_X64_Machine_s.Block
      [Vale_X64_InsAes.va_code_AESNI_enc (Prims.of_int (2)) round_key;
      Vale_X64_InsAes.va_code_AESNI_enc (Prims.of_int (12)) round_key;
      Vale_X64_InsAes.va_code_AESNI_enc (Prims.of_int (13)) round_key;
      Vale_X64_InsAes.va_code_AESNI_enc (Prims.of_int (14)) round_key]
let (va_codegen_success_Aes_round_4way :
  Vale_X64_Machine_s.reg_xmm -> Vale_X64_Decls.va_pbool) =
  fun round_key ->
    Vale_X64_Decls.va_pbool_and
      (Vale_X64_InsAes.va_codegen_success_AESNI_enc (Prims.of_int (2))
         round_key)
      (Vale_X64_Decls.va_pbool_and
         (Vale_X64_InsAes.va_codegen_success_AESNI_enc (Prims.of_int (12))
            round_key)
         (Vale_X64_Decls.va_pbool_and
            (Vale_X64_InsAes.va_codegen_success_AESNI_enc (Prims.of_int (13))
               round_key)
            (Vale_X64_Decls.va_pbool_and
               (Vale_X64_InsAes.va_codegen_success_AESNI_enc
                  (Prims.of_int (14)) round_key) (Vale_X64_Decls.va_ttrue ()))))
type ('alg, 'n, 'roundukey, 'init1, 'init2, 'init3, 'init4, 'roundukeys,
  'vaus0, 'vauk) va_wp_Aes_round_4way = unit

let (va_code_Aes_2rounds_4way :
  unit ->
    (Vale_X64_Decls.ins, Vale_X64_Decls.ocmp) Vale_X64_Machine_s.precode)
  =
  fun uu___ ->
    Vale_X64_Machine_s.Block
      [va_code_Aes_round_4way (Prims.of_int (3));
      va_code_Aes_round_4way (Prims.of_int (4))]
let (va_codegen_success_Aes_2rounds_4way : unit -> Vale_X64_Decls.va_pbool) =
  fun uu___ ->
    Vale_X64_Decls.va_pbool_and
      (va_codegen_success_Aes_round_4way (Prims.of_int (3)))
      (Vale_X64_Decls.va_pbool_and
         (va_codegen_success_Aes_round_4way (Prims.of_int (4)))
         (Vale_X64_Decls.va_ttrue ()))

type ('alg, 'n, 'init1, 'init2, 'init3, 'init4, 'roundukeys, 'vaus0,
  'vauk) va_wp_Aes_2rounds_4way = unit

let (va_code_Aes_3rounds_4way :
  unit ->
    (Vale_X64_Decls.ins, Vale_X64_Decls.ocmp) Vale_X64_Machine_s.precode)
  =
  fun uu___ ->
    Vale_X64_Machine_s.Block
      [va_code_Aes_round_4way (Prims.of_int (4));
      va_code_Aes_round_4way (Prims.of_int (5));
      va_code_Aes_round_4way (Prims.of_int (6))]
let (va_codegen_success_Aes_3rounds_4way : unit -> Vale_X64_Decls.va_pbool) =
  fun uu___ ->
    Vale_X64_Decls.va_pbool_and
      (va_codegen_success_Aes_round_4way (Prims.of_int (4)))
      (Vale_X64_Decls.va_pbool_and
         (va_codegen_success_Aes_round_4way (Prims.of_int (5)))
         (Vale_X64_Decls.va_pbool_and
            (va_codegen_success_Aes_round_4way (Prims.of_int (6)))
            (Vale_X64_Decls.va_ttrue ())))

type ('alg, 'n, 'init1, 'init2, 'init3, 'init4, 'roundukeys, 'vaus0,
  'vauk) va_wp_Aes_3rounds_4way = unit

let (va_code_Aes_4rounds_4way :
  unit ->
    (Vale_X64_Decls.ins, Vale_X64_Decls.ocmp) Vale_X64_Machine_s.precode)
  =
  fun uu___ ->
    Vale_X64_Machine_s.Block
      [va_code_Aes_round_4way (Prims.of_int (3));
      va_code_Aes_round_4way (Prims.of_int (4));
      va_code_Aes_round_4way (Prims.of_int (5));
      va_code_Aes_round_4way (Prims.of_int (6))]
let (va_codegen_success_Aes_4rounds_4way : unit -> Vale_X64_Decls.va_pbool) =
  fun uu___ ->
    Vale_X64_Decls.va_pbool_and
      (va_codegen_success_Aes_round_4way (Prims.of_int (3)))
      (Vale_X64_Decls.va_pbool_and
         (va_codegen_success_Aes_round_4way (Prims.of_int (4)))
         (Vale_X64_Decls.va_pbool_and
            (va_codegen_success_Aes_round_4way (Prims.of_int (5)))
            (Vale_X64_Decls.va_pbool_and
               (va_codegen_success_Aes_round_4way (Prims.of_int (6)))
               (Vale_X64_Decls.va_ttrue ()))))

type ('alg, 'n, 'init1, 'init2, 'init3, 'init4, 'roundukeys, 'vaus0,
  'vauk) va_wp_Aes_4rounds_4way = unit

let (va_code_Aes_ctr_encrypt :
  Vale_AES_AES_common_s.algorithm ->
    (Vale_X64_Decls.ins, Vale_X64_Decls.ocmp) Vale_X64_Machine_s.precode)
  =
  fun alg ->
    Vale_X64_Machine_s.Block
      [va_code_Aes_3rounds_4way ();
      Vale_X64_InsVector.va_code_Load128_buffer Prims.int_zero
        (Prims.of_int (3)) (Vale_X64_Machine_s.OReg (Prims.of_int (8)))
        (Prims.of_int (64)) Vale_Arch_HeapTypes_s.Secret;
      Vale_X64_InsVector.va_code_Load128_buffer Prims.int_zero
        (Prims.of_int (4)) (Vale_X64_Machine_s.OReg (Prims.of_int (8)))
        (Prims.of_int (80)) Vale_Arch_HeapTypes_s.Secret;
      Vale_X64_InsVector.va_code_Load128_buffer Prims.int_zero
        (Prims.of_int (5)) (Vale_X64_Machine_s.OReg (Prims.of_int (8)))
        (Prims.of_int (96)) Vale_Arch_HeapTypes_s.Secret;
      Vale_X64_InsVector.va_code_Load128_buffer Prims.int_zero
        (Prims.of_int (6)) (Vale_X64_Machine_s.OReg (Prims.of_int (8)))
        (Prims.of_int (112)) Vale_Arch_HeapTypes_s.Secret;
      Vale_X64_Machine_s.Block [];
      Vale_X64_Machine_s.Block [];
      Vale_X64_Machine_s.Block [];
      Vale_X64_Machine_s.Block [];
      va_code_Aes_4rounds_4way ();
      Vale_X64_InsVector.va_code_Load128_buffer Prims.int_zero
        (Prims.of_int (3)) (Vale_X64_Machine_s.OReg (Prims.of_int (8)))
        (Prims.of_int (128)) Vale_Arch_HeapTypes_s.Secret;
      Vale_X64_InsVector.va_code_Load128_buffer Prims.int_zero
        (Prims.of_int (4)) (Vale_X64_Machine_s.OReg (Prims.of_int (8)))
        (Prims.of_int (144)) Vale_Arch_HeapTypes_s.Secret;
      Vale_X64_InsVector.va_code_Load128_buffer Prims.int_zero
        (Prims.of_int (5)) (Vale_X64_Machine_s.OReg (Prims.of_int (8)))
        (Prims.of_int (160)) Vale_Arch_HeapTypes_s.Secret;
      Vale_X64_Machine_s.Block [];
      Vale_X64_Machine_s.Block [];
      Vale_X64_Machine_s.Block [];
      va_code_Aes_2rounds_4way ();
      if alg = Vale_AES_AES_common_s.AES_256
      then
        Vale_X64_Machine_s.Block
          [Vale_X64_InsVector.va_code_Mov128 (Prims.of_int (3))
             (Prims.of_int (5));
          Vale_X64_InsVector.va_code_Load128_buffer Prims.int_zero
            (Prims.of_int (4)) (Vale_X64_Machine_s.OReg (Prims.of_int (8)))
            (Prims.of_int (176)) Vale_Arch_HeapTypes_s.Secret;
          Vale_X64_InsVector.va_code_Load128_buffer Prims.int_zero
            (Prims.of_int (5)) (Vale_X64_Machine_s.OReg (Prims.of_int (8)))
            (Prims.of_int (192)) Vale_Arch_HeapTypes_s.Secret;
          Vale_X64_InsVector.va_code_Load128_buffer Prims.int_zero
            (Prims.of_int (6)) (Vale_X64_Machine_s.OReg (Prims.of_int (8)))
            (Prims.of_int (208)) Vale_Arch_HeapTypes_s.Secret;
          Vale_X64_Machine_s.Block [];
          Vale_X64_Machine_s.Block [];
          Vale_X64_Machine_s.Block [];
          Vale_X64_Machine_s.Block [];
          va_code_Aes_4rounds_4way ();
          Vale_X64_InsVector.va_code_Load128_buffer Prims.int_zero
            (Prims.of_int (5)) (Vale_X64_Machine_s.OReg (Prims.of_int (8)))
            (Prims.of_int (224)) Vale_Arch_HeapTypes_s.Secret;
          Vale_X64_Machine_s.Block []]
      else Vale_X64_Machine_s.Block [];
      Vale_X64_InsAes.va_code_AESNI_enc_last (Prims.of_int (2))
        (Prims.of_int (5));
      Vale_X64_InsAes.va_code_AESNI_enc_last (Prims.of_int (12))
        (Prims.of_int (5));
      Vale_X64_InsAes.va_code_AESNI_enc_last (Prims.of_int (13))
        (Prims.of_int (5));
      Vale_X64_InsAes.va_code_AESNI_enc_last (Prims.of_int (14))
        (Prims.of_int (5))]
let (va_codegen_success_Aes_ctr_encrypt :
  Vale_AES_AES_common_s.algorithm -> Vale_X64_Decls.va_pbool) =
  fun alg ->
    Vale_X64_Decls.va_pbool_and (va_codegen_success_Aes_3rounds_4way ())
      (Vale_X64_Decls.va_pbool_and
         (Vale_X64_InsVector.va_codegen_success_Load128_buffer Prims.int_zero
            (Prims.of_int (3)) (Vale_X64_Machine_s.OReg (Prims.of_int (8)))
            (Prims.of_int (64)) Vale_Arch_HeapTypes_s.Secret)
         (Vale_X64_Decls.va_pbool_and
            (Vale_X64_InsVector.va_codegen_success_Load128_buffer
               Prims.int_zero (Prims.of_int (4))
               (Vale_X64_Machine_s.OReg (Prims.of_int (8)))
               (Prims.of_int (80)) Vale_Arch_HeapTypes_s.Secret)
            (Vale_X64_Decls.va_pbool_and
               (Vale_X64_InsVector.va_codegen_success_Load128_buffer
                  Prims.int_zero (Prims.of_int (5))
                  (Vale_X64_Machine_s.OReg (Prims.of_int (8)))
                  (Prims.of_int (96)) Vale_Arch_HeapTypes_s.Secret)
               (Vale_X64_Decls.va_pbool_and
                  (Vale_X64_InsVector.va_codegen_success_Load128_buffer
                     Prims.int_zero (Prims.of_int (6))
                     (Vale_X64_Machine_s.OReg (Prims.of_int (8)))
                     (Prims.of_int (112)) Vale_Arch_HeapTypes_s.Secret)
                  (Vale_X64_Decls.va_pbool_and
                     (va_codegen_success_Aes_4rounds_4way ())
                     (Vale_X64_Decls.va_pbool_and
                        (Vale_X64_InsVector.va_codegen_success_Load128_buffer
                           Prims.int_zero (Prims.of_int (3))
                           (Vale_X64_Machine_s.OReg (Prims.of_int (8)))
                           (Prims.of_int (128)) Vale_Arch_HeapTypes_s.Secret)
                        (Vale_X64_Decls.va_pbool_and
                           (Vale_X64_InsVector.va_codegen_success_Load128_buffer
                              Prims.int_zero (Prims.of_int (4))
                              (Vale_X64_Machine_s.OReg (Prims.of_int (8)))
                              (Prims.of_int (144))
                              Vale_Arch_HeapTypes_s.Secret)
                           (Vale_X64_Decls.va_pbool_and
                              (Vale_X64_InsVector.va_codegen_success_Load128_buffer
                                 Prims.int_zero (Prims.of_int (5))
                                 (Vale_X64_Machine_s.OReg (Prims.of_int (8)))
                                 (Prims.of_int (160))
                                 Vale_Arch_HeapTypes_s.Secret)
                              (Vale_X64_Decls.va_pbool_and
                                 (va_codegen_success_Aes_2rounds_4way ())
                                 (Vale_X64_Decls.va_pbool_and
                                    (if alg = Vale_AES_AES_common_s.AES_256
                                     then
                                       Vale_X64_Decls.va_pbool_and
                                         (Vale_X64_InsVector.va_codegen_success_Mov128
                                            (Prims.of_int (3))
                                            (Prims.of_int (5)))
                                         (Vale_X64_Decls.va_pbool_and
                                            (Vale_X64_InsVector.va_codegen_success_Load128_buffer
                                               Prims.int_zero
                                               (Prims.of_int (4))
                                               (Vale_X64_Machine_s.OReg
                                                  (Prims.of_int (8)))
                                               (Prims.of_int (176))
                                               Vale_Arch_HeapTypes_s.Secret)
                                            (Vale_X64_Decls.va_pbool_and
                                               (Vale_X64_InsVector.va_codegen_success_Load128_buffer
                                                  Prims.int_zero
                                                  (Prims.of_int (5))
                                                  (Vale_X64_Machine_s.OReg
                                                     (Prims.of_int (8)))
                                                  (Prims.of_int (192))
                                                  Vale_Arch_HeapTypes_s.Secret)
                                               (Vale_X64_Decls.va_pbool_and
                                                  (Vale_X64_InsVector.va_codegen_success_Load128_buffer
                                                     Prims.int_zero
                                                     (Prims.of_int (6))
                                                     (Vale_X64_Machine_s.OReg
                                                        (Prims.of_int (8)))
                                                     (Prims.of_int (208))
                                                     Vale_Arch_HeapTypes_s.Secret)
                                                  (Vale_X64_Decls.va_pbool_and
                                                     (va_codegen_success_Aes_4rounds_4way
                                                        ())
                                                     (Vale_X64_Decls.va_pbool_and
                                                        (Vale_X64_InsVector.va_codegen_success_Load128_buffer
                                                           Prims.int_zero
                                                           (Prims.of_int (5))
                                                           (Vale_X64_Machine_s.OReg
                                                              (Prims.of_int (8)))
                                                           (Prims.of_int (224))
                                                           Vale_Arch_HeapTypes_s.Secret)
                                                        (Vale_X64_Decls.va_ttrue
                                                           ()))))))
                                     else Vale_X64_Decls.va_ttrue ())
                                    (Vale_X64_Decls.va_pbool_and
                                       (Vale_X64_InsAes.va_codegen_success_AESNI_enc_last
                                          (Prims.of_int (2))
                                          (Prims.of_int (5)))
                                       (Vale_X64_Decls.va_pbool_and
                                          (Vale_X64_InsAes.va_codegen_success_AESNI_enc_last
                                             (Prims.of_int (12))
                                             (Prims.of_int (5)))
                                          (Vale_X64_Decls.va_pbool_and
                                             (Vale_X64_InsAes.va_codegen_success_AESNI_enc_last
                                                (Prims.of_int (13))
                                                (Prims.of_int (5)))
                                             (Vale_X64_Decls.va_pbool_and
                                                (Vale_X64_InsAes.va_codegen_success_AESNI_enc_last
                                                   (Prims.of_int (14))
                                                   (Prims.of_int (5)))
                                                (Vale_X64_Decls.va_ttrue ())))))))))))))))

type ('alg, 'key, 'roundukeys, 'keysub, 'in1, 'in2, 'in3, 'in4, 'vaus0,
  'vauk) va_wp_Aes_ctr_encrypt = unit

let (va_code_Aes_ctr_ghash :
  unit ->
    (Vale_X64_Decls.ins, Vale_X64_Decls.ocmp) Vale_X64_Machine_s.precode)
  =
  fun uu___ ->
    Vale_X64_Machine_s.Block
      [Vale_AES_X64_GHash.va_code_Compute_ghash_incremental_register ();
      Vale_X64_InsVector.va_code_Mov128 (Prims.of_int (2))
        (Prims.of_int (12));
      Vale_AES_X64_GHash.va_code_Compute_ghash_incremental_register ();
      Vale_X64_InsVector.va_code_Mov128 (Prims.of_int (2))
        (Prims.of_int (13));
      Vale_AES_X64_GHash.va_code_Compute_ghash_incremental_register ();
      Vale_X64_InsVector.va_code_Mov128 (Prims.of_int (2))
        (Prims.of_int (14));
      Vale_AES_X64_GHash.va_code_Compute_ghash_incremental_register ()]
let (va_codegen_success_Aes_ctr_ghash : unit -> Vale_X64_Decls.va_pbool) =
  fun uu___ ->
    Vale_X64_Decls.va_pbool_and
      (Vale_AES_X64_GHash.va_codegen_success_Compute_ghash_incremental_register
         ())
      (Vale_X64_Decls.va_pbool_and
         (Vale_X64_InsVector.va_codegen_success_Mov128 (Prims.of_int (2))
            (Prims.of_int (12)))
         (Vale_X64_Decls.va_pbool_and
            (Vale_AES_X64_GHash.va_codegen_success_Compute_ghash_incremental_register
               ())
            (Vale_X64_Decls.va_pbool_and
               (Vale_X64_InsVector.va_codegen_success_Mov128
                  (Prims.of_int (2)) (Prims.of_int (13)))
               (Vale_X64_Decls.va_pbool_and
                  (Vale_AES_X64_GHash.va_codegen_success_Compute_ghash_incremental_register
                     ())
                  (Vale_X64_Decls.va_pbool_and
                     (Vale_X64_InsVector.va_codegen_success_Mov128
                        (Prims.of_int (2)) (Prims.of_int (14)))
                     (Vale_X64_Decls.va_pbool_and
                        (Vale_AES_X64_GHash.va_codegen_success_Compute_ghash_incremental_register
                           ()) (Vale_X64_Decls.va_ttrue ())))))))

type ('olduoutuptr, 'oldunumuquadublocks, 'count, 'outub, 'hashuinit, 
  'vaus0, 'vauk) va_wp_Aes_ctr_ghash = unit

let (va_code_Aes_ctr_loop_body :
  Vale_AES_AES_common_s.algorithm ->
    (Vale_X64_Decls.ins, Vale_X64_Decls.ocmp) Vale_X64_Machine_s.precode)
  =
  fun alg ->
    Vale_X64_Machine_s.Block
      [Vale_X64_InsVector.va_code_Pinsrq (Prims.of_int (2))
         (Vale_X64_Machine_s.OReg (Prims.of_int (5))) Prims.int_zero;
      Vale_X64_InsVector.va_code_Pinsrq (Prims.of_int (12))
        (Vale_X64_Machine_s.OReg (Prims.of_int (5))) Prims.int_zero;
      Vale_X64_InsVector.va_code_Pinsrq (Prims.of_int (13))
        (Vale_X64_Machine_s.OReg (Prims.of_int (5))) Prims.int_zero;
      Vale_X64_InsVector.va_code_Pinsrq (Prims.of_int (14))
        (Vale_X64_Machine_s.OReg (Prims.of_int (5))) Prims.int_zero;
      Vale_X64_InsVector.va_code_Shufpd (Prims.of_int (2)) (Prims.of_int (9))
        (Prims.of_int (2));
      Vale_X64_InsVector.va_code_Shufpd (Prims.of_int (12))
        (Prims.of_int (9)) Prims.int_zero;
      Vale_X64_InsVector.va_code_Shufpd (Prims.of_int (13))
        (Prims.of_int (10)) (Prims.of_int (2));
      Vale_X64_InsVector.va_code_Shufpd (Prims.of_int (14))
        (Prims.of_int (10)) Prims.int_zero;
      Vale_X64_InsVector.va_code_Pshufb64 (Prims.of_int (9)) Prims.int_zero;
      Vale_X64_InsVector.va_code_Pshufb64 (Prims.of_int (10)) Prims.int_zero;
      Vale_X64_InsVector.va_code_Load128_buffer Prims.int_zero
        (Prims.of_int (3)) (Vale_X64_Machine_s.OReg (Prims.of_int (8)))
        Prims.int_zero Vale_Arch_HeapTypes_s.Secret;
      Vale_X64_InsVector.va_code_Load128_buffer Prims.int_zero
        (Prims.of_int (4)) (Vale_X64_Machine_s.OReg (Prims.of_int (8)))
        (Prims.of_int (16)) Vale_Arch_HeapTypes_s.Secret;
      Vale_X64_InsVector.va_code_Load128_buffer Prims.int_zero
        (Prims.of_int (5)) (Vale_X64_Machine_s.OReg (Prims.of_int (8)))
        (Prims.of_int (32)) Vale_Arch_HeapTypes_s.Secret;
      Vale_X64_InsVector.va_code_Load128_buffer Prims.int_zero
        (Prims.of_int (6)) (Vale_X64_Machine_s.OReg (Prims.of_int (8)))
        (Prims.of_int (48)) Vale_Arch_HeapTypes_s.Secret;
      Vale_X64_Machine_s.Block [];
      Vale_X64_Machine_s.Block [];
      Vale_X64_Machine_s.Block [];
      Vale_X64_Machine_s.Block [];
      Vale_X64_InsVector.va_code_Paddd (Prims.of_int (9)) (Prims.of_int (15));
      Vale_X64_InsVector.va_code_Paddd (Prims.of_int (10))
        (Prims.of_int (15));
      Vale_X64_InsVector.va_code_Pxor (Prims.of_int (2)) (Prims.of_int (3));
      Vale_X64_InsVector.va_code_Pxor (Prims.of_int (12)) (Prims.of_int (3));
      Vale_X64_InsVector.va_code_Pxor (Prims.of_int (13)) (Prims.of_int (3));
      Vale_X64_InsVector.va_code_Pxor (Prims.of_int (14)) (Prims.of_int (3));
      Vale_X64_InsVector.va_code_Pshufb64 (Prims.of_int (9)) Prims.int_zero;
      Vale_X64_InsVector.va_code_Pshufb64 (Prims.of_int (10)) Prims.int_zero;
      va_code_Aes_ctr_encrypt alg;
      Vale_X64_InsVector.va_code_Load128_buffer Prims.int_one
        (Prims.of_int (7)) (Vale_X64_Machine_s.OReg (Prims.of_int (9)))
        Prims.int_zero Vale_Arch_HeapTypes_s.Secret;
      Vale_X64_InsVector.va_code_Pxor (Prims.of_int (2)) (Prims.of_int (7));
      Vale_X64_InsVector.va_code_Load128_buffer Prims.int_one
        (Prims.of_int (7)) (Vale_X64_Machine_s.OReg (Prims.of_int (9)))
        (Prims.of_int (16)) Vale_Arch_HeapTypes_s.Secret;
      Vale_X64_InsVector.va_code_Pxor (Prims.of_int (12)) (Prims.of_int (7));
      Vale_X64_InsVector.va_code_Load128_buffer Prims.int_one
        (Prims.of_int (7)) (Vale_X64_Machine_s.OReg (Prims.of_int (9)))
        (Prims.of_int (32)) Vale_Arch_HeapTypes_s.Secret;
      Vale_X64_InsVector.va_code_Pxor (Prims.of_int (13)) (Prims.of_int (7));
      Vale_X64_InsVector.va_code_Load128_buffer Prims.int_one
        (Prims.of_int (7)) (Vale_X64_Machine_s.OReg (Prims.of_int (9)))
        (Prims.of_int (48)) Vale_Arch_HeapTypes_s.Secret;
      Vale_X64_InsVector.va_code_Pxor (Prims.of_int (14)) (Prims.of_int (7));
      Vale_X64_InsVector.va_code_Store128_buffer Prims.int_one
        (Vale_X64_Machine_s.OReg (Prims.of_int (10))) (Prims.of_int (2))
        Prims.int_zero Vale_Arch_HeapTypes_s.Secret;
      Vale_X64_InsVector.va_code_Store128_buffer Prims.int_one
        (Vale_X64_Machine_s.OReg (Prims.of_int (10))) (Prims.of_int (12))
        (Prims.of_int (16)) Vale_Arch_HeapTypes_s.Secret;
      Vale_X64_InsVector.va_code_Store128_buffer Prims.int_one
        (Vale_X64_Machine_s.OReg (Prims.of_int (10))) (Prims.of_int (13))
        (Prims.of_int (32)) Vale_Arch_HeapTypes_s.Secret;
      Vale_X64_InsVector.va_code_Store128_buffer Prims.int_one
        (Vale_X64_Machine_s.OReg (Prims.of_int (10))) (Prims.of_int (14))
        (Prims.of_int (48)) Vale_Arch_HeapTypes_s.Secret;
      Vale_X64_Machine_s.Block [];
      va_code_Aes_ctr_ghash ();
      Vale_X64_InsBasic.va_code_Sub64
        (Vale_X64_Machine_s.OReg (Prims.of_int (3)))
        (Vale_X64_Machine_s.OConst Prims.int_one);
      Vale_X64_InsBasic.va_code_Add64
        (Vale_X64_Machine_s.OReg (Prims.of_int (9)))
        (Vale_X64_Machine_s.OConst (Prims.of_int (64)));
      Vale_X64_InsBasic.va_code_Add64
        (Vale_X64_Machine_s.OReg (Prims.of_int (10)))
        (Vale_X64_Machine_s.OConst (Prims.of_int (64)))]
let (va_codegen_success_Aes_ctr_loop_body :
  Vale_AES_AES_common_s.algorithm -> Vale_X64_Decls.va_pbool) =
  fun alg ->
    Vale_X64_Decls.va_pbool_and
      (Vale_X64_InsVector.va_codegen_success_Pinsrq (Prims.of_int (2))
         (Vale_X64_Machine_s.OReg (Prims.of_int (5))) Prims.int_zero)
      (Vale_X64_Decls.va_pbool_and
         (Vale_X64_InsVector.va_codegen_success_Pinsrq (Prims.of_int (12))
            (Vale_X64_Machine_s.OReg (Prims.of_int (5))) Prims.int_zero)
         (Vale_X64_Decls.va_pbool_and
            (Vale_X64_InsVector.va_codegen_success_Pinsrq (Prims.of_int (13))
               (Vale_X64_Machine_s.OReg (Prims.of_int (5))) Prims.int_zero)
            (Vale_X64_Decls.va_pbool_and
               (Vale_X64_InsVector.va_codegen_success_Pinsrq
                  (Prims.of_int (14))
                  (Vale_X64_Machine_s.OReg (Prims.of_int (5))) Prims.int_zero)
               (Vale_X64_Decls.va_pbool_and
                  (Vale_X64_InsVector.va_codegen_success_Shufpd
                     (Prims.of_int (2)) (Prims.of_int (9)) (Prims.of_int (2)))
                  (Vale_X64_Decls.va_pbool_and
                     (Vale_X64_InsVector.va_codegen_success_Shufpd
                        (Prims.of_int (12)) (Prims.of_int (9)) Prims.int_zero)
                     (Vale_X64_Decls.va_pbool_and
                        (Vale_X64_InsVector.va_codegen_success_Shufpd
                           (Prims.of_int (13)) (Prims.of_int (10))
                           (Prims.of_int (2)))
                        (Vale_X64_Decls.va_pbool_and
                           (Vale_X64_InsVector.va_codegen_success_Shufpd
                              (Prims.of_int (14)) (Prims.of_int (10))
                              Prims.int_zero)
                           (Vale_X64_Decls.va_pbool_and
                              (Vale_X64_InsVector.va_codegen_success_Pshufb64
                                 (Prims.of_int (9)) Prims.int_zero)
                              (Vale_X64_Decls.va_pbool_and
                                 (Vale_X64_InsVector.va_codegen_success_Pshufb64
                                    (Prims.of_int (10)) Prims.int_zero)
                                 (Vale_X64_Decls.va_pbool_and
                                    (Vale_X64_InsVector.va_codegen_success_Load128_buffer
                                       Prims.int_zero (Prims.of_int (3))
                                       (Vale_X64_Machine_s.OReg
                                          (Prims.of_int (8))) Prims.int_zero
                                       Vale_Arch_HeapTypes_s.Secret)
                                    (Vale_X64_Decls.va_pbool_and
                                       (Vale_X64_InsVector.va_codegen_success_Load128_buffer
                                          Prims.int_zero (Prims.of_int (4))
                                          (Vale_X64_Machine_s.OReg
                                             (Prims.of_int (8)))
                                          (Prims.of_int (16))
                                          Vale_Arch_HeapTypes_s.Secret)
                                       (Vale_X64_Decls.va_pbool_and
                                          (Vale_X64_InsVector.va_codegen_success_Load128_buffer
                                             Prims.int_zero
                                             (Prims.of_int (5))
                                             (Vale_X64_Machine_s.OReg
                                                (Prims.of_int (8)))
                                             (Prims.of_int (32))
                                             Vale_Arch_HeapTypes_s.Secret)
                                          (Vale_X64_Decls.va_pbool_and
                                             (Vale_X64_InsVector.va_codegen_success_Load128_buffer
                                                Prims.int_zero
                                                (Prims.of_int (6))
                                                (Vale_X64_Machine_s.OReg
                                                   (Prims.of_int (8)))
                                                (Prims.of_int (48))
                                                Vale_Arch_HeapTypes_s.Secret)
                                             (Vale_X64_Decls.va_pbool_and
                                                (Vale_X64_InsVector.va_codegen_success_Paddd
                                                   (Prims.of_int (9))
                                                   (Prims.of_int (15)))
                                                (Vale_X64_Decls.va_pbool_and
                                                   (Vale_X64_InsVector.va_codegen_success_Paddd
                                                      (Prims.of_int (10))
                                                      (Prims.of_int (15)))
                                                   (Vale_X64_Decls.va_pbool_and
                                                      (Vale_X64_InsVector.va_codegen_success_Pxor
                                                         (Prims.of_int (2))
                                                         (Prims.of_int (3)))
                                                      (Vale_X64_Decls.va_pbool_and
                                                         (Vale_X64_InsVector.va_codegen_success_Pxor
                                                            (Prims.of_int (12))
                                                            (Prims.of_int (3)))
                                                         (Vale_X64_Decls.va_pbool_and
                                                            (Vale_X64_InsVector.va_codegen_success_Pxor
                                                               (Prims.of_int (13))
                                                               (Prims.of_int (3)))
                                                            (Vale_X64_Decls.va_pbool_and
                                                               (Vale_X64_InsVector.va_codegen_success_Pxor
                                                                  (Prims.of_int (14))
                                                                  (Prims.of_int (3)))
                                                               (Vale_X64_Decls.va_pbool_and
                                                                  (Vale_X64_InsVector.va_codegen_success_Pshufb64
                                                                    (Prims.of_int (9))
                                                                    Prims.int_zero)
                                                                  (Vale_X64_Decls.va_pbool_and
                                                                    (Vale_X64_InsVector.va_codegen_success_Pshufb64
                                                                    (Prims.of_int (10))
                                                                    Prims.int_zero)
                                                                    (Vale_X64_Decls.va_pbool_and
                                                                    (va_codegen_success_Aes_ctr_encrypt
                                                                    alg)
                                                                    (Vale_X64_Decls.va_pbool_and
                                                                    (Vale_X64_InsVector.va_codegen_success_Load128_buffer
                                                                    Prims.int_one
                                                                    (Prims.of_int (7))
                                                                    (Vale_X64_Machine_s.OReg
                                                                    (Prims.of_int (9)))
                                                                    Prims.int_zero
                                                                    Vale_Arch_HeapTypes_s.Secret)
                                                                    (Vale_X64_Decls.va_pbool_and
                                                                    (Vale_X64_InsVector.va_codegen_success_Pxor
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (7)))
                                                                    (Vale_X64_Decls.va_pbool_and
                                                                    (Vale_X64_InsVector.va_codegen_success_Load128_buffer
                                                                    Prims.int_one
                                                                    (Prims.of_int (7))
                                                                    (Vale_X64_Machine_s.OReg
                                                                    (Prims.of_int (9)))
                                                                    (Prims.of_int (16))
                                                                    Vale_Arch_HeapTypes_s.Secret)
                                                                    (Vale_X64_Decls.va_pbool_and
                                                                    (Vale_X64_InsVector.va_codegen_success_Pxor
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (7)))
                                                                    (Vale_X64_Decls.va_pbool_and
                                                                    (Vale_X64_InsVector.va_codegen_success_Load128_buffer
                                                                    Prims.int_one
                                                                    (Prims.of_int (7))
                                                                    (Vale_X64_Machine_s.OReg
                                                                    (Prims.of_int (9)))
                                                                    (Prims.of_int (32))
                                                                    Vale_Arch_HeapTypes_s.Secret)
                                                                    (Vale_X64_Decls.va_pbool_and
                                                                    (Vale_X64_InsVector.va_codegen_success_Pxor
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (7)))
                                                                    (Vale_X64_Decls.va_pbool_and
                                                                    (Vale_X64_InsVector.va_codegen_success_Load128_buffer
                                                                    Prims.int_one
                                                                    (Prims.of_int (7))
                                                                    (Vale_X64_Machine_s.OReg
                                                                    (Prims.of_int (9)))
                                                                    (Prims.of_int (48))
                                                                    Vale_Arch_HeapTypes_s.Secret)
                                                                    (Vale_X64_Decls.va_pbool_and
                                                                    (Vale_X64_InsVector.va_codegen_success_Pxor
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (7)))
                                                                    (Vale_X64_Decls.va_pbool_and
                                                                    (Vale_X64_InsVector.va_codegen_success_Store128_buffer
                                                                    Prims.int_one
                                                                    (Vale_X64_Machine_s.OReg
                                                                    (Prims.of_int (10)))
                                                                    (Prims.of_int (2))
                                                                    Prims.int_zero
                                                                    Vale_Arch_HeapTypes_s.Secret)
                                                                    (Vale_X64_Decls.va_pbool_and
                                                                    (Vale_X64_InsVector.va_codegen_success_Store128_buffer
                                                                    Prims.int_one
                                                                    (Vale_X64_Machine_s.OReg
                                                                    (Prims.of_int (10)))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (16))
                                                                    Vale_Arch_HeapTypes_s.Secret)
                                                                    (Vale_X64_Decls.va_pbool_and
                                                                    (Vale_X64_InsVector.va_codegen_success_Store128_buffer
                                                                    Prims.int_one
                                                                    (Vale_X64_Machine_s.OReg
                                                                    (Prims.of_int (10)))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (32))
                                                                    Vale_Arch_HeapTypes_s.Secret)
                                                                    (Vale_X64_Decls.va_pbool_and
                                                                    (Vale_X64_InsVector.va_codegen_success_Store128_buffer
                                                                    Prims.int_one
                                                                    (Vale_X64_Machine_s.OReg
                                                                    (Prims.of_int (10)))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (48))
                                                                    Vale_Arch_HeapTypes_s.Secret)
                                                                    (Vale_X64_Decls.va_pbool_and
                                                                    (va_codegen_success_Aes_ctr_ghash
                                                                    ())
                                                                    (Vale_X64_Decls.va_pbool_and
                                                                    (Vale_X64_InsBasic.va_codegen_success_Sub64
                                                                    (Vale_X64_Machine_s.OReg
                                                                    (Prims.of_int (3)))
                                                                    (Vale_X64_Machine_s.OConst
                                                                    Prims.int_one))
                                                                    (Vale_X64_Decls.va_pbool_and
                                                                    (Vale_X64_InsBasic.va_codegen_success_Add64
                                                                    (Vale_X64_Machine_s.OReg
                                                                    (Prims.of_int (9)))
                                                                    (Vale_X64_Machine_s.OConst
                                                                    (Prims.of_int (64))))
                                                                    (Vale_X64_Decls.va_pbool_and
                                                                    (Vale_X64_InsBasic.va_codegen_success_Add64
                                                                    (Vale_X64_Machine_s.OReg
                                                                    (Prims.of_int (10)))
                                                                    (Vale_X64_Machine_s.OConst
                                                                    (Prims.of_int (64))))
                                                                    (Vale_X64_Decls.va_ttrue
                                                                    ())))))))))))))))))))))))))))))))))))))))

type ('alg, 'olduplainuptr, 'olduoutuptr, 'oldunumuquadublocks, 'count,
  'plainub, 'outub, 'key, 'roundukeys, 'keysub, 'icbuBE, 'iv, 'hashuinit,
  'vaus0, 'vauk) va_wp_Aes_ctr_loop_body = unit

let (va_code_Aes_counter_loop_body0 :
  Vale_AES_AES_common_s.algorithm ->
    (Vale_X64_Decls.ins, Vale_X64_Decls.ocmp) Vale_X64_Machine_s.precode)
  = fun alg -> Vale_X64_Machine_s.Block [va_code_Aes_ctr_loop_body alg]
let (va_codegen_success_Aes_counter_loop_body0 :
  Vale_AES_AES_common_s.algorithm -> Vale_X64_Decls.va_pbool) =
  fun alg ->
    Vale_X64_Decls.va_pbool_and (va_codegen_success_Aes_ctr_loop_body alg)
      (Vale_X64_Decls.va_ttrue ())

type ('vauold, 'alg, 'vauinuicbuBE, 'vauinukey, 'vauinukeysub, 'vauinuolduiv,
  'vauinuoutub, 'vauinuplainub, 'vauinuroundukeys, 'vauinucount, 'vaus0,
  'vauk) va_wp_Aes_counter_loop_body0 = unit

let (va_code_Aes_counter_loop_while0 :
  Vale_AES_AES_common_s.algorithm ->
    (Vale_X64_Decls.ins, Vale_X64_Decls.ocmp) Vale_X64_Machine_s.precode)
  =
  fun alg ->
    Vale_X64_Machine_s.Block
      [Vale_X64_Machine_s.While
         ((Vale_X64_Decls.va_cmp_gt
             (Vale_X64_Machine_s.OReg (Prims.of_int (3)))
             (Vale_X64_Machine_s.OConst Prims.int_zero)),
           (Vale_X64_Machine_s.Block [va_code_Aes_counter_loop_body0 alg]))]
let (va_codegen_success_Aes_counter_loop_while0 :
  Vale_AES_AES_common_s.algorithm -> Vale_X64_Decls.va_pbool) =
  fun alg ->
    Vale_X64_Decls.va_pbool_and
      (va_codegen_success_Aes_counter_loop_body0 alg)
      (Vale_X64_Decls.va_ttrue ())

type ('vauold, 'alg, 'vauinuicbuBE, 'vauinukey, 'vauinukeysub, 'vauinuolduiv,
  'vauinuoutub, 'vauinuplainub, 'vauinuroundukeys, 'vauinucount, 'vaus0,
  'vauk) va_wp_Aes_counter_loop_while0 = unit

let (va_code_Aes_counter_loop :
  Vale_AES_AES_common_s.algorithm ->
    (Vale_X64_Decls.ins, Vale_X64_Decls.ocmp) Vale_X64_Machine_s.precode)
  =
  fun alg ->
    Vale_X64_Machine_s.Block
      [Vale_X64_InsVector.va_code_Pshufb (Prims.of_int (7))
         (Prims.of_int (8));
      Vale_X64_InsVector.va_code_Mov128 (Prims.of_int (9)) (Prims.of_int (7));
      Vale_X64_InsVector.va_code_InitPshufbDupMask Prims.int_zero
        (Vale_X64_Machine_s.OReg Prims.int_zero);
      Vale_X64_InsVector.va_code_PshufbDup (Prims.of_int (9)) Prims.int_zero;
      Vale_X64_InsVector.va_code_Mov128 (Prims.of_int (10))
        (Prims.of_int (9));
      Vale_X64_InsVector.va_code_ZeroXmm (Prims.of_int (3));
      Vale_X64_InsVector.va_code_PinsrdImm (Prims.of_int (3)) Prims.int_one
        (Prims.of_int (2)) (Vale_X64_Machine_s.OReg Prims.int_zero);
      Vale_X64_InsVector.va_code_Paddd (Prims.of_int (9)) (Prims.of_int (3));
      Vale_X64_InsVector.va_code_PinsrdImm (Prims.of_int (3))
        (Prims.of_int (3)) (Prims.of_int (2))
        (Vale_X64_Machine_s.OReg Prims.int_zero);
      Vale_X64_InsVector.va_code_PinsrdImm (Prims.of_int (3))
        (Prims.of_int (2)) Prims.int_zero
        (Vale_X64_Machine_s.OReg Prims.int_zero);
      Vale_X64_InsVector.va_code_Paddd (Prims.of_int (10)) (Prims.of_int (3));
      Vale_X64_InsVector.va_code_Pshufb (Prims.of_int (9)) (Prims.of_int (8));
      Vale_X64_InsVector.va_code_Pshufb (Prims.of_int (10))
        (Prims.of_int (8));
      Vale_X64_InsVector.va_code_Pextrq
        (Vale_X64_Machine_s.OReg (Prims.of_int (5))) (Prims.of_int (7))
        Prims.int_zero;
      Vale_X64_InsVector.va_code_InitPshufb64Mask Prims.int_zero
        (Vale_X64_Machine_s.OReg Prims.int_zero);
      Vale_X64_InsVector.va_code_ZeroXmm (Prims.of_int (15));
      Vale_X64_InsVector.va_code_PinsrdImm (Prims.of_int (15))
        (Prims.of_int (4)) Prims.int_zero
        (Vale_X64_Machine_s.OReg Prims.int_zero);
      Vale_X64_InsVector.va_code_PinsrdImm (Prims.of_int (15))
        (Prims.of_int (4)) (Prims.of_int (2))
        (Vale_X64_Machine_s.OReg Prims.int_zero);
      va_code_Aes_counter_loop_while0 alg;
      Vale_X64_InsVector.va_code_Mov128 (Prims.of_int (7)) (Prims.of_int (9));
      Vale_X64_InsVector.va_code_Pinsrq (Prims.of_int (7))
        (Vale_X64_Machine_s.OReg (Prims.of_int (5))) Prims.int_zero;
      Vale_X64_InsVector.va_code_Pshufb (Prims.of_int (7)) (Prims.of_int (8))]
let (va_codegen_success_Aes_counter_loop :
  Vale_AES_AES_common_s.algorithm -> Vale_X64_Decls.va_pbool) =
  fun alg ->
    Vale_X64_Decls.va_pbool_and
      (Vale_X64_InsVector.va_codegen_success_Pshufb (Prims.of_int (7))
         (Prims.of_int (8)))
      (Vale_X64_Decls.va_pbool_and
         (Vale_X64_InsVector.va_codegen_success_Mov128 (Prims.of_int (9))
            (Prims.of_int (7)))
         (Vale_X64_Decls.va_pbool_and
            (Vale_X64_InsVector.va_codegen_success_InitPshufbDupMask
               Prims.int_zero (Vale_X64_Machine_s.OReg Prims.int_zero))
            (Vale_X64_Decls.va_pbool_and
               (Vale_X64_InsVector.va_codegen_success_PshufbDup
                  (Prims.of_int (9)) Prims.int_zero)
               (Vale_X64_Decls.va_pbool_and
                  (Vale_X64_InsVector.va_codegen_success_Mov128
                     (Prims.of_int (10)) (Prims.of_int (9)))
                  (Vale_X64_Decls.va_pbool_and
                     (Vale_X64_InsVector.va_codegen_success_ZeroXmm
                        (Prims.of_int (3)))
                     (Vale_X64_Decls.va_pbool_and
                        (Vale_X64_InsVector.va_codegen_success_PinsrdImm
                           (Prims.of_int (3)) Prims.int_one
                           (Prims.of_int (2))
                           (Vale_X64_Machine_s.OReg Prims.int_zero))
                        (Vale_X64_Decls.va_pbool_and
                           (Vale_X64_InsVector.va_codegen_success_Paddd
                              (Prims.of_int (9)) (Prims.of_int (3)))
                           (Vale_X64_Decls.va_pbool_and
                              (Vale_X64_InsVector.va_codegen_success_PinsrdImm
                                 (Prims.of_int (3)) (Prims.of_int (3))
                                 (Prims.of_int (2))
                                 (Vale_X64_Machine_s.OReg Prims.int_zero))
                              (Vale_X64_Decls.va_pbool_and
                                 (Vale_X64_InsVector.va_codegen_success_PinsrdImm
                                    (Prims.of_int (3)) (Prims.of_int (2))
                                    Prims.int_zero
                                    (Vale_X64_Machine_s.OReg Prims.int_zero))
                                 (Vale_X64_Decls.va_pbool_and
                                    (Vale_X64_InsVector.va_codegen_success_Paddd
                                       (Prims.of_int (10)) (Prims.of_int (3)))
                                    (Vale_X64_Decls.va_pbool_and
                                       (Vale_X64_InsVector.va_codegen_success_Pshufb
                                          (Prims.of_int (9))
                                          (Prims.of_int (8)))
                                       (Vale_X64_Decls.va_pbool_and
                                          (Vale_X64_InsVector.va_codegen_success_Pshufb
                                             (Prims.of_int (10))
                                             (Prims.of_int (8)))
                                          (Vale_X64_Decls.va_pbool_and
                                             (Vale_X64_InsVector.va_codegen_success_Pextrq
                                                (Vale_X64_Machine_s.OReg
                                                   (Prims.of_int (5)))
                                                (Prims.of_int (7))
                                                Prims.int_zero)
                                             (Vale_X64_Decls.va_pbool_and
                                                (Vale_X64_InsVector.va_codegen_success_InitPshufb64Mask
                                                   Prims.int_zero
                                                   (Vale_X64_Machine_s.OReg
                                                      Prims.int_zero))
                                                (Vale_X64_Decls.va_pbool_and
                                                   (Vale_X64_InsVector.va_codegen_success_ZeroXmm
                                                      (Prims.of_int (15)))
                                                   (Vale_X64_Decls.va_pbool_and
                                                      (Vale_X64_InsVector.va_codegen_success_PinsrdImm
                                                         (Prims.of_int (15))
                                                         (Prims.of_int (4))
                                                         Prims.int_zero
                                                         (Vale_X64_Machine_s.OReg
                                                            Prims.int_zero))
                                                      (Vale_X64_Decls.va_pbool_and
                                                         (Vale_X64_InsVector.va_codegen_success_PinsrdImm
                                                            (Prims.of_int (15))
                                                            (Prims.of_int (4))
                                                            (Prims.of_int (2))
                                                            (Vale_X64_Machine_s.OReg
                                                               Prims.int_zero))
                                                         (Vale_X64_Decls.va_pbool_and
                                                            (va_codegen_success_Aes_counter_loop_while0
                                                               alg)
                                                            (Vale_X64_Decls.va_pbool_and
                                                               (Vale_X64_InsVector.va_codegen_success_Mov128
                                                                  (Prims.of_int (7))
                                                                  (Prims.of_int (9)))
                                                               (Vale_X64_Decls.va_pbool_and
                                                                  (Vale_X64_InsVector.va_codegen_success_Pinsrq
                                                                    (Prims.of_int (7))
                                                                    (Vale_X64_Machine_s.OReg
                                                                    (Prims.of_int (5)))
                                                                    Prims.int_zero)
                                                                  (Vale_X64_Decls.va_pbool_and
                                                                    (Vale_X64_InsVector.va_codegen_success_Pshufb
                                                                    (Prims.of_int (7))
                                                                    (Prims.of_int (8)))
                                                                    (Vale_X64_Decls.va_ttrue
                                                                    ()))))))))))))))))))))))

type ('alg, 'plainub, 'outub, 'key, 'roundukeys, 'keysub, 'vaus0,
  'vauk) va_wp_Aes_counter_loop = unit
