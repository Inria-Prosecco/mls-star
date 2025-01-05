open Prims
let (lo : Vale_Math_Poly2_s.poly -> Vale_Math_Poly2_s.poly) =
  fun x -> Vale_Math_Poly2.mask x (Prims.of_int (64))
let (hi : Vale_Math_Poly2_s.poly -> Vale_Math_Poly2_s.poly) =
  fun x -> Vale_Math_Poly2_s.shift x (Prims.of_int (-64))
type ('scratchub, 'heap3, 'data, 'z3) scratch_reqs_simple = unit
let va_subscript_FStar__Seq__Base__seq :
  'uuuuu . unit -> 'uuuuu FStar_Seq_Base.seq -> Prims.nat -> 'uuuuu =
  fun uu___ -> FStar_Seq_Base.index
let (va_code_Load_one_msb :
  unit ->
    (Vale_X64_Decls.ins, Vale_X64_Decls.ocmp) Vale_X64_Machine_s.precode)
  =
  fun uu___ ->
    Vale_X64_Machine_s.Block
      [Vale_X64_InsVector.va_code_ZeroXmm (Prims.of_int (2));
      Vale_X64_InsVector.va_code_PinsrqImm (Prims.of_int (2))
        (Prims.parse_int "72057594037927936") Prims.int_one
        (Vale_X64_Machine_s.OReg (Prims.of_int (11)))]
let (va_codegen_success_Load_one_msb : unit -> Vale_X64_Decls.va_pbool) =
  fun uu___ ->
    Vale_X64_Decls.va_pbool_and
      (Vale_X64_InsVector.va_codegen_success_ZeroXmm (Prims.of_int (2)))
      (Vale_X64_Decls.va_pbool_and
         (Vale_X64_InsVector.va_codegen_success_PinsrqImm (Prims.of_int (2))
            (Prims.parse_int "72057594037927936") Prims.int_one
            (Vale_X64_Machine_s.OReg (Prims.of_int (11))))
         (Vale_X64_Decls.va_ttrue ()))

type ('vaus0, 'vauk) va_wp_Load_one_msb = unit

let (va_code_Ctr32_ghash_6_prelude :
  Vale_AES_AES_common_s.algorithm ->
    (Vale_X64_Decls.ins, Vale_X64_Decls.ocmp) Vale_X64_Machine_s.precode)
  =
  fun alg ->
    Vale_X64_Machine_s.Block
      [va_code_Load_one_msb ();
      Vale_X64_InsVector.va_code_VPxor (Prims.of_int (4)) (Prims.of_int (4))
        (Vale_X64_Machine_s.OReg (Prims.of_int (4)));
      Vale_X64_InsVector.va_code_Load128_buffer Prims.int_zero
        (Prims.of_int (15)) (Vale_X64_Machine_s.OReg (Prims.of_int (2)))
        (Prims.of_int (-128)) Vale_Arch_HeapTypes_s.Secret;
      Vale_X64_InsVector.va_code_VPaddd (Prims.of_int (10)) Prims.int_one
        (Prims.of_int (2));
      Vale_X64_InsVector.va_code_VPaddd (Prims.of_int (11))
        (Prims.of_int (10)) (Prims.of_int (2));
      Vale_X64_InsVector.va_code_VPaddd (Prims.of_int (12))
        (Prims.of_int (11)) (Prims.of_int (2));
      Vale_X64_InsVector.va_code_VPaddd (Prims.of_int (13))
        (Prims.of_int (12)) (Prims.of_int (2));
      Vale_X64_InsVector.va_code_VPaddd (Prims.of_int (14))
        (Prims.of_int (13)) (Prims.of_int (2));
      Vale_X64_InsVector.va_code_VPxor (Prims.of_int (9)) Prims.int_one
        (Vale_X64_Machine_s.OReg (Prims.of_int (15)));
      Vale_X64_InsVector.va_code_Store128_buffer (Prims.of_int (3))
        (Vale_X64_Machine_s.OReg (Prims.of_int (6))) (Prims.of_int (4))
        (Prims.of_int (16)) Vale_Arch_HeapTypes_s.Secret]
let (va_codegen_success_Ctr32_ghash_6_prelude :
  Vale_AES_AES_common_s.algorithm -> Vale_X64_Decls.va_pbool) =
  fun alg ->
    Vale_X64_Decls.va_pbool_and (va_codegen_success_Load_one_msb ())
      (Vale_X64_Decls.va_pbool_and
         (Vale_X64_InsVector.va_codegen_success_VPxor (Prims.of_int (4))
            (Prims.of_int (4)) (Vale_X64_Machine_s.OReg (Prims.of_int (4))))
         (Vale_X64_Decls.va_pbool_and
            (Vale_X64_InsVector.va_codegen_success_Load128_buffer
               Prims.int_zero (Prims.of_int (15))
               (Vale_X64_Machine_s.OReg (Prims.of_int (2)))
               (Prims.of_int (-128)) Vale_Arch_HeapTypes_s.Secret)
            (Vale_X64_Decls.va_pbool_and
               (Vale_X64_InsVector.va_codegen_success_VPaddd
                  (Prims.of_int (10)) Prims.int_one (Prims.of_int (2)))
               (Vale_X64_Decls.va_pbool_and
                  (Vale_X64_InsVector.va_codegen_success_VPaddd
                     (Prims.of_int (11)) (Prims.of_int (10))
                     (Prims.of_int (2)))
                  (Vale_X64_Decls.va_pbool_and
                     (Vale_X64_InsVector.va_codegen_success_VPaddd
                        (Prims.of_int (12)) (Prims.of_int (11))
                        (Prims.of_int (2)))
                     (Vale_X64_Decls.va_pbool_and
                        (Vale_X64_InsVector.va_codegen_success_VPaddd
                           (Prims.of_int (13)) (Prims.of_int (12))
                           (Prims.of_int (2)))
                        (Vale_X64_Decls.va_pbool_and
                           (Vale_X64_InsVector.va_codegen_success_VPaddd
                              (Prims.of_int (14)) (Prims.of_int (13))
                              (Prims.of_int (2)))
                           (Vale_X64_Decls.va_pbool_and
                              (Vale_X64_InsVector.va_codegen_success_VPxor
                                 (Prims.of_int (9)) Prims.int_one
                                 (Vale_X64_Machine_s.OReg (Prims.of_int (15))))
                              (Vale_X64_Decls.va_pbool_and
                                 (Vale_X64_InsVector.va_codegen_success_Store128_buffer
                                    (Prims.of_int (3))
                                    (Vale_X64_Machine_s.OReg
                                       (Prims.of_int (6))) (Prims.of_int (4))
                                    (Prims.of_int (16))
                                    Vale_Arch_HeapTypes_s.Secret)
                                 (Vale_X64_Decls.va_ttrue ()))))))))))

type ('alg, 'scratchub, 'keyuwords, 'roundukeys, 'keysub, 'ctruorig, 
  'vaus0, 'vauk) va_wp_Ctr32_ghash_6_prelude = unit

let (va_code_Handle_ctr32_2 :
  unit ->
    (Vale_X64_Decls.ins, Vale_X64_Decls.ocmp) Vale_X64_Machine_s.precode)
  =
  fun uu___ ->
    Vale_X64_Machine_s.Block
      [Vale_X64_InsVector.va_code_VPshufb (Prims.of_int (6)) Prims.int_one
         Prims.int_zero;
      Vale_AES_X64_AESopt.va_code_Load_one_lsb (Prims.of_int (5));
      Vale_X64_InsVector.va_code_VPaddd (Prims.of_int (10))
        (Prims.of_int (6)) (Prims.of_int (5));
      Vale_AES_X64_AESopt.va_code_Load_two_lsb (Prims.of_int (5));
      Vale_X64_InsVector.va_code_VPaddd (Prims.of_int (11))
        (Prims.of_int (6)) (Prims.of_int (5));
      Vale_X64_InsVector.va_code_VPaddd (Prims.of_int (12))
        (Prims.of_int (10)) (Prims.of_int (5));
      Vale_X64_InsVector.va_code_VPshufb (Prims.of_int (10))
        (Prims.of_int (10)) Prims.int_zero;
      Vale_X64_InsVector.va_code_VPaddd (Prims.of_int (13))
        (Prims.of_int (11)) (Prims.of_int (5));
      Vale_X64_InsVector.va_code_VPshufb (Prims.of_int (11))
        (Prims.of_int (11)) Prims.int_zero;
      Vale_X64_InsVector.va_code_VPxor (Prims.of_int (10))
        (Prims.of_int (10)) (Vale_X64_Machine_s.OReg (Prims.of_int (4)));
      Vale_X64_InsVector.va_code_VPaddd (Prims.of_int (14))
        (Prims.of_int (12)) (Prims.of_int (5));
      Vale_X64_InsVector.va_code_VPshufb (Prims.of_int (12))
        (Prims.of_int (12)) Prims.int_zero;
      Vale_X64_InsVector.va_code_VPxor (Prims.of_int (11))
        (Prims.of_int (11)) (Vale_X64_Machine_s.OReg (Prims.of_int (4)));
      Vale_X64_InsVector.va_code_VPaddd Prims.int_one (Prims.of_int (13))
        (Prims.of_int (5));
      Vale_X64_InsVector.va_code_VPshufb (Prims.of_int (13))
        (Prims.of_int (13)) Prims.int_zero;
      Vale_X64_InsVector.va_code_VPxor (Prims.of_int (12))
        (Prims.of_int (12)) (Vale_X64_Machine_s.OReg (Prims.of_int (4)));
      Vale_X64_InsVector.va_code_VPshufb (Prims.of_int (14))
        (Prims.of_int (14)) Prims.int_zero;
      Vale_X64_InsVector.va_code_VPxor (Prims.of_int (13))
        (Prims.of_int (13)) (Vale_X64_Machine_s.OReg (Prims.of_int (4)));
      Vale_X64_InsVector.va_code_VPshufb Prims.int_one Prims.int_one
        Prims.int_zero;
      Vale_X64_InsVector.va_code_VPxor (Prims.of_int (14))
        (Prims.of_int (14)) (Vale_X64_Machine_s.OReg (Prims.of_int (4)))]
let (va_codegen_success_Handle_ctr32_2 : unit -> Vale_X64_Decls.va_pbool) =
  fun uu___ ->
    Vale_X64_Decls.va_pbool_and
      (Vale_X64_InsVector.va_codegen_success_VPshufb (Prims.of_int (6))
         Prims.int_one Prims.int_zero)
      (Vale_X64_Decls.va_pbool_and
         (Vale_AES_X64_AESopt.va_codegen_success_Load_one_lsb
            (Prims.of_int (5)))
         (Vale_X64_Decls.va_pbool_and
            (Vale_X64_InsVector.va_codegen_success_VPaddd (Prims.of_int (10))
               (Prims.of_int (6)) (Prims.of_int (5)))
            (Vale_X64_Decls.va_pbool_and
               (Vale_AES_X64_AESopt.va_codegen_success_Load_two_lsb
                  (Prims.of_int (5)))
               (Vale_X64_Decls.va_pbool_and
                  (Vale_X64_InsVector.va_codegen_success_VPaddd
                     (Prims.of_int (11)) (Prims.of_int (6))
                     (Prims.of_int (5)))
                  (Vale_X64_Decls.va_pbool_and
                     (Vale_X64_InsVector.va_codegen_success_VPaddd
                        (Prims.of_int (12)) (Prims.of_int (10))
                        (Prims.of_int (5)))
                     (Vale_X64_Decls.va_pbool_and
                        (Vale_X64_InsVector.va_codegen_success_VPshufb
                           (Prims.of_int (10)) (Prims.of_int (10))
                           Prims.int_zero)
                        (Vale_X64_Decls.va_pbool_and
                           (Vale_X64_InsVector.va_codegen_success_VPaddd
                              (Prims.of_int (13)) (Prims.of_int (11))
                              (Prims.of_int (5)))
                           (Vale_X64_Decls.va_pbool_and
                              (Vale_X64_InsVector.va_codegen_success_VPshufb
                                 (Prims.of_int (11)) (Prims.of_int (11))
                                 Prims.int_zero)
                              (Vale_X64_Decls.va_pbool_and
                                 (Vale_X64_InsVector.va_codegen_success_VPxor
                                    (Prims.of_int (10)) (Prims.of_int (10))
                                    (Vale_X64_Machine_s.OReg
                                       (Prims.of_int (4))))
                                 (Vale_X64_Decls.va_pbool_and
                                    (Vale_X64_InsVector.va_codegen_success_VPaddd
                                       (Prims.of_int (14))
                                       (Prims.of_int (12)) (Prims.of_int (5)))
                                    (Vale_X64_Decls.va_pbool_and
                                       (Vale_X64_InsVector.va_codegen_success_VPshufb
                                          (Prims.of_int (12))
                                          (Prims.of_int (12)) Prims.int_zero)
                                       (Vale_X64_Decls.va_pbool_and
                                          (Vale_X64_InsVector.va_codegen_success_VPxor
                                             (Prims.of_int (11))
                                             (Prims.of_int (11))
                                             (Vale_X64_Machine_s.OReg
                                                (Prims.of_int (4))))
                                          (Vale_X64_Decls.va_pbool_and
                                             (Vale_X64_InsVector.va_codegen_success_VPaddd
                                                Prims.int_one
                                                (Prims.of_int (13))
                                                (Prims.of_int (5)))
                                             (Vale_X64_Decls.va_pbool_and
                                                (Vale_X64_InsVector.va_codegen_success_VPshufb
                                                   (Prims.of_int (13))
                                                   (Prims.of_int (13))
                                                   Prims.int_zero)
                                                (Vale_X64_Decls.va_pbool_and
                                                   (Vale_X64_InsVector.va_codegen_success_VPxor
                                                      (Prims.of_int (12))
                                                      (Prims.of_int (12))
                                                      (Vale_X64_Machine_s.OReg
                                                         (Prims.of_int (4))))
                                                   (Vale_X64_Decls.va_pbool_and
                                                      (Vale_X64_InsVector.va_codegen_success_VPshufb
                                                         (Prims.of_int (14))
                                                         (Prims.of_int (14))
                                                         Prims.int_zero)
                                                      (Vale_X64_Decls.va_pbool_and
                                                         (Vale_X64_InsVector.va_codegen_success_VPxor
                                                            (Prims.of_int (13))
                                                            (Prims.of_int (13))
                                                            (Vale_X64_Machine_s.OReg
                                                               (Prims.of_int (4))))
                                                         (Vale_X64_Decls.va_pbool_and
                                                            (Vale_X64_InsVector.va_codegen_success_VPshufb
                                                               Prims.int_one
                                                               Prims.int_one
                                                               Prims.int_zero)
                                                            (Vale_X64_Decls.va_pbool_and
                                                               (Vale_X64_InsVector.va_codegen_success_VPxor
                                                                  (Prims.of_int (14))
                                                                  (Prims.of_int (14))
                                                                  (Vale_X64_Machine_s.OReg
                                                                    (Prims.of_int (4))))
                                                               (Vale_X64_Decls.va_ttrue
                                                                  ()))))))))))))))))))))

type ('ctruBE, 'vaus0, 'vauk) va_wp_Handle_ctr32_2 = unit

let (va_code_Loop6x_decrypt :
  Vale_AES_AES_common_s.algorithm ->
    (Vale_X64_Decls.ins, Vale_X64_Decls.ocmp) Vale_X64_Machine_s.precode)
  =
  fun alg ->
    Vale_X64_Machine_s.Block
      [Vale_X64_Machine_s.Block [];
      Vale_X64_Machine_s.Block [];
      Vale_X64_Machine_s.Block [];
      Vale_AES_X64_AESopt.va_code_Loop6x_partial alg;
      Vale_AES_X64_AESopt.va_code_Loop6x_final alg;
      Vale_X64_InsBasic.va_code_Sub64
        (Vale_X64_Machine_s.OReg (Prims.of_int (3)))
        (Vale_X64_Machine_s.OConst (Prims.of_int (6)));
      Vale_X64_Machine_s.IfElse
        ((Vale_X64_Decls.va_cmp_gt
            (Vale_X64_Machine_s.OReg (Prims.of_int (3)))
            (Vale_X64_Machine_s.OConst (Prims.of_int (6)))),
          (Vale_X64_Machine_s.Block
             [Vale_X64_InsBasic.va_code_Add64
                (Vale_X64_Machine_s.OReg (Prims.of_int (14)))
                (Vale_X64_Machine_s.OConst (Prims.of_int (96)))]),
          (Vale_X64_Machine_s.Block []));
      Vale_X64_Machine_s.Block [];
      Vale_X64_Machine_s.Block [];
      Vale_X64_Machine_s.Block [];
      Vale_X64_Machine_s.Block [];
      Vale_X64_Machine_s.IfElse
        ((Vale_X64_Decls.va_cmp_gt
            (Vale_X64_Machine_s.OReg (Prims.of_int (3)))
            (Vale_X64_Machine_s.OConst Prims.int_zero)),
          (Vale_X64_Machine_s.Block
             [Vale_AES_X64_AESopt.va_code_Loop6x_save_output ();
             Vale_X64_InsVector.va_code_Load128_buffer (Prims.of_int (3))
               (Prims.of_int (7))
               (Vale_X64_Machine_s.OReg (Prims.of_int (6)))
               (Prims.of_int (32)) Vale_Arch_HeapTypes_s.Secret;
             Vale_X64_Machine_s.Block []]),
          (Vale_X64_Machine_s.Block
             [Vale_X64_InsVector.va_code_Mem128_lemma ();
             Vale_AES_X64_PolyOps.va_code_VPolyAdd (Prims.of_int (8))
               (Prims.of_int (8))
               (Vale_X64_Machine_s.OMem
                  ((Vale_X64_Machine_s.MReg
                      ((Vale_X64_Machine_s.Reg
                          (Prims.int_zero, (Prims.of_int (6)))),
                        (Prims.of_int (16)))), Vale_Arch_HeapTypes_s.Secret));
             Vale_AES_X64_PolyOps.va_code_VPolyAdd (Prims.of_int (8))
               (Prims.of_int (8))
               (Vale_X64_Machine_s.OReg (Prims.of_int (4)))]))]
let (va_codegen_success_Loop6x_decrypt :
  Vale_AES_AES_common_s.algorithm -> Vale_X64_Decls.va_pbool) =
  fun alg ->
    Vale_X64_Decls.va_pbool_and
      (Vale_AES_X64_AESopt.va_codegen_success_Loop6x_partial alg)
      (Vale_X64_Decls.va_pbool_and
         (Vale_AES_X64_AESopt.va_codegen_success_Loop6x_final alg)
         (Vale_X64_Decls.va_pbool_and
            (Vale_X64_InsBasic.va_codegen_success_Sub64
               (Vale_X64_Machine_s.OReg (Prims.of_int (3)))
               (Vale_X64_Machine_s.OConst (Prims.of_int (6))))
            (Vale_X64_Decls.va_pbool_and
               (Vale_X64_InsBasic.va_codegen_success_Add64
                  (Vale_X64_Machine_s.OReg (Prims.of_int (14)))
                  (Vale_X64_Machine_s.OConst (Prims.of_int (96))))
               (Vale_X64_Decls.va_pbool_and
                  (Vale_X64_Decls.va_pbool_and
                     (Vale_AES_X64_AESopt.va_codegen_success_Loop6x_save_output
                        ())
                     (Vale_X64_Decls.va_pbool_and
                        (Vale_X64_InsVector.va_codegen_success_Load128_buffer
                           (Prims.of_int (3)) (Prims.of_int (7))
                           (Vale_X64_Machine_s.OReg (Prims.of_int (6)))
                           (Prims.of_int (32)) Vale_Arch_HeapTypes_s.Secret)
                        (Vale_X64_Decls.va_pbool_and
                           (Vale_X64_InsVector.va_codegen_success_Mem128_lemma
                              ())
                           (Vale_X64_Decls.va_pbool_and
                              (Vale_AES_X64_PolyOps.va_codegen_success_VPolyAdd
                                 (Prims.of_int (8)) (Prims.of_int (8))
                                 (Vale_X64_Machine_s.OMem
                                    ((Vale_X64_Machine_s.MReg
                                        ((Vale_X64_Machine_s.Reg
                                            (Prims.int_zero,
                                              (Prims.of_int (6)))),
                                          (Prims.of_int (16)))),
                                      Vale_Arch_HeapTypes_s.Secret)))
                              (Vale_AES_X64_PolyOps.va_codegen_success_VPolyAdd
                                 (Prims.of_int (8)) (Prims.of_int (8))
                                 (Vale_X64_Machine_s.OReg (Prims.of_int (4))))))))
                  (Vale_X64_Decls.va_ttrue ())))))

type ('alg, 'huLE, 'yuorig, 'yuprev, 'count, 'ivub, 'in0ub, 'inub, 'outub,
  'scratchub, 'plainuquads, 'keyuwords, 'roundukeys, 'keysub, 'hkeysub,
  'ctruBEuorig, 'ctruBE, 'vaus0, 'vauk) va_wp_Loop6x_decrypt = unit

let (va_code_Loop6x_loop_decrypt_body0 :
  Vale_AES_AES_common_s.algorithm ->
    (Vale_X64_Decls.ins, Vale_X64_Decls.ocmp) Vale_X64_Machine_s.precode)
  =
  fun alg ->
    Vale_X64_Machine_s.Block
      [va_code_Loop6x_decrypt alg; Vale_X64_Machine_s.Block []]
let (va_codegen_success_Loop6x_loop_decrypt_body0 :
  Vale_AES_AES_common_s.algorithm -> Vale_X64_Decls.va_pbool) =
  fun alg ->
    Vale_X64_Decls.va_pbool_and (va_codegen_success_Loop6x_decrypt alg)
      (Vale_X64_Decls.va_ttrue ())

type ('vauold, 'alg, 'vauinuctruBEuorig, 'vauinuhuLE, 'vauinuhkeysub,
  'vauinuin0ub, 'vauinuinub, 'vauinuivub, 'vauinukeyuwords, 'vauinukeysub,
  'vauinuoutub, 'vauinuplainuquads, 'vauinuroundukeys, 'vauinuscratchub,
  'vauinuyuorig, 'vauinuctr, 'vauinuiter, 'vauinuyucur, 'vaus0,
  'vauk) va_wp_Loop6x_loop_decrypt_body0 = unit

let (va_code_Loop6x_loop_decrypt_while0 :
  Vale_AES_AES_common_s.algorithm ->
    (Vale_X64_Decls.ins, Vale_X64_Decls.ocmp) Vale_X64_Machine_s.precode)
  =
  fun alg ->
    Vale_X64_Machine_s.Block
      [Vale_X64_Machine_s.While
         ((Vale_X64_Decls.va_cmp_gt
             (Vale_X64_Machine_s.OReg (Prims.of_int (3)))
             (Vale_X64_Machine_s.OConst Prims.int_zero)),
           (Vale_X64_Machine_s.Block [va_code_Loop6x_loop_decrypt_body0 alg]))]
let (va_codegen_success_Loop6x_loop_decrypt_while0 :
  Vale_AES_AES_common_s.algorithm -> Vale_X64_Decls.va_pbool) =
  fun alg ->
    Vale_X64_Decls.va_pbool_and
      (va_codegen_success_Loop6x_loop_decrypt_body0 alg)
      (Vale_X64_Decls.va_ttrue ())

type ('vauold, 'alg, 'vauinuctruBEuorig, 'vauinuhuLE, 'vauinuhkeysub,
  'vauinuin0ub, 'vauinuinub, 'vauinuivub, 'vauinukeyuwords, 'vauinukeysub,
  'vauinuoutub, 'vauinuplainuquads, 'vauinuroundukeys, 'vauinuscratchub,
  'vauinuyuorig, 'vauinuctr, 'vauinuiter, 'vauinuyucur, 'vaus0,
  'vauk) va_wp_Loop6x_loop_decrypt_while0 = unit

let (va_code_Loop6x_loop_decrypt :
  Vale_AES_AES_common_s.algorithm ->
    (Vale_X64_Decls.ins, Vale_X64_Decls.ocmp) Vale_X64_Machine_s.precode)
  =
  fun alg ->
    Vale_X64_Machine_s.Block
      [Vale_X64_Machine_s.IfElse
         ((Vale_X64_Decls.va_cmp_eq
             (Vale_X64_Machine_s.OReg (Prims.of_int (3)))
             (Vale_X64_Machine_s.OConst (Prims.of_int (6)))),
           (Vale_X64_Machine_s.Block
              [Vale_X64_InsBasic.va_code_Sub64
                 (Vale_X64_Machine_s.OReg (Prims.of_int (14)))
                 (Vale_X64_Machine_s.OConst (Prims.of_int (96)))]),
           (Vale_X64_Machine_s.Block []));
      va_code_Loop6x_loop_decrypt_while0 alg]
let (va_codegen_success_Loop6x_loop_decrypt :
  Vale_AES_AES_common_s.algorithm -> Vale_X64_Decls.va_pbool) =
  fun alg ->
    Vale_X64_Decls.va_pbool_and
      (Vale_X64_InsBasic.va_codegen_success_Sub64
         (Vale_X64_Machine_s.OReg (Prims.of_int (14)))
         (Vale_X64_Machine_s.OConst (Prims.of_int (96))))
      (Vale_X64_Decls.va_pbool_and
         (va_codegen_success_Loop6x_loop_decrypt_while0 alg)
         (Vale_X64_Decls.va_ttrue ()))

type ('alg, 'huLE, 'yuorig, 'yuprev, 'ivub, 'in0ub, 'inub, 'outub,
  'scratchub, 'keyuwords, 'roundukeys, 'keysub, 'hkeysub, 'ctruBEuorig,
  'ctruBE, 'vaus0, 'vauk) va_wp_Loop6x_loop_decrypt = unit

let (va_code_Loop6x_loop_body0 :
  Vale_AES_AES_common_s.algorithm ->
    (Vale_X64_Decls.ins, Vale_X64_Decls.ocmp) Vale_X64_Machine_s.precode)
  =
  fun alg ->
    Vale_X64_Machine_s.Block
      [Vale_AES_X64_AESopt.va_code_Loop6x alg; Vale_X64_Machine_s.Block []]
let (va_codegen_success_Loop6x_loop_body0 :
  Vale_AES_AES_common_s.algorithm -> Vale_X64_Decls.va_pbool) =
  fun alg ->
    Vale_X64_Decls.va_pbool_and
      (Vale_AES_X64_AESopt.va_codegen_success_Loop6x alg)
      (Vale_X64_Decls.va_ttrue ())

type ('vauold, 'alg, 'vauinucount, 'vauinuctruBEuorig, 'vauinuhuLE,
  'vauinuhkeysub, 'vauinuin0ub, 'vauinuinub, 'vauinuivub, 'vauinukeyuwords,
  'vauinukeysub, 'vauinuoutub, 'vauinuplainuquads, 'vauinuroundukeys,
  'vauinuscratchub, 'vauinuyuorig, 'vauinuctr, 'vauinuiter, 'vauinuyucur,
  'vaus0, 'vauk) va_wp_Loop6x_loop_body0 = unit

let (va_code_Loop6x_loop_while0 :
  Vale_AES_AES_common_s.algorithm ->
    (Vale_X64_Decls.ins, Vale_X64_Decls.ocmp) Vale_X64_Machine_s.precode)
  =
  fun alg ->
    Vale_X64_Machine_s.Block
      [Vale_X64_Machine_s.While
         ((Vale_X64_Decls.va_cmp_gt
             (Vale_X64_Machine_s.OReg (Prims.of_int (3)))
             (Vale_X64_Machine_s.OConst Prims.int_zero)),
           (Vale_X64_Machine_s.Block [va_code_Loop6x_loop_body0 alg]))]
let (va_codegen_success_Loop6x_loop_while0 :
  Vale_AES_AES_common_s.algorithm -> Vale_X64_Decls.va_pbool) =
  fun alg ->
    Vale_X64_Decls.va_pbool_and (va_codegen_success_Loop6x_loop_body0 alg)
      (Vale_X64_Decls.va_ttrue ())

type ('vauold, 'alg, 'vauinucount, 'vauinuctruBEuorig, 'vauinuhuLE,
  'vauinuhkeysub, 'vauinuin0ub, 'vauinuinub, 'vauinuivub, 'vauinukeyuwords,
  'vauinukeysub, 'vauinuoutub, 'vauinuplainuquads, 'vauinuroundukeys,
  'vauinuscratchub, 'vauinuyuorig, 'vauinuctr, 'vauinuiter, 'vauinuyucur,
  'vaus0, 'vauk) va_wp_Loop6x_loop_while0 = unit

let (va_code_Loop6x_loop :
  Vale_AES_AES_common_s.algorithm ->
    (Vale_X64_Decls.ins, Vale_X64_Decls.ocmp) Vale_X64_Machine_s.precode)
  = fun alg -> Vale_X64_Machine_s.Block [va_code_Loop6x_loop_while0 alg]
let (va_codegen_success_Loop6x_loop :
  Vale_AES_AES_common_s.algorithm -> Vale_X64_Decls.va_pbool) =
  fun alg ->
    Vale_X64_Decls.va_pbool_and (va_codegen_success_Loop6x_loop_while0 alg)
      (Vale_X64_Decls.va_ttrue ())

type ('alg, 'huLE, 'yuorig, 'yuprev, 'count, 'ivub, 'in0ub, 'inub, 'outub,
  'scratchub, 'plainuquads, 'keyuwords, 'roundukeys, 'keysub, 'hkeysub,
  'ctruBEuorig, 'ctruBE, 'vaus0, 'vauk) va_wp_Loop6x_loop = unit

let (va_code_AESNI_ctr32_6x_preamble :
  Vale_AES_AES_common_s.algorithm ->
    (Vale_X64_Decls.ins, Vale_X64_Decls.ocmp) Vale_X64_Machine_s.precode)
  =
  fun alg ->
    Vale_X64_Machine_s.Block
      [Vale_X64_InsVector.va_code_Load128_buffer Prims.int_zero
         (Prims.of_int (4)) (Vale_X64_Machine_s.OReg (Prims.of_int (2)))
         (Prims.of_int (-128)) Vale_Arch_HeapTypes_s.Secret;
      va_code_Load_one_msb ();
      Vale_X64_InsVector.va_code_Load128_buffer Prims.int_zero
        (Prims.of_int (15)) (Vale_X64_Machine_s.OReg (Prims.of_int (2)))
        (Prims.of_int (-112)) Vale_Arch_HeapTypes_s.Secret;
      Vale_X64_InsBasic.va_code_Mov64
        (Vale_X64_Machine_s.OReg (Prims.of_int (12)))
        (Vale_X64_Machine_s.OReg (Prims.of_int (2)));
      Vale_X64_InsBasic.va_code_Sub64
        (Vale_X64_Machine_s.OReg (Prims.of_int (12)))
        (Vale_X64_Machine_s.OConst (Prims.of_int (96)));
      Vale_X64_InsVector.va_code_VPxor (Prims.of_int (9)) Prims.int_one
        (Vale_X64_Machine_s.OReg (Prims.of_int (4)));
      Vale_X64_InsBasic.va_code_Add64 (Vale_X64_Machine_s.OReg Prims.int_one)
        (Vale_X64_Machine_s.OConst (Prims.of_int (6)));
      Vale_X64_Machine_s.IfElse
        ((Vale_X64_Decls.va_cmp_lt (Vale_X64_Machine_s.OReg Prims.int_one)
            (Vale_X64_Machine_s.OConst (Prims.of_int (256)))),
          (Vale_X64_Machine_s.Block
             [Vale_X64_InsVector.va_code_VPaddd (Prims.of_int (10))
                Prims.int_one (Prims.of_int (2));
             Vale_X64_InsVector.va_code_VPaddd (Prims.of_int (11))
               (Prims.of_int (10)) (Prims.of_int (2));
             Vale_X64_InsVector.va_code_VPxor (Prims.of_int (10))
               (Prims.of_int (10))
               (Vale_X64_Machine_s.OReg (Prims.of_int (4)));
             Vale_X64_InsVector.va_code_VPaddd (Prims.of_int (12))
               (Prims.of_int (11)) (Prims.of_int (2));
             Vale_X64_InsVector.va_code_VPxor (Prims.of_int (11))
               (Prims.of_int (11))
               (Vale_X64_Machine_s.OReg (Prims.of_int (4)));
             Vale_X64_InsVector.va_code_VPaddd (Prims.of_int (13))
               (Prims.of_int (12)) (Prims.of_int (2));
             Vale_X64_InsVector.va_code_VPxor (Prims.of_int (12))
               (Prims.of_int (12))
               (Vale_X64_Machine_s.OReg (Prims.of_int (4)));
             Vale_X64_InsVector.va_code_VPaddd (Prims.of_int (14))
               (Prims.of_int (13)) (Prims.of_int (2));
             Vale_X64_InsVector.va_code_VPxor (Prims.of_int (13))
               (Prims.of_int (13))
               (Vale_X64_Machine_s.OReg (Prims.of_int (4)));
             Vale_X64_InsVector.va_code_VPaddd Prims.int_one
               (Prims.of_int (14)) (Prims.of_int (2));
             Vale_X64_InsVector.va_code_VPxor (Prims.of_int (14))
               (Prims.of_int (14))
               (Vale_X64_Machine_s.OReg (Prims.of_int (4)))]),
          (Vale_X64_Machine_s.Block
             [Vale_X64_InsBasic.va_code_Sub64
                (Vale_X64_Machine_s.OReg Prims.int_one)
                (Vale_X64_Machine_s.OConst (Prims.of_int (256)));
             va_code_Handle_ctr32_2 ()]))]
let (va_codegen_success_AESNI_ctr32_6x_preamble :
  Vale_AES_AES_common_s.algorithm -> Vale_X64_Decls.va_pbool) =
  fun alg ->
    Vale_X64_Decls.va_pbool_and
      (Vale_X64_InsVector.va_codegen_success_Load128_buffer Prims.int_zero
         (Prims.of_int (4)) (Vale_X64_Machine_s.OReg (Prims.of_int (2)))
         (Prims.of_int (-128)) Vale_Arch_HeapTypes_s.Secret)
      (Vale_X64_Decls.va_pbool_and (va_codegen_success_Load_one_msb ())
         (Vale_X64_Decls.va_pbool_and
            (Vale_X64_InsVector.va_codegen_success_Load128_buffer
               Prims.int_zero (Prims.of_int (15))
               (Vale_X64_Machine_s.OReg (Prims.of_int (2)))
               (Prims.of_int (-112)) Vale_Arch_HeapTypes_s.Secret)
            (Vale_X64_Decls.va_pbool_and
               (Vale_X64_InsBasic.va_codegen_success_Mov64
                  (Vale_X64_Machine_s.OReg (Prims.of_int (12)))
                  (Vale_X64_Machine_s.OReg (Prims.of_int (2))))
               (Vale_X64_Decls.va_pbool_and
                  (Vale_X64_InsBasic.va_codegen_success_Sub64
                     (Vale_X64_Machine_s.OReg (Prims.of_int (12)))
                     (Vale_X64_Machine_s.OConst (Prims.of_int (96))))
                  (Vale_X64_Decls.va_pbool_and
                     (Vale_X64_InsVector.va_codegen_success_VPxor
                        (Prims.of_int (9)) Prims.int_one
                        (Vale_X64_Machine_s.OReg (Prims.of_int (4))))
                     (Vale_X64_Decls.va_pbool_and
                        (Vale_X64_InsBasic.va_codegen_success_Add64
                           (Vale_X64_Machine_s.OReg Prims.int_one)
                           (Vale_X64_Machine_s.OConst (Prims.of_int (6))))
                        (Vale_X64_Decls.va_pbool_and
                           (Vale_X64_Decls.va_pbool_and
                              (Vale_X64_InsVector.va_codegen_success_VPaddd
                                 (Prims.of_int (10)) Prims.int_one
                                 (Prims.of_int (2)))
                              (Vale_X64_Decls.va_pbool_and
                                 (Vale_X64_InsVector.va_codegen_success_VPaddd
                                    (Prims.of_int (11)) (Prims.of_int (10))
                                    (Prims.of_int (2)))
                                 (Vale_X64_Decls.va_pbool_and
                                    (Vale_X64_InsVector.va_codegen_success_VPxor
                                       (Prims.of_int (10))
                                       (Prims.of_int (10))
                                       (Vale_X64_Machine_s.OReg
                                          (Prims.of_int (4))))
                                    (Vale_X64_Decls.va_pbool_and
                                       (Vale_X64_InsVector.va_codegen_success_VPaddd
                                          (Prims.of_int (12))
                                          (Prims.of_int (11))
                                          (Prims.of_int (2)))
                                       (Vale_X64_Decls.va_pbool_and
                                          (Vale_X64_InsVector.va_codegen_success_VPxor
                                             (Prims.of_int (11))
                                             (Prims.of_int (11))
                                             (Vale_X64_Machine_s.OReg
                                                (Prims.of_int (4))))
                                          (Vale_X64_Decls.va_pbool_and
                                             (Vale_X64_InsVector.va_codegen_success_VPaddd
                                                (Prims.of_int (13))
                                                (Prims.of_int (12))
                                                (Prims.of_int (2)))
                                             (Vale_X64_Decls.va_pbool_and
                                                (Vale_X64_InsVector.va_codegen_success_VPxor
                                                   (Prims.of_int (12))
                                                   (Prims.of_int (12))
                                                   (Vale_X64_Machine_s.OReg
                                                      (Prims.of_int (4))))
                                                (Vale_X64_Decls.va_pbool_and
                                                   (Vale_X64_InsVector.va_codegen_success_VPaddd
                                                      (Prims.of_int (14))
                                                      (Prims.of_int (13))
                                                      (Prims.of_int (2)))
                                                   (Vale_X64_Decls.va_pbool_and
                                                      (Vale_X64_InsVector.va_codegen_success_VPxor
                                                         (Prims.of_int (13))
                                                         (Prims.of_int (13))
                                                         (Vale_X64_Machine_s.OReg
                                                            (Prims.of_int (4))))
                                                      (Vale_X64_Decls.va_pbool_and
                                                         (Vale_X64_InsVector.va_codegen_success_VPaddd
                                                            Prims.int_one
                                                            (Prims.of_int (14))
                                                            (Prims.of_int (2)))
                                                         (Vale_X64_Decls.va_pbool_and
                                                            (Vale_X64_InsVector.va_codegen_success_VPxor
                                                               (Prims.of_int (14))
                                                               (Prims.of_int (14))
                                                               (Vale_X64_Machine_s.OReg
                                                                  (Prims.of_int (4))))
                                                            (Vale_X64_Decls.va_pbool_and
                                                               (Vale_X64_InsBasic.va_codegen_success_Sub64
                                                                  (Vale_X64_Machine_s.OReg
                                                                    Prims.int_one)
                                                                  (Vale_X64_Machine_s.OConst
                                                                    (Prims.of_int (256))))
                                                               (va_codegen_success_Handle_ctr32_2
                                                                  ())))))))))))))
                           (Vale_X64_Decls.va_ttrue ()))))))))

type ('alg, 'keyuwords, 'roundukeys, 'keysub, 'ctruorig, 'vaus0,
  'vauk) va_wp_AESNI_ctr32_6x_preamble = unit

let (va_code_AESNI_ctr32_6x_loop_body :
  Vale_AES_AES_common_s.algorithm ->
    Prims.nat ->
      (Vale_X64_Decls.ins, Vale_X64_Decls.ocmp) Vale_X64_Machine_s.precode)
  =
  fun alg ->
    fun rnd ->
      Vale_X64_Machine_s.Block
        [Vale_X64_InsAes.va_code_VAESNI_enc (Prims.of_int (9))
           (Prims.of_int (9)) (Prims.of_int (15));
        Vale_X64_InsAes.va_code_VAESNI_enc (Prims.of_int (10))
          (Prims.of_int (10)) (Prims.of_int (15));
        Vale_X64_InsAes.va_code_VAESNI_enc (Prims.of_int (11))
          (Prims.of_int (11)) (Prims.of_int (15));
        Vale_X64_InsAes.va_code_VAESNI_enc (Prims.of_int (12))
          (Prims.of_int (12)) (Prims.of_int (15));
        Vale_X64_InsAes.va_code_VAESNI_enc (Prims.of_int (13))
          (Prims.of_int (13)) (Prims.of_int (15));
        Vale_X64_InsAes.va_code_VAESNI_enc (Prims.of_int (14))
          (Prims.of_int (14)) (Prims.of_int (15));
        Vale_X64_InsVector.va_code_Load128_buffer Prims.int_zero
          (Prims.of_int (15)) (Vale_X64_Machine_s.OReg (Prims.of_int (2)))
          (((Prims.of_int (16)) * (rnd + (Prims.of_int (2)))) -
             (Prims.of_int (128))) Vale_Arch_HeapTypes_s.Secret]
let (va_codegen_success_AESNI_ctr32_6x_loop_body :
  Vale_AES_AES_common_s.algorithm -> Prims.nat -> Vale_X64_Decls.va_pbool) =
  fun alg ->
    fun rnd ->
      Vale_X64_Decls.va_pbool_and
        (Vale_X64_InsAes.va_codegen_success_VAESNI_enc (Prims.of_int (9))
           (Prims.of_int (9)) (Prims.of_int (15)))
        (Vale_X64_Decls.va_pbool_and
           (Vale_X64_InsAes.va_codegen_success_VAESNI_enc (Prims.of_int (10))
              (Prims.of_int (10)) (Prims.of_int (15)))
           (Vale_X64_Decls.va_pbool_and
              (Vale_X64_InsAes.va_codegen_success_VAESNI_enc
                 (Prims.of_int (11)) (Prims.of_int (11)) (Prims.of_int (15)))
              (Vale_X64_Decls.va_pbool_and
                 (Vale_X64_InsAes.va_codegen_success_VAESNI_enc
                    (Prims.of_int (12)) (Prims.of_int (12))
                    (Prims.of_int (15)))
                 (Vale_X64_Decls.va_pbool_and
                    (Vale_X64_InsAes.va_codegen_success_VAESNI_enc
                       (Prims.of_int (13)) (Prims.of_int (13))
                       (Prims.of_int (15)))
                    (Vale_X64_Decls.va_pbool_and
                       (Vale_X64_InsAes.va_codegen_success_VAESNI_enc
                          (Prims.of_int (14)) (Prims.of_int (14))
                          (Prims.of_int (15)))
                       (Vale_X64_Decls.va_pbool_and
                          (Vale_X64_InsVector.va_codegen_success_Load128_buffer
                             Prims.int_zero (Prims.of_int (15))
                             (Vale_X64_Machine_s.OReg (Prims.of_int (2)))
                             (((Prims.of_int (16)) *
                                 (rnd + (Prims.of_int (2))))
                                - (Prims.of_int (128)))
                             Vale_Arch_HeapTypes_s.Secret)
                          (Vale_X64_Decls.va_ttrue ())))))))

type ('alg, 'rnd, 'keyuwords, 'roundukeys, 'keysub, 'init0, 'init1, 'init2,
  'init3, 'init4, 'init5, 'vaus0, 'vauk) va_wp_AESNI_ctr32_6x_loop_body =
  unit

let rec (va_code_AESNI_ctr32_6x_loop_recursive :
  Vale_AES_AES_common_s.algorithm ->
    Prims.nat ->
      (Vale_X64_Decls.ins, Vale_X64_Decls.ocmp) Vale_X64_Machine_s.precode)
  =
  fun alg ->
    fun rnd ->
      Vale_X64_Machine_s.Block
        [if rnd > Prims.int_zero
         then
           Vale_X64_Machine_s.Block
             [va_code_AESNI_ctr32_6x_loop_recursive alg (rnd - Prims.int_one)]
         else Vale_X64_Machine_s.Block [];
        va_code_AESNI_ctr32_6x_loop_body alg rnd]
let rec (va_codegen_success_AESNI_ctr32_6x_loop_recursive :
  Vale_AES_AES_common_s.algorithm -> Prims.nat -> Vale_X64_Decls.va_pbool) =
  fun alg ->
    fun rnd ->
      Vale_X64_Decls.va_pbool_and
        (if rnd > Prims.int_zero
         then
           Vale_X64_Decls.va_pbool_and
             (va_codegen_success_AESNI_ctr32_6x_loop_recursive alg
                (rnd - Prims.int_one)) (Vale_X64_Decls.va_ttrue ())
         else Vale_X64_Decls.va_ttrue ())
        (Vale_X64_Decls.va_pbool_and
           (va_codegen_success_AESNI_ctr32_6x_loop_body alg rnd)
           (Vale_X64_Decls.va_ttrue ()))
type ('alg, 'rnd, 'keyuwords, 'roundukeys, 'keysub, 'init0, 'init1, 'init2,
  'init3, 'init4, 'init5, 'vaus0,
  'vauk) va_wp_AESNI_ctr32_6x_loop_recursive = unit

let (va_code_AESNI_ctr32_6x_round9 :
  Vale_AES_AES_common_s.algorithm ->
    (Vale_X64_Decls.ins, Vale_X64_Decls.ocmp) Vale_X64_Machine_s.precode)
  =
  fun alg ->
    Vale_X64_Machine_s.Block
      [if alg = Vale_AES_AES_common_s.AES_128
       then
         Vale_X64_Machine_s.Block
           [Vale_X64_InsVector.va_code_Load128_buffer Prims.int_zero
              (Prims.of_int (3)) (Vale_X64_Machine_s.OReg (Prims.of_int (2)))
              (Prims.of_int (32)) Vale_Arch_HeapTypes_s.Secret]
       else
         Vale_X64_Machine_s.Block
           [Vale_X64_InsVector.va_code_Load128_buffer Prims.int_zero
              (Prims.of_int (3)) (Vale_X64_Machine_s.OReg (Prims.of_int (2)))
              (Prims.of_int (96)) Vale_Arch_HeapTypes_s.Secret];
      Vale_X64_InsAes.va_code_VAESNI_enc (Prims.of_int (9))
        (Prims.of_int (9)) (Prims.of_int (15));
      Vale_X64_InsVector.va_code_Mem128_lemma ();
      Vale_X64_InsVector.va_code_VPxor (Prims.of_int (4)) (Prims.of_int (3))
        (Vale_X64_Machine_s.OMem
           ((Vale_X64_Machine_s.MReg
               ((Vale_X64_Machine_s.Reg (Prims.int_zero, (Prims.of_int (5)))),
                 Prims.int_zero)), Vale_Arch_HeapTypes_s.Secret));
      Vale_X64_InsAes.va_code_VAESNI_enc (Prims.of_int (10))
        (Prims.of_int (10)) (Prims.of_int (15));
      Vale_X64_InsVector.va_code_Mem128_lemma ();
      Vale_X64_InsVector.va_code_VPxor (Prims.of_int (5)) (Prims.of_int (3))
        (Vale_X64_Machine_s.OMem
           ((Vale_X64_Machine_s.MReg
               ((Vale_X64_Machine_s.Reg (Prims.int_zero, (Prims.of_int (5)))),
                 (Prims.of_int (16)))), Vale_Arch_HeapTypes_s.Secret));
      Vale_X64_InsAes.va_code_VAESNI_enc (Prims.of_int (11))
        (Prims.of_int (11)) (Prims.of_int (15));
      Vale_X64_InsVector.va_code_Mem128_lemma ();
      Vale_X64_InsVector.va_code_VPxor (Prims.of_int (6)) (Prims.of_int (3))
        (Vale_X64_Machine_s.OMem
           ((Vale_X64_Machine_s.MReg
               ((Vale_X64_Machine_s.Reg (Prims.int_zero, (Prims.of_int (5)))),
                 (Prims.of_int (32)))), Vale_Arch_HeapTypes_s.Secret));
      Vale_X64_InsAes.va_code_VAESNI_enc (Prims.of_int (12))
        (Prims.of_int (12)) (Prims.of_int (15));
      Vale_X64_InsVector.va_code_Mem128_lemma ();
      Vale_X64_InsVector.va_code_VPxor (Prims.of_int (8)) (Prims.of_int (3))
        (Vale_X64_Machine_s.OMem
           ((Vale_X64_Machine_s.MReg
               ((Vale_X64_Machine_s.Reg (Prims.int_zero, (Prims.of_int (5)))),
                 (Prims.of_int (48)))), Vale_Arch_HeapTypes_s.Secret));
      Vale_X64_InsAes.va_code_VAESNI_enc (Prims.of_int (13))
        (Prims.of_int (13)) (Prims.of_int (15));
      Vale_X64_InsVector.va_code_Mem128_lemma ();
      Vale_X64_InsVector.va_code_VPxor (Prims.of_int (2)) (Prims.of_int (3))
        (Vale_X64_Machine_s.OMem
           ((Vale_X64_Machine_s.MReg
               ((Vale_X64_Machine_s.Reg (Prims.int_zero, (Prims.of_int (5)))),
                 (Prims.of_int (64)))), Vale_Arch_HeapTypes_s.Secret));
      Vale_X64_InsAes.va_code_VAESNI_enc (Prims.of_int (14))
        (Prims.of_int (14)) (Prims.of_int (15));
      Vale_X64_InsVector.va_code_Mem128_lemma ();
      Vale_X64_InsVector.va_code_VPxor (Prims.of_int (3)) (Prims.of_int (3))
        (Vale_X64_Machine_s.OMem
           ((Vale_X64_Machine_s.MReg
               ((Vale_X64_Machine_s.Reg (Prims.int_zero, (Prims.of_int (5)))),
                 (Prims.of_int (80)))), Vale_Arch_HeapTypes_s.Secret));
      Vale_X64_InsBasic.va_code_AddLea64
        (Vale_X64_Machine_s.OReg (Prims.of_int (5)))
        (Vale_X64_Machine_s.OReg (Prims.of_int (5)))
        (Vale_X64_Machine_s.OConst (Prims.of_int (96)))]
let (va_codegen_success_AESNI_ctr32_6x_round9 :
  Vale_AES_AES_common_s.algorithm -> Vale_X64_Decls.va_pbool) =
  fun alg ->
    Vale_X64_Decls.va_pbool_and
      (if alg = Vale_AES_AES_common_s.AES_128
       then
         Vale_X64_Decls.va_pbool_and
           (Vale_X64_InsVector.va_codegen_success_Load128_buffer
              Prims.int_zero (Prims.of_int (3))
              (Vale_X64_Machine_s.OReg (Prims.of_int (2)))
              (Prims.of_int (32)) Vale_Arch_HeapTypes_s.Secret)
           (Vale_X64_Decls.va_ttrue ())
       else
         Vale_X64_Decls.va_pbool_and
           (Vale_X64_InsVector.va_codegen_success_Load128_buffer
              Prims.int_zero (Prims.of_int (3))
              (Vale_X64_Machine_s.OReg (Prims.of_int (2)))
              (Prims.of_int (96)) Vale_Arch_HeapTypes_s.Secret)
           (Vale_X64_Decls.va_ttrue ()))
      (Vale_X64_Decls.va_pbool_and
         (Vale_X64_InsAes.va_codegen_success_VAESNI_enc (Prims.of_int (9))
            (Prims.of_int (9)) (Prims.of_int (15)))
         (Vale_X64_Decls.va_pbool_and
            (Vale_X64_InsVector.va_codegen_success_Mem128_lemma ())
            (Vale_X64_Decls.va_pbool_and
               (Vale_X64_InsVector.va_codegen_success_VPxor
                  (Prims.of_int (4)) (Prims.of_int (3))
                  (Vale_X64_Machine_s.OMem
                     ((Vale_X64_Machine_s.MReg
                         ((Vale_X64_Machine_s.Reg
                             (Prims.int_zero, (Prims.of_int (5)))),
                           Prims.int_zero)), Vale_Arch_HeapTypes_s.Secret)))
               (Vale_X64_Decls.va_pbool_and
                  (Vale_X64_InsAes.va_codegen_success_VAESNI_enc
                     (Prims.of_int (10)) (Prims.of_int (10))
                     (Prims.of_int (15)))
                  (Vale_X64_Decls.va_pbool_and
                     (Vale_X64_InsVector.va_codegen_success_Mem128_lemma ())
                     (Vale_X64_Decls.va_pbool_and
                        (Vale_X64_InsVector.va_codegen_success_VPxor
                           (Prims.of_int (5)) (Prims.of_int (3))
                           (Vale_X64_Machine_s.OMem
                              ((Vale_X64_Machine_s.MReg
                                  ((Vale_X64_Machine_s.Reg
                                      (Prims.int_zero, (Prims.of_int (5)))),
                                    (Prims.of_int (16)))),
                                Vale_Arch_HeapTypes_s.Secret)))
                        (Vale_X64_Decls.va_pbool_and
                           (Vale_X64_InsAes.va_codegen_success_VAESNI_enc
                              (Prims.of_int (11)) (Prims.of_int (11))
                              (Prims.of_int (15)))
                           (Vale_X64_Decls.va_pbool_and
                              (Vale_X64_InsVector.va_codegen_success_Mem128_lemma
                                 ())
                              (Vale_X64_Decls.va_pbool_and
                                 (Vale_X64_InsVector.va_codegen_success_VPxor
                                    (Prims.of_int (6)) (Prims.of_int (3))
                                    (Vale_X64_Machine_s.OMem
                                       ((Vale_X64_Machine_s.MReg
                                           ((Vale_X64_Machine_s.Reg
                                               (Prims.int_zero,
                                                 (Prims.of_int (5)))),
                                             (Prims.of_int (32)))),
                                         Vale_Arch_HeapTypes_s.Secret)))
                                 (Vale_X64_Decls.va_pbool_and
                                    (Vale_X64_InsAes.va_codegen_success_VAESNI_enc
                                       (Prims.of_int (12))
                                       (Prims.of_int (12))
                                       (Prims.of_int (15)))
                                    (Vale_X64_Decls.va_pbool_and
                                       (Vale_X64_InsVector.va_codegen_success_Mem128_lemma
                                          ())
                                       (Vale_X64_Decls.va_pbool_and
                                          (Vale_X64_InsVector.va_codegen_success_VPxor
                                             (Prims.of_int (8))
                                             (Prims.of_int (3))
                                             (Vale_X64_Machine_s.OMem
                                                ((Vale_X64_Machine_s.MReg
                                                    ((Vale_X64_Machine_s.Reg
                                                        (Prims.int_zero,
                                                          (Prims.of_int (5)))),
                                                      (Prims.of_int (48)))),
                                                  Vale_Arch_HeapTypes_s.Secret)))
                                          (Vale_X64_Decls.va_pbool_and
                                             (Vale_X64_InsAes.va_codegen_success_VAESNI_enc
                                                (Prims.of_int (13))
                                                (Prims.of_int (13))
                                                (Prims.of_int (15)))
                                             (Vale_X64_Decls.va_pbool_and
                                                (Vale_X64_InsVector.va_codegen_success_Mem128_lemma
                                                   ())
                                                (Vale_X64_Decls.va_pbool_and
                                                   (Vale_X64_InsVector.va_codegen_success_VPxor
                                                      (Prims.of_int (2))
                                                      (Prims.of_int (3))
                                                      (Vale_X64_Machine_s.OMem
                                                         ((Vale_X64_Machine_s.MReg
                                                             ((Vale_X64_Machine_s.Reg
                                                                 (Prims.int_zero,
                                                                   (Prims.of_int (5)))),
                                                               (Prims.of_int (64)))),
                                                           Vale_Arch_HeapTypes_s.Secret)))
                                                   (Vale_X64_Decls.va_pbool_and
                                                      (Vale_X64_InsAes.va_codegen_success_VAESNI_enc
                                                         (Prims.of_int (14))
                                                         (Prims.of_int (14))
                                                         (Prims.of_int (15)))
                                                      (Vale_X64_Decls.va_pbool_and
                                                         (Vale_X64_InsVector.va_codegen_success_Mem128_lemma
                                                            ())
                                                         (Vale_X64_Decls.va_pbool_and
                                                            (Vale_X64_InsVector.va_codegen_success_VPxor
                                                               (Prims.of_int (3))
                                                               (Prims.of_int (3))
                                                               (Vale_X64_Machine_s.OMem
                                                                  ((Vale_X64_Machine_s.MReg
                                                                    ((Vale_X64_Machine_s.Reg
                                                                    (Prims.int_zero,
                                                                    (Prims.of_int (5)))),
                                                                    (Prims.of_int (80)))),
                                                                    Vale_Arch_HeapTypes_s.Secret)))
                                                            (Vale_X64_Decls.va_pbool_and
                                                               (Vale_X64_InsBasic.va_codegen_success_AddLea64
                                                                  (Vale_X64_Machine_s.OReg
                                                                    (Prims.of_int (5)))
                                                                  (Vale_X64_Machine_s.OReg
                                                                    (Prims.of_int (5)))
                                                                  (Vale_X64_Machine_s.OConst
                                                                    (Prims.of_int (96))))
                                                               (Vale_X64_Decls.va_ttrue
                                                                  ()))))))))))))))))))))

type ('alg, 'count, 'inub, 'keyuwords, 'roundukeys, 'keysub, 'init0, 
  'init1, 'init2, 'init3, 'init4, 'init5, 'vaus0,
  'vauk) va_wp_AESNI_ctr32_6x_round9 = unit

let (va_code_AESNI_ctr32_6x_final :
  Vale_AES_AES_common_s.algorithm ->
    (Vale_X64_Decls.ins, Vale_X64_Decls.ocmp) Vale_X64_Machine_s.precode)
  =
  fun alg ->
    Vale_X64_Machine_s.Block
      [Vale_X64_InsAes.va_code_VAESNI_enc_last (Prims.of_int (9))
         (Prims.of_int (9)) (Prims.of_int (4));
      Vale_X64_InsAes.va_code_VAESNI_enc_last (Prims.of_int (10))
        (Prims.of_int (10)) (Prims.of_int (5));
      Vale_X64_InsAes.va_code_VAESNI_enc_last (Prims.of_int (11))
        (Prims.of_int (11)) (Prims.of_int (6));
      Vale_X64_InsAes.va_code_VAESNI_enc_last (Prims.of_int (12))
        (Prims.of_int (12)) (Prims.of_int (8));
      Vale_X64_InsAes.va_code_VAESNI_enc_last (Prims.of_int (13))
        (Prims.of_int (13)) (Prims.of_int (2));
      Vale_X64_InsAes.va_code_VAESNI_enc_last (Prims.of_int (14))
        (Prims.of_int (14)) (Prims.of_int (3));
      Vale_X64_InsVector.va_code_Store128_buffer (Prims.of_int (6))
        (Vale_X64_Machine_s.OReg (Prims.of_int (4))) (Prims.of_int (9))
        Prims.int_zero Vale_Arch_HeapTypes_s.Secret;
      Vale_X64_InsVector.va_code_Store128_buffer (Prims.of_int (6))
        (Vale_X64_Machine_s.OReg (Prims.of_int (4))) (Prims.of_int (10))
        (Prims.of_int (16)) Vale_Arch_HeapTypes_s.Secret;
      Vale_X64_InsVector.va_code_Store128_buffer (Prims.of_int (6))
        (Vale_X64_Machine_s.OReg (Prims.of_int (4))) (Prims.of_int (11))
        (Prims.of_int (32)) Vale_Arch_HeapTypes_s.Secret;
      Vale_X64_InsVector.va_code_Store128_buffer (Prims.of_int (6))
        (Vale_X64_Machine_s.OReg (Prims.of_int (4))) (Prims.of_int (12))
        (Prims.of_int (48)) Vale_Arch_HeapTypes_s.Secret;
      Vale_X64_InsVector.va_code_Store128_buffer (Prims.of_int (6))
        (Vale_X64_Machine_s.OReg (Prims.of_int (4))) (Prims.of_int (13))
        (Prims.of_int (64)) Vale_Arch_HeapTypes_s.Secret;
      Vale_X64_InsVector.va_code_Store128_buffer (Prims.of_int (6))
        (Vale_X64_Machine_s.OReg (Prims.of_int (4))) (Prims.of_int (14))
        (Prims.of_int (80)) Vale_Arch_HeapTypes_s.Secret;
      Vale_X64_InsBasic.va_code_AddLea64
        (Vale_X64_Machine_s.OReg (Prims.of_int (4)))
        (Vale_X64_Machine_s.OReg (Prims.of_int (4)))
        (Vale_X64_Machine_s.OConst (Prims.of_int (96)))]
let (va_codegen_success_AESNI_ctr32_6x_final :
  Vale_AES_AES_common_s.algorithm -> Vale_X64_Decls.va_pbool) =
  fun alg ->
    Vale_X64_Decls.va_pbool_and
      (Vale_X64_InsAes.va_codegen_success_VAESNI_enc_last (Prims.of_int (9))
         (Prims.of_int (9)) (Prims.of_int (4)))
      (Vale_X64_Decls.va_pbool_and
         (Vale_X64_InsAes.va_codegen_success_VAESNI_enc_last
            (Prims.of_int (10)) (Prims.of_int (10)) (Prims.of_int (5)))
         (Vale_X64_Decls.va_pbool_and
            (Vale_X64_InsAes.va_codegen_success_VAESNI_enc_last
               (Prims.of_int (11)) (Prims.of_int (11)) (Prims.of_int (6)))
            (Vale_X64_Decls.va_pbool_and
               (Vale_X64_InsAes.va_codegen_success_VAESNI_enc_last
                  (Prims.of_int (12)) (Prims.of_int (12)) (Prims.of_int (8)))
               (Vale_X64_Decls.va_pbool_and
                  (Vale_X64_InsAes.va_codegen_success_VAESNI_enc_last
                     (Prims.of_int (13)) (Prims.of_int (13))
                     (Prims.of_int (2)))
                  (Vale_X64_Decls.va_pbool_and
                     (Vale_X64_InsAes.va_codegen_success_VAESNI_enc_last
                        (Prims.of_int (14)) (Prims.of_int (14))
                        (Prims.of_int (3)))
                     (Vale_X64_Decls.va_pbool_and
                        (Vale_X64_InsVector.va_codegen_success_Store128_buffer
                           (Prims.of_int (6))
                           (Vale_X64_Machine_s.OReg (Prims.of_int (4)))
                           (Prims.of_int (9)) Prims.int_zero
                           Vale_Arch_HeapTypes_s.Secret)
                        (Vale_X64_Decls.va_pbool_and
                           (Vale_X64_InsVector.va_codegen_success_Store128_buffer
                              (Prims.of_int (6))
                              (Vale_X64_Machine_s.OReg (Prims.of_int (4)))
                              (Prims.of_int (10)) (Prims.of_int (16))
                              Vale_Arch_HeapTypes_s.Secret)
                           (Vale_X64_Decls.va_pbool_and
                              (Vale_X64_InsVector.va_codegen_success_Store128_buffer
                                 (Prims.of_int (6))
                                 (Vale_X64_Machine_s.OReg (Prims.of_int (4)))
                                 (Prims.of_int (11)) (Prims.of_int (32))
                                 Vale_Arch_HeapTypes_s.Secret)
                              (Vale_X64_Decls.va_pbool_and
                                 (Vale_X64_InsVector.va_codegen_success_Store128_buffer
                                    (Prims.of_int (6))
                                    (Vale_X64_Machine_s.OReg
                                       (Prims.of_int (4)))
                                    (Prims.of_int (12)) (Prims.of_int (48))
                                    Vale_Arch_HeapTypes_s.Secret)
                                 (Vale_X64_Decls.va_pbool_and
                                    (Vale_X64_InsVector.va_codegen_success_Store128_buffer
                                       (Prims.of_int (6))
                                       (Vale_X64_Machine_s.OReg
                                          (Prims.of_int (4)))
                                       (Prims.of_int (13))
                                       (Prims.of_int (64))
                                       Vale_Arch_HeapTypes_s.Secret)
                                    (Vale_X64_Decls.va_pbool_and
                                       (Vale_X64_InsVector.va_codegen_success_Store128_buffer
                                          (Prims.of_int (6))
                                          (Vale_X64_Machine_s.OReg
                                             (Prims.of_int (4)))
                                          (Prims.of_int (14))
                                          (Prims.of_int (80))
                                          Vale_Arch_HeapTypes_s.Secret)
                                       (Vale_X64_Decls.va_pbool_and
                                          (Vale_X64_InsBasic.va_codegen_success_AddLea64
                                             (Vale_X64_Machine_s.OReg
                                                (Prims.of_int (4)))
                                             (Vale_X64_Machine_s.OReg
                                                (Prims.of_int (4)))
                                             (Vale_X64_Machine_s.OConst
                                                (Prims.of_int (96))))
                                          (Vale_X64_Decls.va_ttrue ())))))))))))))

type ('alg, 'count, 'outub, 'keyuwords, 'roundukeys, 'keysub, 'init0, 
  'init1, 'init2, 'init3, 'init4, 'init5, 'ctr0, 'ctr1, 'ctr2, 'ctr3, 
  'ctr4, 'ctr5, 'plain0, 'plain1, 'plain2, 'plain3, 'plain4, 'plain5, 
  'vaus0, 'vauk) va_wp_AESNI_ctr32_6x_final = unit

let (va_code_AESNI_ctr32_6x :
  Vale_AES_AES_common_s.algorithm ->
    (Vale_X64_Decls.ins, Vale_X64_Decls.ocmp) Vale_X64_Machine_s.precode)
  =
  fun alg ->
    Vale_X64_Machine_s.Block
      [Vale_X64_Machine_s.Block [];
      Vale_X64_Machine_s.Block [];
      Vale_X64_Machine_s.Block [];
      Vale_X64_Machine_s.Block [];
      Vale_X64_Machine_s.Block [];
      Vale_X64_Machine_s.Block [];
      va_code_AESNI_ctr32_6x_preamble alg;
      if alg = Vale_AES_AES_common_s.AES_128
      then
        Vale_X64_Machine_s.Block
          [va_code_AESNI_ctr32_6x_loop_recursive alg (Prims.of_int (7))]
      else
        Vale_X64_Machine_s.Block
          [va_code_AESNI_ctr32_6x_loop_recursive alg (Prims.of_int (11))];
      va_code_AESNI_ctr32_6x_round9 alg;
      va_code_AESNI_ctr32_6x_final alg;
      Vale_X64_Machine_s.Block []]
let (va_codegen_success_AESNI_ctr32_6x :
  Vale_AES_AES_common_s.algorithm -> Vale_X64_Decls.va_pbool) =
  fun alg ->
    Vale_X64_Decls.va_pbool_and
      (va_codegen_success_AESNI_ctr32_6x_preamble alg)
      (Vale_X64_Decls.va_pbool_and
         (if alg = Vale_AES_AES_common_s.AES_128
          then
            Vale_X64_Decls.va_pbool_and
              (va_codegen_success_AESNI_ctr32_6x_loop_recursive alg
                 (Prims.of_int (7))) (Vale_X64_Decls.va_ttrue ())
          else
            Vale_X64_Decls.va_pbool_and
              (va_codegen_success_AESNI_ctr32_6x_loop_recursive alg
                 (Prims.of_int (11))) (Vale_X64_Decls.va_ttrue ()))
         (Vale_X64_Decls.va_pbool_and
            (va_codegen_success_AESNI_ctr32_6x_round9 alg)
            (Vale_X64_Decls.va_pbool_and
               (va_codegen_success_AESNI_ctr32_6x_final alg)
               (Vale_X64_Decls.va_ttrue ()))))

type ('alg, 'count, 'inub, 'outub, 'plainuquads, 'keyuwords, 'roundukeys,
  'keysub, 'ctruBE, 'ctruBEuorig, 'vaus0, 'vauk) va_wp_AESNI_ctr32_6x = 
  unit

let (va_code_Encrypt_save_and_shuffle_output :
  unit ->
    (Vale_X64_Decls.ins, Vale_X64_Decls.ocmp) Vale_X64_Machine_s.precode)
  =
  fun uu___ ->
    Vale_X64_Machine_s.Block
      [Vale_X64_InsVector.va_code_Store128_buffer (Prims.of_int (6))
         (Vale_X64_Machine_s.OReg (Prims.of_int (4))) (Prims.of_int (9))
         (Prims.of_int (-96)) Vale_Arch_HeapTypes_s.Secret;
      Vale_X64_InsVector.va_code_VPshufb (Prims.of_int (9))
        (Prims.of_int (9)) Prims.int_zero;
      Vale_X64_InsVector.va_code_VPxor Prims.int_one Prims.int_one
        (Vale_X64_Machine_s.OReg (Prims.of_int (7)));
      Vale_X64_InsVector.va_code_Store128_buffer (Prims.of_int (6))
        (Vale_X64_Machine_s.OReg (Prims.of_int (4))) (Prims.of_int (10))
        (Prims.of_int (-80)) Vale_Arch_HeapTypes_s.Secret;
      Vale_X64_InsVector.va_code_VPshufb (Prims.of_int (10))
        (Prims.of_int (10)) Prims.int_zero;
      Vale_X64_InsVector.va_code_Store128_buffer (Prims.of_int (6))
        (Vale_X64_Machine_s.OReg (Prims.of_int (4))) (Prims.of_int (11))
        (Prims.of_int (-64)) Vale_Arch_HeapTypes_s.Secret;
      Vale_X64_InsVector.va_code_VPshufb (Prims.of_int (11))
        (Prims.of_int (11)) Prims.int_zero;
      Vale_X64_InsVector.va_code_Store128_buffer (Prims.of_int (6))
        (Vale_X64_Machine_s.OReg (Prims.of_int (4))) (Prims.of_int (12))
        (Prims.of_int (-48)) Vale_Arch_HeapTypes_s.Secret;
      Vale_X64_InsVector.va_code_VPshufb (Prims.of_int (12))
        (Prims.of_int (12)) Prims.int_zero;
      Vale_X64_InsVector.va_code_Store128_buffer (Prims.of_int (6))
        (Vale_X64_Machine_s.OReg (Prims.of_int (4))) (Prims.of_int (13))
        (Prims.of_int (-32)) Vale_Arch_HeapTypes_s.Secret;
      Vale_X64_InsVector.va_code_VPshufb (Prims.of_int (13))
        (Prims.of_int (13)) Prims.int_zero;
      Vale_X64_InsVector.va_code_Store128_buffer (Prims.of_int (6))
        (Vale_X64_Machine_s.OReg (Prims.of_int (4))) (Prims.of_int (14))
        (Prims.of_int (-16)) Vale_Arch_HeapTypes_s.Secret;
      Vale_X64_InsVector.va_code_VPshufb (Prims.of_int (14))
        (Prims.of_int (14)) Prims.int_zero]
let (va_codegen_success_Encrypt_save_and_shuffle_output :
  unit -> Vale_X64_Decls.va_pbool) =
  fun uu___ ->
    Vale_X64_Decls.va_pbool_and
      (Vale_X64_InsVector.va_codegen_success_Store128_buffer
         (Prims.of_int (6)) (Vale_X64_Machine_s.OReg (Prims.of_int (4)))
         (Prims.of_int (9)) (Prims.of_int (-96)) Vale_Arch_HeapTypes_s.Secret)
      (Vale_X64_Decls.va_pbool_and
         (Vale_X64_InsVector.va_codegen_success_VPshufb (Prims.of_int (9))
            (Prims.of_int (9)) Prims.int_zero)
         (Vale_X64_Decls.va_pbool_and
            (Vale_X64_InsVector.va_codegen_success_VPxor Prims.int_one
               Prims.int_one (Vale_X64_Machine_s.OReg (Prims.of_int (7))))
            (Vale_X64_Decls.va_pbool_and
               (Vale_X64_InsVector.va_codegen_success_Store128_buffer
                  (Prims.of_int (6))
                  (Vale_X64_Machine_s.OReg (Prims.of_int (4)))
                  (Prims.of_int (10)) (Prims.of_int (-80))
                  Vale_Arch_HeapTypes_s.Secret)
               (Vale_X64_Decls.va_pbool_and
                  (Vale_X64_InsVector.va_codegen_success_VPshufb
                     (Prims.of_int (10)) (Prims.of_int (10)) Prims.int_zero)
                  (Vale_X64_Decls.va_pbool_and
                     (Vale_X64_InsVector.va_codegen_success_Store128_buffer
                        (Prims.of_int (6))
                        (Vale_X64_Machine_s.OReg (Prims.of_int (4)))
                        (Prims.of_int (11)) (Prims.of_int (-64))
                        Vale_Arch_HeapTypes_s.Secret)
                     (Vale_X64_Decls.va_pbool_and
                        (Vale_X64_InsVector.va_codegen_success_VPshufb
                           (Prims.of_int (11)) (Prims.of_int (11))
                           Prims.int_zero)
                        (Vale_X64_Decls.va_pbool_and
                           (Vale_X64_InsVector.va_codegen_success_Store128_buffer
                              (Prims.of_int (6))
                              (Vale_X64_Machine_s.OReg (Prims.of_int (4)))
                              (Prims.of_int (12)) (Prims.of_int (-48))
                              Vale_Arch_HeapTypes_s.Secret)
                           (Vale_X64_Decls.va_pbool_and
                              (Vale_X64_InsVector.va_codegen_success_VPshufb
                                 (Prims.of_int (12)) (Prims.of_int (12))
                                 Prims.int_zero)
                              (Vale_X64_Decls.va_pbool_and
                                 (Vale_X64_InsVector.va_codegen_success_Store128_buffer
                                    (Prims.of_int (6))
                                    (Vale_X64_Machine_s.OReg
                                       (Prims.of_int (4)))
                                    (Prims.of_int (13)) (Prims.of_int (-32))
                                    Vale_Arch_HeapTypes_s.Secret)
                                 (Vale_X64_Decls.va_pbool_and
                                    (Vale_X64_InsVector.va_codegen_success_VPshufb
                                       (Prims.of_int (13))
                                       (Prims.of_int (13)) Prims.int_zero)
                                    (Vale_X64_Decls.va_pbool_and
                                       (Vale_X64_InsVector.va_codegen_success_Store128_buffer
                                          (Prims.of_int (6))
                                          (Vale_X64_Machine_s.OReg
                                             (Prims.of_int (4)))
                                          (Prims.of_int (14))
                                          (Prims.of_int (-16))
                                          Vale_Arch_HeapTypes_s.Secret)
                                       (Vale_X64_Decls.va_pbool_and
                                          (Vale_X64_InsVector.va_codegen_success_VPshufb
                                             (Prims.of_int (14))
                                             (Prims.of_int (14))
                                             Prims.int_zero)
                                          (Vale_X64_Decls.va_ttrue ())))))))))))))

type ('count, 'outub, 'vaus0, 'vauk) va_wp_Encrypt_save_and_shuffle_output =
  unit

let (va_code_UpdateScratch :
  unit ->
    (Vale_X64_Decls.ins, Vale_X64_Decls.ocmp) Vale_X64_Machine_s.precode)
  =
  fun uu___ ->
    Vale_X64_Machine_s.Block
      [Vale_X64_InsVector.va_code_ZeroXmm (Prims.of_int (4));
      Vale_X64_InsVector.va_code_Mov128 (Prims.of_int (7))
        (Prims.of_int (14));
      Vale_X64_InsVector.va_code_Store128_buffer (Prims.of_int (3))
        (Vale_X64_Machine_s.OReg (Prims.of_int (6))) (Prims.of_int (4))
        (Prims.of_int (16)) Vale_Arch_HeapTypes_s.Secret;
      Vale_X64_InsVector.va_code_Store128_buffer (Prims.of_int (3))
        (Vale_X64_Machine_s.OReg (Prims.of_int (6))) (Prims.of_int (13))
        (Prims.of_int (48)) Vale_Arch_HeapTypes_s.Secret;
      Vale_X64_InsVector.va_code_Store128_buffer (Prims.of_int (3))
        (Vale_X64_Machine_s.OReg (Prims.of_int (6))) (Prims.of_int (12))
        (Prims.of_int (64)) Vale_Arch_HeapTypes_s.Secret;
      Vale_X64_InsVector.va_code_Store128_buffer (Prims.of_int (3))
        (Vale_X64_Machine_s.OReg (Prims.of_int (6))) (Prims.of_int (11))
        (Prims.of_int (80)) Vale_Arch_HeapTypes_s.Secret;
      Vale_X64_InsVector.va_code_Store128_buffer (Prims.of_int (3))
        (Vale_X64_Machine_s.OReg (Prims.of_int (6))) (Prims.of_int (10))
        (Prims.of_int (96)) Vale_Arch_HeapTypes_s.Secret;
      Vale_X64_InsVector.va_code_Store128_buffer (Prims.of_int (3))
        (Vale_X64_Machine_s.OReg (Prims.of_int (6))) (Prims.of_int (9))
        (Prims.of_int (112)) Vale_Arch_HeapTypes_s.Secret]
let (va_codegen_success_UpdateScratch : unit -> Vale_X64_Decls.va_pbool) =
  fun uu___ ->
    Vale_X64_Decls.va_pbool_and
      (Vale_X64_InsVector.va_codegen_success_ZeroXmm (Prims.of_int (4)))
      (Vale_X64_Decls.va_pbool_and
         (Vale_X64_InsVector.va_codegen_success_Mov128 (Prims.of_int (7))
            (Prims.of_int (14)))
         (Vale_X64_Decls.va_pbool_and
            (Vale_X64_InsVector.va_codegen_success_Store128_buffer
               (Prims.of_int (3))
               (Vale_X64_Machine_s.OReg (Prims.of_int (6)))
               (Prims.of_int (4)) (Prims.of_int (16))
               Vale_Arch_HeapTypes_s.Secret)
            (Vale_X64_Decls.va_pbool_and
               (Vale_X64_InsVector.va_codegen_success_Store128_buffer
                  (Prims.of_int (3))
                  (Vale_X64_Machine_s.OReg (Prims.of_int (6)))
                  (Prims.of_int (13)) (Prims.of_int (48))
                  Vale_Arch_HeapTypes_s.Secret)
               (Vale_X64_Decls.va_pbool_and
                  (Vale_X64_InsVector.va_codegen_success_Store128_buffer
                     (Prims.of_int (3))
                     (Vale_X64_Machine_s.OReg (Prims.of_int (6)))
                     (Prims.of_int (12)) (Prims.of_int (64))
                     Vale_Arch_HeapTypes_s.Secret)
                  (Vale_X64_Decls.va_pbool_and
                     (Vale_X64_InsVector.va_codegen_success_Store128_buffer
                        (Prims.of_int (3))
                        (Vale_X64_Machine_s.OReg (Prims.of_int (6)))
                        (Prims.of_int (11)) (Prims.of_int (80))
                        Vale_Arch_HeapTypes_s.Secret)
                     (Vale_X64_Decls.va_pbool_and
                        (Vale_X64_InsVector.va_codegen_success_Store128_buffer
                           (Prims.of_int (3))
                           (Vale_X64_Machine_s.OReg (Prims.of_int (6)))
                           (Prims.of_int (10)) (Prims.of_int (96))
                           Vale_Arch_HeapTypes_s.Secret)
                        (Vale_X64_Decls.va_pbool_and
                           (Vale_X64_InsVector.va_codegen_success_Store128_buffer
                              (Prims.of_int (3))
                              (Vale_X64_Machine_s.OReg (Prims.of_int (6)))
                              (Prims.of_int (9)) (Prims.of_int (112))
                              Vale_Arch_HeapTypes_s.Secret)
                           (Vale_X64_Decls.va_ttrue ()))))))))

type ('scratchub, 'vaus0, 'vauk) va_wp_UpdateScratch = unit

let (va_code_AES_GCM_encrypt_6mult :
  Vale_AES_AES_common_s.algorithm ->
    (Vale_X64_Decls.ins, Vale_X64_Decls.ocmp) Vale_X64_Machine_s.precode)
  =
  fun alg ->
    Vale_X64_Machine_s.Block
      [Vale_X64_Machine_s.IfElse
         ((Vale_X64_Decls.va_cmp_eq
             (Vale_X64_Machine_s.OReg (Prims.of_int (3)))
             (Vale_X64_Machine_s.OConst Prims.int_zero)),
           (Vale_X64_Machine_s.Block
              [Vale_X64_InsVector.va_code_VPshufb Prims.int_one Prims.int_one
                 Prims.int_zero;
              Vale_X64_InsVector.va_code_Store128_buffer (Prims.of_int (3))
                (Vale_X64_Machine_s.OReg (Prims.of_int (6))) Prims.int_one
                (Prims.of_int (32)) Vale_Arch_HeapTypes_s.Secret]),
           (Vale_X64_Machine_s.Block
              [Vale_X64_InsVector.va_code_Store128_buffer (Prims.of_int (3))
                 (Vale_X64_Machine_s.OReg (Prims.of_int (6)))
                 (Prims.of_int (8)) (Prims.of_int (32))
                 Vale_Arch_HeapTypes_s.Secret;
              Vale_X64_InsBasic.va_code_Add64
                (Vale_X64_Machine_s.OReg (Prims.of_int (2)))
                (Vale_X64_Machine_s.OConst (Prims.of_int (128)));
              Vale_X64_InsVector.va_code_Pextrq
                (Vale_X64_Machine_s.OReg Prims.int_one) Prims.int_one
                Prims.int_zero;
              Vale_X64_InsBasic.va_code_And64
                (Vale_X64_Machine_s.OReg Prims.int_one)
                (Vale_X64_Machine_s.OConst (Prims.of_int (255)));
              Vale_X64_InsVector.va_code_VPshufb Prims.int_one Prims.int_one
                Prims.int_zero;
              Vale_X64_InsBasic.va_code_AddLea64
                (Vale_X64_Machine_s.OReg (Prims.of_int (14)))
                (Vale_X64_Machine_s.OReg (Prims.of_int (4)))
                (Vale_X64_Machine_s.OConst (Prims.of_int (96)));
              va_code_AESNI_ctr32_6x alg;
              Vale_X64_InsVector.va_code_VPshufb (Prims.of_int (8))
                (Prims.of_int (9)) Prims.int_zero;
              Vale_X64_InsVector.va_code_VPshufb (Prims.of_int (2))
                (Prims.of_int (10)) Prims.int_zero;
              Vale_X64_InsVector.va_code_Store128_buffer (Prims.of_int (3))
                (Vale_X64_Machine_s.OReg (Prims.of_int (6)))
                (Prims.of_int (8)) (Prims.of_int (112))
                Vale_Arch_HeapTypes_s.Secret;
              Vale_X64_InsVector.va_code_VPshufb (Prims.of_int (4))
                (Prims.of_int (11)) Prims.int_zero;
              Vale_X64_InsVector.va_code_Store128_buffer (Prims.of_int (3))
                (Vale_X64_Machine_s.OReg (Prims.of_int (6)))
                (Prims.of_int (2)) (Prims.of_int (96))
                Vale_Arch_HeapTypes_s.Secret;
              Vale_X64_InsVector.va_code_VPshufb (Prims.of_int (5))
                (Prims.of_int (12)) Prims.int_zero;
              Vale_X64_InsVector.va_code_Store128_buffer (Prims.of_int (3))
                (Vale_X64_Machine_s.OReg (Prims.of_int (6)))
                (Prims.of_int (4)) (Prims.of_int (80))
                Vale_Arch_HeapTypes_s.Secret;
              Vale_X64_InsVector.va_code_VPshufb (Prims.of_int (6))
                (Prims.of_int (13)) Prims.int_zero;
              Vale_X64_InsVector.va_code_Store128_buffer (Prims.of_int (3))
                (Vale_X64_Machine_s.OReg (Prims.of_int (6)))
                (Prims.of_int (5)) (Prims.of_int (64))
                Vale_Arch_HeapTypes_s.Secret;
              Vale_X64_InsVector.va_code_VPshufb (Prims.of_int (7))
                (Prims.of_int (14)) Prims.int_zero;
              Vale_X64_InsVector.va_code_Store128_buffer (Prims.of_int (3))
                (Vale_X64_Machine_s.OReg (Prims.of_int (6)))
                (Prims.of_int (6)) (Prims.of_int (48))
                Vale_Arch_HeapTypes_s.Secret;
              va_code_AESNI_ctr32_6x alg;
              Vale_X64_InsBasic.va_code_Sub64
                (Vale_X64_Machine_s.OReg (Prims.of_int (3)))
                (Vale_X64_Machine_s.OConst (Prims.of_int (12)));
              Vale_X64_InsVector.va_code_Load128_buffer (Prims.of_int (3))
                (Prims.of_int (8))
                (Vale_X64_Machine_s.OReg (Prims.of_int (6)))
                (Prims.of_int (32)) Vale_Arch_HeapTypes_s.Secret;
              va_code_Ctr32_ghash_6_prelude alg;
              va_code_Loop6x_loop alg;
              Vale_X64_InsVector.va_code_Load128_buffer (Prims.of_int (3))
                (Prims.of_int (7))
                (Vale_X64_Machine_s.OReg (Prims.of_int (6)))
                (Prims.of_int (32)) Vale_Arch_HeapTypes_s.Secret;
              Vale_X64_InsVector.va_code_Store128_buffer (Prims.of_int (3))
                (Vale_X64_Machine_s.OReg (Prims.of_int (6))) Prims.int_one
                (Prims.of_int (32)) Vale_Arch_HeapTypes_s.Secret;
              Vale_X64_InsVector.va_code_ZeroXmm (Prims.of_int (4));
              Vale_X64_InsVector.va_code_Store128_buffer (Prims.of_int (3))
                (Vale_X64_Machine_s.OReg (Prims.of_int (6)))
                (Prims.of_int (4)) (Prims.of_int (16))
                Vale_Arch_HeapTypes_s.Secret;
              Vale_X64_Machine_s.Block [];
              Vale_AES_X64_AESopt2.va_code_GhashUnroll6x ();
              Vale_X64_Machine_s.Block [];
              Vale_X64_Machine_s.Block [];
              Vale_X64_InsVector.va_code_InitPshufbMask Prims.int_zero
                (Vale_X64_Machine_s.OReg (Prims.of_int (12)));
              Vale_X64_Machine_s.Block [];
              va_code_Encrypt_save_and_shuffle_output ();
              va_code_UpdateScratch ();
              Vale_X64_Machine_s.Block [];
              Vale_AES_X64_AESopt2.va_code_GhashUnroll6x ();
              Vale_X64_Machine_s.Block [];
              Vale_X64_Machine_s.Block [];
              Vale_X64_Machine_s.Block [];
              Vale_X64_InsBasic.va_code_Sub64
                (Vale_X64_Machine_s.OReg (Prims.of_int (2)))
                (Vale_X64_Machine_s.OConst (Prims.of_int (128)))]))]
let (va_codegen_success_AES_GCM_encrypt_6mult :
  Vale_AES_AES_common_s.algorithm -> Vale_X64_Decls.va_pbool) =
  fun alg ->
    Vale_X64_Decls.va_pbool_and
      (Vale_X64_Decls.va_pbool_and
         (Vale_X64_InsVector.va_codegen_success_VPshufb Prims.int_one
            Prims.int_one Prims.int_zero)
         (Vale_X64_Decls.va_pbool_and
            (Vale_X64_InsVector.va_codegen_success_Store128_buffer
               (Prims.of_int (3))
               (Vale_X64_Machine_s.OReg (Prims.of_int (6))) Prims.int_one
               (Prims.of_int (32)) Vale_Arch_HeapTypes_s.Secret)
            (Vale_X64_Decls.va_pbool_and
               (Vale_X64_InsVector.va_codegen_success_Store128_buffer
                  (Prims.of_int (3))
                  (Vale_X64_Machine_s.OReg (Prims.of_int (6)))
                  (Prims.of_int (8)) (Prims.of_int (32))
                  Vale_Arch_HeapTypes_s.Secret)
               (Vale_X64_Decls.va_pbool_and
                  (Vale_X64_InsBasic.va_codegen_success_Add64
                     (Vale_X64_Machine_s.OReg (Prims.of_int (2)))
                     (Vale_X64_Machine_s.OConst (Prims.of_int (128))))
                  (Vale_X64_Decls.va_pbool_and
                     (Vale_X64_InsVector.va_codegen_success_Pextrq
                        (Vale_X64_Machine_s.OReg Prims.int_one) Prims.int_one
                        Prims.int_zero)
                     (Vale_X64_Decls.va_pbool_and
                        (Vale_X64_InsBasic.va_codegen_success_And64
                           (Vale_X64_Machine_s.OReg Prims.int_one)
                           (Vale_X64_Machine_s.OConst (Prims.of_int (255))))
                        (Vale_X64_Decls.va_pbool_and
                           (Vale_X64_InsVector.va_codegen_success_VPshufb
                              Prims.int_one Prims.int_one Prims.int_zero)
                           (Vale_X64_Decls.va_pbool_and
                              (Vale_X64_InsBasic.va_codegen_success_AddLea64
                                 (Vale_X64_Machine_s.OReg (Prims.of_int (14)))
                                 (Vale_X64_Machine_s.OReg (Prims.of_int (4)))
                                 (Vale_X64_Machine_s.OConst
                                    (Prims.of_int (96))))
                              (Vale_X64_Decls.va_pbool_and
                                 (va_codegen_success_AESNI_ctr32_6x alg)
                                 (Vale_X64_Decls.va_pbool_and
                                    (Vale_X64_InsVector.va_codegen_success_VPshufb
                                       (Prims.of_int (8)) (Prims.of_int (9))
                                       Prims.int_zero)
                                    (Vale_X64_Decls.va_pbool_and
                                       (Vale_X64_InsVector.va_codegen_success_VPshufb
                                          (Prims.of_int (2))
                                          (Prims.of_int (10)) Prims.int_zero)
                                       (Vale_X64_Decls.va_pbool_and
                                          (Vale_X64_InsVector.va_codegen_success_Store128_buffer
                                             (Prims.of_int (3))
                                             (Vale_X64_Machine_s.OReg
                                                (Prims.of_int (6)))
                                             (Prims.of_int (8))
                                             (Prims.of_int (112))
                                             Vale_Arch_HeapTypes_s.Secret)
                                          (Vale_X64_Decls.va_pbool_and
                                             (Vale_X64_InsVector.va_codegen_success_VPshufb
                                                (Prims.of_int (4))
                                                (Prims.of_int (11))
                                                Prims.int_zero)
                                             (Vale_X64_Decls.va_pbool_and
                                                (Vale_X64_InsVector.va_codegen_success_Store128_buffer
                                                   (Prims.of_int (3))
                                                   (Vale_X64_Machine_s.OReg
                                                      (Prims.of_int (6)))
                                                   (Prims.of_int (2))
                                                   (Prims.of_int (96))
                                                   Vale_Arch_HeapTypes_s.Secret)
                                                (Vale_X64_Decls.va_pbool_and
                                                   (Vale_X64_InsVector.va_codegen_success_VPshufb
                                                      (Prims.of_int (5))
                                                      (Prims.of_int (12))
                                                      Prims.int_zero)
                                                   (Vale_X64_Decls.va_pbool_and
                                                      (Vale_X64_InsVector.va_codegen_success_Store128_buffer
                                                         (Prims.of_int (3))
                                                         (Vale_X64_Machine_s.OReg
                                                            (Prims.of_int (6)))
                                                         (Prims.of_int (4))
                                                         (Prims.of_int (80))
                                                         Vale_Arch_HeapTypes_s.Secret)
                                                      (Vale_X64_Decls.va_pbool_and
                                                         (Vale_X64_InsVector.va_codegen_success_VPshufb
                                                            (Prims.of_int (6))
                                                            (Prims.of_int (13))
                                                            Prims.int_zero)
                                                         (Vale_X64_Decls.va_pbool_and
                                                            (Vale_X64_InsVector.va_codegen_success_Store128_buffer
                                                               (Prims.of_int (3))
                                                               (Vale_X64_Machine_s.OReg
                                                                  (Prims.of_int (6)))
                                                               (Prims.of_int (5))
                                                               (Prims.of_int (64))
                                                               Vale_Arch_HeapTypes_s.Secret)
                                                            (Vale_X64_Decls.va_pbool_and
                                                               (Vale_X64_InsVector.va_codegen_success_VPshufb
                                                                  (Prims.of_int (7))
                                                                  (Prims.of_int (14))
                                                                  Prims.int_zero)
                                                               (Vale_X64_Decls.va_pbool_and
                                                                  (Vale_X64_InsVector.va_codegen_success_Store128_buffer
                                                                    (Prims.of_int (3))
                                                                    (Vale_X64_Machine_s.OReg
                                                                    (Prims.of_int (6)))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (48))
                                                                    Vale_Arch_HeapTypes_s.Secret)
                                                                  (Vale_X64_Decls.va_pbool_and
                                                                    (va_codegen_success_AESNI_ctr32_6x
                                                                    alg)
                                                                    (Vale_X64_Decls.va_pbool_and
                                                                    (Vale_X64_InsBasic.va_codegen_success_Sub64
                                                                    (Vale_X64_Machine_s.OReg
                                                                    (Prims.of_int (3)))
                                                                    (Vale_X64_Machine_s.OConst
                                                                    (Prims.of_int (12))))
                                                                    (Vale_X64_Decls.va_pbool_and
                                                                    (Vale_X64_InsVector.va_codegen_success_Load128_buffer
                                                                    (Prims.of_int (3))
                                                                    (Prims.of_int (8))
                                                                    (Vale_X64_Machine_s.OReg
                                                                    (Prims.of_int (6)))
                                                                    (Prims.of_int (32))
                                                                    Vale_Arch_HeapTypes_s.Secret)
                                                                    (Vale_X64_Decls.va_pbool_and
                                                                    (va_codegen_success_Ctr32_ghash_6_prelude
                                                                    alg)
                                                                    (Vale_X64_Decls.va_pbool_and
                                                                    (va_codegen_success_Loop6x_loop
                                                                    alg)
                                                                    (Vale_X64_Decls.va_pbool_and
                                                                    (Vale_X64_InsVector.va_codegen_success_Load128_buffer
                                                                    (Prims.of_int (3))
                                                                    (Prims.of_int (7))
                                                                    (Vale_X64_Machine_s.OReg
                                                                    (Prims.of_int (6)))
                                                                    (Prims.of_int (32))
                                                                    Vale_Arch_HeapTypes_s.Secret)
                                                                    (Vale_X64_Decls.va_pbool_and
                                                                    (Vale_X64_InsVector.va_codegen_success_Store128_buffer
                                                                    (Prims.of_int (3))
                                                                    (Vale_X64_Machine_s.OReg
                                                                    (Prims.of_int (6)))
                                                                    Prims.int_one
                                                                    (Prims.of_int (32))
                                                                    Vale_Arch_HeapTypes_s.Secret)
                                                                    (Vale_X64_Decls.va_pbool_and
                                                                    (Vale_X64_InsVector.va_codegen_success_ZeroXmm
                                                                    (Prims.of_int (4)))
                                                                    (Vale_X64_Decls.va_pbool_and
                                                                    (Vale_X64_InsVector.va_codegen_success_Store128_buffer
                                                                    (Prims.of_int (3))
                                                                    (Vale_X64_Machine_s.OReg
                                                                    (Prims.of_int (6)))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (16))
                                                                    Vale_Arch_HeapTypes_s.Secret)
                                                                    (Vale_X64_Decls.va_pbool_and
                                                                    (Vale_AES_X64_AESopt2.va_codegen_success_GhashUnroll6x
                                                                    ())
                                                                    (Vale_X64_Decls.va_pbool_and
                                                                    (Vale_X64_InsVector.va_codegen_success_InitPshufbMask
                                                                    Prims.int_zero
                                                                    (Vale_X64_Machine_s.OReg
                                                                    (Prims.of_int (12))))
                                                                    (Vale_X64_Decls.va_pbool_and
                                                                    (va_codegen_success_Encrypt_save_and_shuffle_output
                                                                    ())
                                                                    (Vale_X64_Decls.va_pbool_and
                                                                    (va_codegen_success_UpdateScratch
                                                                    ())
                                                                    (Vale_X64_Decls.va_pbool_and
                                                                    (Vale_AES_X64_AESopt2.va_codegen_success_GhashUnroll6x
                                                                    ())
                                                                    (Vale_X64_InsBasic.va_codegen_success_Sub64
                                                                    (Vale_X64_Machine_s.OReg
                                                                    (Prims.of_int (2)))
                                                                    (Vale_X64_Machine_s.OConst
                                                                    (Prims.of_int (128))))))))))))))))))))))))))))))))))))))
      (Vale_X64_Decls.va_ttrue ())

type ('alg, 'huLE, 'ivub, 'inub, 'outub, 'scratchub, 'keyuwords, 'roundukeys,
  'keysub, 'hkeysub, 'vaus0, 'vauk) va_wp_AES_GCM_encrypt_6mult = unit

let (va_code_DecryptPrelude :
  unit ->
    (Vale_X64_Decls.ins, Vale_X64_Decls.ocmp) Vale_X64_Machine_s.precode)
  =
  fun uu___ ->
    Vale_X64_Machine_s.Block
      [Vale_X64_InsVector.va_code_Load128_buffer (Prims.of_int (6))
         (Prims.of_int (7)) (Vale_X64_Machine_s.OReg (Prims.of_int (5)))
         (Prims.of_int (80)) Vale_Arch_HeapTypes_s.Secret;
      Vale_X64_InsVector.va_code_Load128_buffer (Prims.of_int (6))
        (Prims.of_int (4)) (Vale_X64_Machine_s.OReg (Prims.of_int (5)))
        (Prims.of_int (64)) Vale_Arch_HeapTypes_s.Secret;
      Vale_X64_InsVector.va_code_Load128_buffer (Prims.of_int (6))
        (Prims.of_int (5)) (Vale_X64_Machine_s.OReg (Prims.of_int (5)))
        (Prims.of_int (48)) Vale_Arch_HeapTypes_s.Secret;
      Vale_X64_InsVector.va_code_Load128_buffer (Prims.of_int (6))
        (Prims.of_int (6)) (Vale_X64_Machine_s.OReg (Prims.of_int (5)))
        (Prims.of_int (32)) Vale_Arch_HeapTypes_s.Secret;
      Vale_X64_InsVector.va_code_VPshufb (Prims.of_int (7))
        (Prims.of_int (7)) Prims.int_zero;
      Vale_X64_InsVector.va_code_Load128_buffer (Prims.of_int (6))
        (Prims.of_int (2)) (Vale_X64_Machine_s.OReg (Prims.of_int (5)))
        (Prims.of_int (16)) Vale_Arch_HeapTypes_s.Secret;
      Vale_X64_InsVector.va_code_VPshufb (Prims.of_int (4))
        (Prims.of_int (4)) Prims.int_zero;
      Vale_X64_InsVector.va_code_Load128_buffer (Prims.of_int (6))
        (Prims.of_int (3)) (Vale_X64_Machine_s.OReg (Prims.of_int (5)))
        Prims.int_zero Vale_Arch_HeapTypes_s.Secret;
      Vale_X64_InsVector.va_code_VPshufb (Prims.of_int (5))
        (Prims.of_int (5)) Prims.int_zero;
      Vale_X64_InsVector.va_code_Store128_buffer (Prims.of_int (3))
        (Vale_X64_Machine_s.OReg (Prims.of_int (6))) (Prims.of_int (4))
        (Prims.of_int (48)) Vale_Arch_HeapTypes_s.Secret;
      Vale_X64_InsVector.va_code_VPshufb (Prims.of_int (6))
        (Prims.of_int (6)) Prims.int_zero;
      Vale_X64_InsVector.va_code_Store128_buffer (Prims.of_int (3))
        (Vale_X64_Machine_s.OReg (Prims.of_int (6))) (Prims.of_int (5))
        (Prims.of_int (64)) Vale_Arch_HeapTypes_s.Secret;
      Vale_X64_InsVector.va_code_VPshufb (Prims.of_int (2))
        (Prims.of_int (2)) Prims.int_zero;
      Vale_X64_InsVector.va_code_Store128_buffer (Prims.of_int (3))
        (Vale_X64_Machine_s.OReg (Prims.of_int (6))) (Prims.of_int (6))
        (Prims.of_int (80)) Vale_Arch_HeapTypes_s.Secret;
      Vale_X64_InsVector.va_code_VPshufb (Prims.of_int (3))
        (Prims.of_int (3)) Prims.int_zero;
      Vale_X64_InsVector.va_code_Store128_buffer (Prims.of_int (3))
        (Vale_X64_Machine_s.OReg (Prims.of_int (6))) (Prims.of_int (2))
        (Prims.of_int (96)) Vale_Arch_HeapTypes_s.Secret;
      Vale_X64_InsVector.va_code_Store128_buffer (Prims.of_int (3))
        (Vale_X64_Machine_s.OReg (Prims.of_int (6))) (Prims.of_int (3))
        (Prims.of_int (112)) Vale_Arch_HeapTypes_s.Secret]
let (va_codegen_success_DecryptPrelude : unit -> Vale_X64_Decls.va_pbool) =
  fun uu___ ->
    Vale_X64_Decls.va_pbool_and
      (Vale_X64_InsVector.va_codegen_success_Load128_buffer
         (Prims.of_int (6)) (Prims.of_int (7))
         (Vale_X64_Machine_s.OReg (Prims.of_int (5))) (Prims.of_int (80))
         Vale_Arch_HeapTypes_s.Secret)
      (Vale_X64_Decls.va_pbool_and
         (Vale_X64_InsVector.va_codegen_success_Load128_buffer
            (Prims.of_int (6)) (Prims.of_int (4))
            (Vale_X64_Machine_s.OReg (Prims.of_int (5))) (Prims.of_int (64))
            Vale_Arch_HeapTypes_s.Secret)
         (Vale_X64_Decls.va_pbool_and
            (Vale_X64_InsVector.va_codegen_success_Load128_buffer
               (Prims.of_int (6)) (Prims.of_int (5))
               (Vale_X64_Machine_s.OReg (Prims.of_int (5)))
               (Prims.of_int (48)) Vale_Arch_HeapTypes_s.Secret)
            (Vale_X64_Decls.va_pbool_and
               (Vale_X64_InsVector.va_codegen_success_Load128_buffer
                  (Prims.of_int (6)) (Prims.of_int (6))
                  (Vale_X64_Machine_s.OReg (Prims.of_int (5)))
                  (Prims.of_int (32)) Vale_Arch_HeapTypes_s.Secret)
               (Vale_X64_Decls.va_pbool_and
                  (Vale_X64_InsVector.va_codegen_success_VPshufb
                     (Prims.of_int (7)) (Prims.of_int (7)) Prims.int_zero)
                  (Vale_X64_Decls.va_pbool_and
                     (Vale_X64_InsVector.va_codegen_success_Load128_buffer
                        (Prims.of_int (6)) (Prims.of_int (2))
                        (Vale_X64_Machine_s.OReg (Prims.of_int (5)))
                        (Prims.of_int (16)) Vale_Arch_HeapTypes_s.Secret)
                     (Vale_X64_Decls.va_pbool_and
                        (Vale_X64_InsVector.va_codegen_success_VPshufb
                           (Prims.of_int (4)) (Prims.of_int (4))
                           Prims.int_zero)
                        (Vale_X64_Decls.va_pbool_and
                           (Vale_X64_InsVector.va_codegen_success_Load128_buffer
                              (Prims.of_int (6)) (Prims.of_int (3))
                              (Vale_X64_Machine_s.OReg (Prims.of_int (5)))
                              Prims.int_zero Vale_Arch_HeapTypes_s.Secret)
                           (Vale_X64_Decls.va_pbool_and
                              (Vale_X64_InsVector.va_codegen_success_VPshufb
                                 (Prims.of_int (5)) (Prims.of_int (5))
                                 Prims.int_zero)
                              (Vale_X64_Decls.va_pbool_and
                                 (Vale_X64_InsVector.va_codegen_success_Store128_buffer
                                    (Prims.of_int (3))
                                    (Vale_X64_Machine_s.OReg
                                       (Prims.of_int (6))) (Prims.of_int (4))
                                    (Prims.of_int (48))
                                    Vale_Arch_HeapTypes_s.Secret)
                                 (Vale_X64_Decls.va_pbool_and
                                    (Vale_X64_InsVector.va_codegen_success_VPshufb
                                       (Prims.of_int (6)) (Prims.of_int (6))
                                       Prims.int_zero)
                                    (Vale_X64_Decls.va_pbool_and
                                       (Vale_X64_InsVector.va_codegen_success_Store128_buffer
                                          (Prims.of_int (3))
                                          (Vale_X64_Machine_s.OReg
                                             (Prims.of_int (6)))
                                          (Prims.of_int (5))
                                          (Prims.of_int (64))
                                          Vale_Arch_HeapTypes_s.Secret)
                                       (Vale_X64_Decls.va_pbool_and
                                          (Vale_X64_InsVector.va_codegen_success_VPshufb
                                             (Prims.of_int (2))
                                             (Prims.of_int (2))
                                             Prims.int_zero)
                                          (Vale_X64_Decls.va_pbool_and
                                             (Vale_X64_InsVector.va_codegen_success_Store128_buffer
                                                (Prims.of_int (3))
                                                (Vale_X64_Machine_s.OReg
                                                   (Prims.of_int (6)))
                                                (Prims.of_int (6))
                                                (Prims.of_int (80))
                                                Vale_Arch_HeapTypes_s.Secret)
                                             (Vale_X64_Decls.va_pbool_and
                                                (Vale_X64_InsVector.va_codegen_success_VPshufb
                                                   (Prims.of_int (3))
                                                   (Prims.of_int (3))
                                                   Prims.int_zero)
                                                (Vale_X64_Decls.va_pbool_and
                                                   (Vale_X64_InsVector.va_codegen_success_Store128_buffer
                                                      (Prims.of_int (3))
                                                      (Vale_X64_Machine_s.OReg
                                                         (Prims.of_int (6)))
                                                      (Prims.of_int (2))
                                                      (Prims.of_int (96))
                                                      Vale_Arch_HeapTypes_s.Secret)
                                                   (Vale_X64_Decls.va_pbool_and
                                                      (Vale_X64_InsVector.va_codegen_success_Store128_buffer
                                                         (Prims.of_int (3))
                                                         (Vale_X64_Machine_s.OReg
                                                            (Prims.of_int (6)))
                                                         (Prims.of_int (3))
                                                         (Prims.of_int (112))
                                                         Vale_Arch_HeapTypes_s.Secret)
                                                      (Vale_X64_Decls.va_ttrue
                                                         ())))))))))))))))))

type ('inub, 'scratchub, 'vaus0, 'vauk) va_wp_DecryptPrelude = unit

let (va_code_AES_GCM_decrypt_6mult :
  Vale_AES_AES_common_s.algorithm ->
    (Vale_X64_Decls.ins, Vale_X64_Decls.ocmp) Vale_X64_Machine_s.precode)
  =
  fun alg ->
    Vale_X64_Machine_s.Block
      [Vale_X64_Machine_s.IfElse
         ((Vale_X64_Decls.va_cmp_eq
             (Vale_X64_Machine_s.OReg (Prims.of_int (3)))
             (Vale_X64_Machine_s.OConst Prims.int_zero)),
           (Vale_X64_Machine_s.Block
              [Vale_X64_InsVector.va_code_VPshufb Prims.int_one Prims.int_one
                 Prims.int_zero;
              Vale_X64_InsVector.va_code_Store128_buffer (Prims.of_int (3))
                (Vale_X64_Machine_s.OReg (Prims.of_int (6))) Prims.int_one
                (Prims.of_int (32)) Vale_Arch_HeapTypes_s.Secret]),
           (Vale_X64_Machine_s.Block
              [Vale_X64_InsVector.va_code_Store128_buffer (Prims.of_int (3))
                 (Vale_X64_Machine_s.OReg (Prims.of_int (6)))
                 (Prims.of_int (8)) (Prims.of_int (32))
                 Vale_Arch_HeapTypes_s.Secret;
              Vale_X64_InsBasic.va_code_Add64
                (Vale_X64_Machine_s.OReg (Prims.of_int (2)))
                (Vale_X64_Machine_s.OConst (Prims.of_int (128)));
              Vale_X64_InsVector.va_code_Pextrq
                (Vale_X64_Machine_s.OReg Prims.int_one) Prims.int_one
                Prims.int_zero;
              Vale_X64_InsBasic.va_code_And64
                (Vale_X64_Machine_s.OReg Prims.int_one)
                (Vale_X64_Machine_s.OConst (Prims.of_int (255)));
              Vale_X64_InsVector.va_code_VPshufb Prims.int_one Prims.int_one
                Prims.int_zero;
              Vale_X64_InsBasic.va_code_AddLea64
                (Vale_X64_Machine_s.OReg (Prims.of_int (14)))
                (Vale_X64_Machine_s.OReg (Prims.of_int (5)))
                (Vale_X64_Machine_s.OConst (Prims.of_int (96)));
              Vale_X64_InsVector.va_code_Load128_buffer (Prims.of_int (3))
                (Prims.of_int (8))
                (Vale_X64_Machine_s.OReg (Prims.of_int (6)))
                (Prims.of_int (32)) Vale_Arch_HeapTypes_s.Secret;
              va_code_DecryptPrelude ();
              va_code_Ctr32_ghash_6_prelude alg;
              va_code_Loop6x_loop_decrypt alg;
              Vale_X64_InsVector.va_code_Store128_buffer (Prims.of_int (3))
                (Vale_X64_Machine_s.OReg (Prims.of_int (6))) Prims.int_one
                (Prims.of_int (32)) Vale_Arch_HeapTypes_s.Secret;
              Vale_X64_InsVector.va_code_Store128_buffer (Prims.of_int (6))
                (Vale_X64_Machine_s.OReg (Prims.of_int (4)))
                (Prims.of_int (9)) (Prims.of_int (-96))
                Vale_Arch_HeapTypes_s.Secret;
              Vale_X64_InsVector.va_code_Store128_buffer (Prims.of_int (6))
                (Vale_X64_Machine_s.OReg (Prims.of_int (4)))
                (Prims.of_int (10)) (Prims.of_int (-80))
                Vale_Arch_HeapTypes_s.Secret;
              Vale_X64_InsVector.va_code_Store128_buffer (Prims.of_int (6))
                (Vale_X64_Machine_s.OReg (Prims.of_int (4)))
                (Prims.of_int (11)) (Prims.of_int (-64))
                Vale_Arch_HeapTypes_s.Secret;
              Vale_X64_InsVector.va_code_Store128_buffer (Prims.of_int (6))
                (Vale_X64_Machine_s.OReg (Prims.of_int (4)))
                (Prims.of_int (12)) (Prims.of_int (-48))
                Vale_Arch_HeapTypes_s.Secret;
              Vale_X64_InsVector.va_code_Store128_buffer (Prims.of_int (6))
                (Vale_X64_Machine_s.OReg (Prims.of_int (4)))
                (Prims.of_int (13)) (Prims.of_int (-32))
                Vale_Arch_HeapTypes_s.Secret;
              Vale_X64_InsVector.va_code_Store128_buffer (Prims.of_int (6))
                (Vale_X64_Machine_s.OReg (Prims.of_int (4)))
                (Prims.of_int (14)) (Prims.of_int (-16))
                Vale_Arch_HeapTypes_s.Secret;
              Vale_X64_Machine_s.Block [];
              Vale_X64_Machine_s.Block [];
              Vale_X64_InsBasic.va_code_Sub64
                (Vale_X64_Machine_s.OReg (Prims.of_int (2)))
                (Vale_X64_Machine_s.OConst (Prims.of_int (128)))]))]
let (va_codegen_success_AES_GCM_decrypt_6mult :
  Vale_AES_AES_common_s.algorithm -> Vale_X64_Decls.va_pbool) =
  fun alg ->
    Vale_X64_Decls.va_pbool_and
      (Vale_X64_Decls.va_pbool_and
         (Vale_X64_InsVector.va_codegen_success_VPshufb Prims.int_one
            Prims.int_one Prims.int_zero)
         (Vale_X64_Decls.va_pbool_and
            (Vale_X64_InsVector.va_codegen_success_Store128_buffer
               (Prims.of_int (3))
               (Vale_X64_Machine_s.OReg (Prims.of_int (6))) Prims.int_one
               (Prims.of_int (32)) Vale_Arch_HeapTypes_s.Secret)
            (Vale_X64_Decls.va_pbool_and
               (Vale_X64_InsVector.va_codegen_success_Store128_buffer
                  (Prims.of_int (3))
                  (Vale_X64_Machine_s.OReg (Prims.of_int (6)))
                  (Prims.of_int (8)) (Prims.of_int (32))
                  Vale_Arch_HeapTypes_s.Secret)
               (Vale_X64_Decls.va_pbool_and
                  (Vale_X64_InsBasic.va_codegen_success_Add64
                     (Vale_X64_Machine_s.OReg (Prims.of_int (2)))
                     (Vale_X64_Machine_s.OConst (Prims.of_int (128))))
                  (Vale_X64_Decls.va_pbool_and
                     (Vale_X64_InsVector.va_codegen_success_Pextrq
                        (Vale_X64_Machine_s.OReg Prims.int_one) Prims.int_one
                        Prims.int_zero)
                     (Vale_X64_Decls.va_pbool_and
                        (Vale_X64_InsBasic.va_codegen_success_And64
                           (Vale_X64_Machine_s.OReg Prims.int_one)
                           (Vale_X64_Machine_s.OConst (Prims.of_int (255))))
                        (Vale_X64_Decls.va_pbool_and
                           (Vale_X64_InsVector.va_codegen_success_VPshufb
                              Prims.int_one Prims.int_one Prims.int_zero)
                           (Vale_X64_Decls.va_pbool_and
                              (Vale_X64_InsBasic.va_codegen_success_AddLea64
                                 (Vale_X64_Machine_s.OReg (Prims.of_int (14)))
                                 (Vale_X64_Machine_s.OReg (Prims.of_int (5)))
                                 (Vale_X64_Machine_s.OConst
                                    (Prims.of_int (96))))
                              (Vale_X64_Decls.va_pbool_and
                                 (Vale_X64_InsVector.va_codegen_success_Load128_buffer
                                    (Prims.of_int (3)) (Prims.of_int (8))
                                    (Vale_X64_Machine_s.OReg
                                       (Prims.of_int (6)))
                                    (Prims.of_int (32))
                                    Vale_Arch_HeapTypes_s.Secret)
                                 (Vale_X64_Decls.va_pbool_and
                                    (va_codegen_success_DecryptPrelude ())
                                    (Vale_X64_Decls.va_pbool_and
                                       (va_codegen_success_Ctr32_ghash_6_prelude
                                          alg)
                                       (Vale_X64_Decls.va_pbool_and
                                          (va_codegen_success_Loop6x_loop_decrypt
                                             alg)
                                          (Vale_X64_Decls.va_pbool_and
                                             (Vale_X64_InsVector.va_codegen_success_Store128_buffer
                                                (Prims.of_int (3))
                                                (Vale_X64_Machine_s.OReg
                                                   (Prims.of_int (6)))
                                                Prims.int_one
                                                (Prims.of_int (32))
                                                Vale_Arch_HeapTypes_s.Secret)
                                             (Vale_X64_Decls.va_pbool_and
                                                (Vale_X64_InsVector.va_codegen_success_Store128_buffer
                                                   (Prims.of_int (6))
                                                   (Vale_X64_Machine_s.OReg
                                                      (Prims.of_int (4)))
                                                   (Prims.of_int (9))
                                                   (Prims.of_int (-96))
                                                   Vale_Arch_HeapTypes_s.Secret)
                                                (Vale_X64_Decls.va_pbool_and
                                                   (Vale_X64_InsVector.va_codegen_success_Store128_buffer
                                                      (Prims.of_int (6))
                                                      (Vale_X64_Machine_s.OReg
                                                         (Prims.of_int (4)))
                                                      (Prims.of_int (10))
                                                      (Prims.of_int (-80))
                                                      Vale_Arch_HeapTypes_s.Secret)
                                                   (Vale_X64_Decls.va_pbool_and
                                                      (Vale_X64_InsVector.va_codegen_success_Store128_buffer
                                                         (Prims.of_int (6))
                                                         (Vale_X64_Machine_s.OReg
                                                            (Prims.of_int (4)))
                                                         (Prims.of_int (11))
                                                         (Prims.of_int (-64))
                                                         Vale_Arch_HeapTypes_s.Secret)
                                                      (Vale_X64_Decls.va_pbool_and
                                                         (Vale_X64_InsVector.va_codegen_success_Store128_buffer
                                                            (Prims.of_int (6))
                                                            (Vale_X64_Machine_s.OReg
                                                               (Prims.of_int (4)))
                                                            (Prims.of_int (12))
                                                            (Prims.of_int (-48))
                                                            Vale_Arch_HeapTypes_s.Secret)
                                                         (Vale_X64_Decls.va_pbool_and
                                                            (Vale_X64_InsVector.va_codegen_success_Store128_buffer
                                                               (Prims.of_int (6))
                                                               (Vale_X64_Machine_s.OReg
                                                                  (Prims.of_int (4)))
                                                               (Prims.of_int (13))
                                                               (Prims.of_int (-32))
                                                               Vale_Arch_HeapTypes_s.Secret)
                                                            (Vale_X64_Decls.va_pbool_and
                                                               (Vale_X64_InsVector.va_codegen_success_Store128_buffer
                                                                  (Prims.of_int (6))
                                                                  (Vale_X64_Machine_s.OReg
                                                                    (Prims.of_int (4)))
                                                                  (Prims.of_int (14))
                                                                  (Prims.of_int (-16))
                                                                  Vale_Arch_HeapTypes_s.Secret)
                                                               (Vale_X64_InsBasic.va_codegen_success_Sub64
                                                                  (Vale_X64_Machine_s.OReg
                                                                    (Prims.of_int (2)))
                                                                  (Vale_X64_Machine_s.OConst
                                                                    (Prims.of_int (128)))))))))))))))))))))))
      (Vale_X64_Decls.va_ttrue ())

type ('alg, 'huLE, 'ivub, 'inub, 'outub, 'scratchub, 'keyuwords, 'roundukeys,
  'keysub, 'hkeysub, 'vaus0, 'vauk) va_wp_AES_GCM_decrypt_6mult = unit
