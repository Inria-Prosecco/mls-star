open Prims
let (va_code_Callee_save_registers :
  Prims.bool ->
    (Vale_X64_Decls.ins, Vale_X64_Decls.ocmp) Vale_X64_Machine_s.precode)
  =
  fun win ->
    Vale_X64_Machine_s.Block
      [if win
       then
         Vale_X64_Machine_s.Block
           [Vale_X64_InsStack.va_code_PushXmm (Prims.of_int (15))
              (Vale_X64_Machine_s.OReg Prims.int_zero);
           Vale_X64_InsStack.va_code_PushXmm (Prims.of_int (14))
             (Vale_X64_Machine_s.OReg Prims.int_zero);
           Vale_X64_InsStack.va_code_PushXmm (Prims.of_int (13))
             (Vale_X64_Machine_s.OReg Prims.int_zero);
           Vale_X64_InsStack.va_code_PushXmm (Prims.of_int (12))
             (Vale_X64_Machine_s.OReg Prims.int_zero);
           Vale_X64_InsStack.va_code_PushXmm (Prims.of_int (11))
             (Vale_X64_Machine_s.OReg Prims.int_zero);
           Vale_X64_InsStack.va_code_PushXmm (Prims.of_int (10))
             (Vale_X64_Machine_s.OReg Prims.int_zero);
           Vale_X64_InsStack.va_code_PushXmm (Prims.of_int (9))
             (Vale_X64_Machine_s.OReg Prims.int_zero);
           Vale_X64_InsStack.va_code_PushXmm (Prims.of_int (8))
             (Vale_X64_Machine_s.OReg Prims.int_zero);
           Vale_X64_InsStack.va_code_PushXmm (Prims.of_int (7))
             (Vale_X64_Machine_s.OReg Prims.int_zero);
           Vale_X64_InsStack.va_code_PushXmm (Prims.of_int (6))
             (Vale_X64_Machine_s.OReg Prims.int_zero)]
       else Vale_X64_Machine_s.Block [];
      Vale_X64_InsStack.va_code_Push
        (Vale_X64_Machine_s.OReg (Prims.of_int (15)));
      Vale_X64_InsStack.va_code_Push
        (Vale_X64_Machine_s.OReg (Prims.of_int (14)));
      Vale_X64_InsStack.va_code_Push
        (Vale_X64_Machine_s.OReg (Prims.of_int (13)));
      Vale_X64_InsStack.va_code_Push
        (Vale_X64_Machine_s.OReg (Prims.of_int (12)));
      Vale_X64_InsStack.va_code_Push
        (Vale_X64_Machine_s.OReg (Prims.of_int (4)));
      Vale_X64_InsStack.va_code_Push
        (Vale_X64_Machine_s.OReg (Prims.of_int (5)));
      Vale_X64_InsStack.va_code_Push
        (Vale_X64_Machine_s.OReg (Prims.of_int (6)));
      Vale_X64_InsStack.va_code_Push (Vale_X64_Machine_s.OReg Prims.int_one)]
let (va_codegen_success_Callee_save_registers :
  Prims.bool -> Vale_X64_Decls.va_pbool) =
  fun win ->
    Vale_X64_Decls.va_pbool_and
      (if win
       then
         Vale_X64_Decls.va_pbool_and
           (Vale_X64_InsStack.va_codegen_success_PushXmm (Prims.of_int (15))
              (Vale_X64_Machine_s.OReg Prims.int_zero))
           (Vale_X64_Decls.va_pbool_and
              (Vale_X64_InsStack.va_codegen_success_PushXmm
                 (Prims.of_int (14)) (Vale_X64_Machine_s.OReg Prims.int_zero))
              (Vale_X64_Decls.va_pbool_and
                 (Vale_X64_InsStack.va_codegen_success_PushXmm
                    (Prims.of_int (13))
                    (Vale_X64_Machine_s.OReg Prims.int_zero))
                 (Vale_X64_Decls.va_pbool_and
                    (Vale_X64_InsStack.va_codegen_success_PushXmm
                       (Prims.of_int (12))
                       (Vale_X64_Machine_s.OReg Prims.int_zero))
                    (Vale_X64_Decls.va_pbool_and
                       (Vale_X64_InsStack.va_codegen_success_PushXmm
                          (Prims.of_int (11))
                          (Vale_X64_Machine_s.OReg Prims.int_zero))
                       (Vale_X64_Decls.va_pbool_and
                          (Vale_X64_InsStack.va_codegen_success_PushXmm
                             (Prims.of_int (10))
                             (Vale_X64_Machine_s.OReg Prims.int_zero))
                          (Vale_X64_Decls.va_pbool_and
                             (Vale_X64_InsStack.va_codegen_success_PushXmm
                                (Prims.of_int (9))
                                (Vale_X64_Machine_s.OReg Prims.int_zero))
                             (Vale_X64_Decls.va_pbool_and
                                (Vale_X64_InsStack.va_codegen_success_PushXmm
                                   (Prims.of_int (8))
                                   (Vale_X64_Machine_s.OReg Prims.int_zero))
                                (Vale_X64_Decls.va_pbool_and
                                   (Vale_X64_InsStack.va_codegen_success_PushXmm
                                      (Prims.of_int (7))
                                      (Vale_X64_Machine_s.OReg Prims.int_zero))
                                   (Vale_X64_Decls.va_pbool_and
                                      (Vale_X64_InsStack.va_codegen_success_PushXmm
                                         (Prims.of_int (6))
                                         (Vale_X64_Machine_s.OReg
                                            Prims.int_zero))
                                      (Vale_X64_Decls.va_ttrue ()))))))))))
       else Vale_X64_Decls.va_ttrue ())
      (Vale_X64_Decls.va_pbool_and
         (Vale_X64_InsStack.va_codegen_success_Push
            (Vale_X64_Machine_s.OReg (Prims.of_int (15))))
         (Vale_X64_Decls.va_pbool_and
            (Vale_X64_InsStack.va_codegen_success_Push
               (Vale_X64_Machine_s.OReg (Prims.of_int (14))))
            (Vale_X64_Decls.va_pbool_and
               (Vale_X64_InsStack.va_codegen_success_Push
                  (Vale_X64_Machine_s.OReg (Prims.of_int (13))))
               (Vale_X64_Decls.va_pbool_and
                  (Vale_X64_InsStack.va_codegen_success_Push
                     (Vale_X64_Machine_s.OReg (Prims.of_int (12))))
                  (Vale_X64_Decls.va_pbool_and
                     (Vale_X64_InsStack.va_codegen_success_Push
                        (Vale_X64_Machine_s.OReg (Prims.of_int (4))))
                     (Vale_X64_Decls.va_pbool_and
                        (Vale_X64_InsStack.va_codegen_success_Push
                           (Vale_X64_Machine_s.OReg (Prims.of_int (5))))
                        (Vale_X64_Decls.va_pbool_and
                           (Vale_X64_InsStack.va_codegen_success_Push
                              (Vale_X64_Machine_s.OReg (Prims.of_int (6))))
                           (Vale_X64_Decls.va_pbool_and
                              (Vale_X64_InsStack.va_codegen_success_Push
                                 (Vale_X64_Machine_s.OReg Prims.int_one))
                              (Vale_X64_Decls.va_ttrue ())))))))))

type ('win, 'vaus0, 'vauk) va_wp_Callee_save_registers = unit

let (va_code_Callee_restore_registers :
  Prims.bool ->
    (Vale_X64_Decls.ins, Vale_X64_Decls.ocmp) Vale_X64_Machine_s.precode)
  =
  fun win ->
    Vale_X64_Machine_s.Block
      [Vale_X64_InsStack.va_code_Pop (Vale_X64_Machine_s.OReg Prims.int_one);
      Vale_X64_InsStack.va_code_Pop
        (Vale_X64_Machine_s.OReg (Prims.of_int (6)));
      Vale_X64_InsStack.va_code_Pop
        (Vale_X64_Machine_s.OReg (Prims.of_int (5)));
      Vale_X64_InsStack.va_code_Pop
        (Vale_X64_Machine_s.OReg (Prims.of_int (4)));
      Vale_X64_InsStack.va_code_Pop
        (Vale_X64_Machine_s.OReg (Prims.of_int (12)));
      Vale_X64_InsStack.va_code_Pop
        (Vale_X64_Machine_s.OReg (Prims.of_int (13)));
      Vale_X64_InsStack.va_code_Pop
        (Vale_X64_Machine_s.OReg (Prims.of_int (14)));
      Vale_X64_InsStack.va_code_Pop
        (Vale_X64_Machine_s.OReg (Prims.of_int (15)));
      if win
      then
        Vale_X64_Machine_s.Block
          [Vale_X64_InsStack.va_code_PopXmm (Prims.of_int (6))
             (Vale_X64_Machine_s.OReg Prims.int_zero);
          Vale_X64_InsStack.va_code_PopXmm (Prims.of_int (7))
            (Vale_X64_Machine_s.OReg Prims.int_zero);
          Vale_X64_InsStack.va_code_PopXmm (Prims.of_int (8))
            (Vale_X64_Machine_s.OReg Prims.int_zero);
          Vale_X64_InsStack.va_code_PopXmm (Prims.of_int (9))
            (Vale_X64_Machine_s.OReg Prims.int_zero);
          Vale_X64_InsStack.va_code_PopXmm (Prims.of_int (10))
            (Vale_X64_Machine_s.OReg Prims.int_zero);
          Vale_X64_InsStack.va_code_PopXmm (Prims.of_int (11))
            (Vale_X64_Machine_s.OReg Prims.int_zero);
          Vale_X64_InsStack.va_code_PopXmm (Prims.of_int (12))
            (Vale_X64_Machine_s.OReg Prims.int_zero);
          Vale_X64_InsStack.va_code_PopXmm (Prims.of_int (13))
            (Vale_X64_Machine_s.OReg Prims.int_zero);
          Vale_X64_InsStack.va_code_PopXmm (Prims.of_int (14))
            (Vale_X64_Machine_s.OReg Prims.int_zero);
          Vale_X64_InsStack.va_code_PopXmm (Prims.of_int (15))
            (Vale_X64_Machine_s.OReg Prims.int_zero)]
      else Vale_X64_Machine_s.Block []]
let (va_codegen_success_Callee_restore_registers :
  Prims.bool -> Vale_X64_Decls.va_pbool) =
  fun win ->
    Vale_X64_Decls.va_pbool_and
      (Vale_X64_InsStack.va_codegen_success_Pop
         (Vale_X64_Machine_s.OReg Prims.int_one))
      (Vale_X64_Decls.va_pbool_and
         (Vale_X64_InsStack.va_codegen_success_Pop
            (Vale_X64_Machine_s.OReg (Prims.of_int (6))))
         (Vale_X64_Decls.va_pbool_and
            (Vale_X64_InsStack.va_codegen_success_Pop
               (Vale_X64_Machine_s.OReg (Prims.of_int (5))))
            (Vale_X64_Decls.va_pbool_and
               (Vale_X64_InsStack.va_codegen_success_Pop
                  (Vale_X64_Machine_s.OReg (Prims.of_int (4))))
               (Vale_X64_Decls.va_pbool_and
                  (Vale_X64_InsStack.va_codegen_success_Pop
                     (Vale_X64_Machine_s.OReg (Prims.of_int (12))))
                  (Vale_X64_Decls.va_pbool_and
                     (Vale_X64_InsStack.va_codegen_success_Pop
                        (Vale_X64_Machine_s.OReg (Prims.of_int (13))))
                     (Vale_X64_Decls.va_pbool_and
                        (Vale_X64_InsStack.va_codegen_success_Pop
                           (Vale_X64_Machine_s.OReg (Prims.of_int (14))))
                        (Vale_X64_Decls.va_pbool_and
                           (Vale_X64_InsStack.va_codegen_success_Pop
                              (Vale_X64_Machine_s.OReg (Prims.of_int (15))))
                           (Vale_X64_Decls.va_pbool_and
                              (if win
                               then
                                 Vale_X64_Decls.va_pbool_and
                                   (Vale_X64_InsStack.va_codegen_success_PopXmm
                                      (Prims.of_int (6))
                                      (Vale_X64_Machine_s.OReg Prims.int_zero))
                                   (Vale_X64_Decls.va_pbool_and
                                      (Vale_X64_InsStack.va_codegen_success_PopXmm
                                         (Prims.of_int (7))
                                         (Vale_X64_Machine_s.OReg
                                            Prims.int_zero))
                                      (Vale_X64_Decls.va_pbool_and
                                         (Vale_X64_InsStack.va_codegen_success_PopXmm
                                            (Prims.of_int (8))
                                            (Vale_X64_Machine_s.OReg
                                               Prims.int_zero))
                                         (Vale_X64_Decls.va_pbool_and
                                            (Vale_X64_InsStack.va_codegen_success_PopXmm
                                               (Prims.of_int (9))
                                               (Vale_X64_Machine_s.OReg
                                                  Prims.int_zero))
                                            (Vale_X64_Decls.va_pbool_and
                                               (Vale_X64_InsStack.va_codegen_success_PopXmm
                                                  (Prims.of_int (10))
                                                  (Vale_X64_Machine_s.OReg
                                                     Prims.int_zero))
                                               (Vale_X64_Decls.va_pbool_and
                                                  (Vale_X64_InsStack.va_codegen_success_PopXmm
                                                     (Prims.of_int (11))
                                                     (Vale_X64_Machine_s.OReg
                                                        Prims.int_zero))
                                                  (Vale_X64_Decls.va_pbool_and
                                                     (Vale_X64_InsStack.va_codegen_success_PopXmm
                                                        (Prims.of_int (12))
                                                        (Vale_X64_Machine_s.OReg
                                                           Prims.int_zero))
                                                     (Vale_X64_Decls.va_pbool_and
                                                        (Vale_X64_InsStack.va_codegen_success_PopXmm
                                                           (Prims.of_int (13))
                                                           (Vale_X64_Machine_s.OReg
                                                              Prims.int_zero))
                                                        (Vale_X64_Decls.va_pbool_and
                                                           (Vale_X64_InsStack.va_codegen_success_PopXmm
                                                              (Prims.of_int (14))
                                                              (Vale_X64_Machine_s.OReg
                                                                 Prims.int_zero))
                                                           (Vale_X64_Decls.va_pbool_and
                                                              (Vale_X64_InsStack.va_codegen_success_PopXmm
                                                                 (Prims.of_int (15))
                                                                 (Vale_X64_Machine_s.OReg
                                                                    Prims.int_zero))
                                                              (Vale_X64_Decls.va_ttrue
                                                                 ()))))))))))
                               else Vale_X64_Decls.va_ttrue ())
                              (Vale_X64_Decls.va_ttrue ())))))))))

type ('win, 'olduxmm6, 'olduxmm7, 'olduxmm8, 'olduxmm9, 'olduxmm10,
  'olduxmm11, 'olduxmm12, 'olduxmm13, 'olduxmm14, 'olduxmm15, 'vaus0,
  'vauk) va_wp_Callee_restore_registers = unit
