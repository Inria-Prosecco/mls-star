open Prims
let (va_code_Test :
  Prims.bool ->
    (Vale_X64_Decls.ins, Vale_X64_Decls.ocmp) Vale_X64_Machine_s.precode)
  =
  fun win ->
    Vale_X64_Machine_s.Block
      [Vale_X64_InsMem.va_code_CreateHeaplets ();
      Vale_X64_InsBasic.va_code_Mov64
        (Vale_X64_Machine_s.OReg Prims.int_zero)
        (Vale_X64_Machine_s.OReg Prims.int_one);
      Vale_X64_InsMem.va_code_DestroyHeaplets ()]
let (va_codegen_success_Test : Prims.bool -> Vale_X64_Decls.va_pbool) =
  fun win ->
    Vale_X64_Decls.va_pbool_and
      (Vale_X64_InsMem.va_codegen_success_CreateHeaplets ())
      (Vale_X64_Decls.va_pbool_and
         (Vale_X64_InsBasic.va_codegen_success_Mov64
            (Vale_X64_Machine_s.OReg Prims.int_zero)
            (Vale_X64_Machine_s.OReg Prims.int_one))
         (Vale_X64_Decls.va_pbool_and
            (Vale_X64_InsMem.va_codegen_success_DestroyHeaplets ())
            (Vale_X64_Decls.va_ttrue ())))
type ('vaub0, 'vaus0, 'win, 'arg0, 'arg1, 'arg2, 'arg3, 'arg4, 'arg5, 
  'arg6, 'arg7) va_req_Test = unit
type ('vaub0, 'vaus0, 'win, 'arg0, 'arg1, 'arg2, 'arg3, 'arg4, 'arg5, 
  'arg6, 'arg7, 'vausM, 'vaufM) va_ens_Test = unit

type ('win, 'arg0, 'arg1, 'arg2, 'arg3, 'arg4, 'arg5, 'arg6, 'arg7, 'vaus0,
  'vauk) va_wp_Test = unit
