open Prims
let (va_code_KeyExpansionStdcall :
  Prims.bool ->
    Vale_AES_AES_common_s.algorithm ->
      (Vale_X64_Decls.ins, Vale_X64_Decls.ocmp) Vale_X64_Machine_s.precode)
  =
  fun win ->
    fun alg ->
      Vale_X64_Machine_s.Block
        [Vale_X64_InsMem.va_code_CreateHeaplets ();
        if alg = Vale_AES_AES_common_s.AES_128
        then
          Vale_X64_Machine_s.Block
            [Vale_AES_X64_AES128.va_code_KeyExpansion128Stdcall win]
        else
          Vale_X64_Machine_s.Block
            [Vale_AES_X64_AES256.va_code_KeyExpansion256Stdcall win];
        Vale_X64_InsMem.va_code_DestroyHeaplets ()]
let (va_codegen_success_KeyExpansionStdcall :
  Prims.bool -> Vale_AES_AES_common_s.algorithm -> Vale_X64_Decls.va_pbool) =
  fun win ->
    fun alg ->
      Vale_X64_Decls.va_pbool_and
        (Vale_X64_InsMem.va_codegen_success_CreateHeaplets ())
        (Vale_X64_Decls.va_pbool_and
           (if alg = Vale_AES_AES_common_s.AES_128
            then
              Vale_X64_Decls.va_pbool_and
                (Vale_AES_X64_AES128.va_codegen_success_KeyExpansion128Stdcall
                   win) (Vale_X64_Decls.va_ttrue ())
            else
              Vale_X64_Decls.va_pbool_and
                (Vale_AES_X64_AES256.va_codegen_success_KeyExpansion256Stdcall
                   win) (Vale_X64_Decls.va_ttrue ()))
           (Vale_X64_Decls.va_pbool_and
              (Vale_X64_InsMem.va_codegen_success_DestroyHeaplets ())
              (Vale_X64_Decls.va_ttrue ())))
type ('vaub0, 'vaus0, 'win, 'alg, 'inputukeyub,
  'outputukeyuexpansionub) va_req_KeyExpansionStdcall = unit
type ('vaub0, 'vaus0, 'win, 'alg, 'inputukeyub, 'outputukeyuexpansionub,
  'vausM, 'vaufM) va_ens_KeyExpansionStdcall = unit

type ('win, 'alg, 'inputukeyub, 'outputukeyuexpansionub, 'vaus0,
  'vauk) va_wp_KeyExpansionStdcall = unit

let (va_code_AESEncryptBlock :
  Vale_AES_AES_common_s.algorithm ->
    (Vale_X64_Decls.ins, Vale_X64_Decls.ocmp) Vale_X64_Machine_s.precode)
  =
  fun alg ->
    Vale_X64_Machine_s.Block
      [if alg = Vale_AES_AES_common_s.AES_128
       then
         Vale_X64_Machine_s.Block
           [Vale_AES_X64_AES128.va_code_AES128EncryptBlock ()]
       else
         Vale_X64_Machine_s.Block
           [Vale_AES_X64_AES256.va_code_AES256EncryptBlock ()]]
let (va_codegen_success_AESEncryptBlock :
  Vale_AES_AES_common_s.algorithm -> Vale_X64_Decls.va_pbool) =
  fun alg ->
    Vale_X64_Decls.va_pbool_and
      (if alg = Vale_AES_AES_common_s.AES_128
       then
         Vale_X64_Decls.va_pbool_and
           (Vale_AES_X64_AES128.va_codegen_success_AES128EncryptBlock ())
           (Vale_X64_Decls.va_ttrue ())
       else
         Vale_X64_Decls.va_pbool_and
           (Vale_AES_X64_AES256.va_codegen_success_AES256EncryptBlock ())
           (Vale_X64_Decls.va_ttrue ())) (Vale_X64_Decls.va_ttrue ())

type ('alg, 'input, 'key, 'roundukeys, 'keysubuffer, 'vaus0,
  'vauk) va_wp_AESEncryptBlock = unit
