open Prims
let (va_code_Stack_lemma :
  unit ->
    (Vale_X64_Decls.ins, Vale_X64_Decls.ocmp) Vale_X64_Machine_s.precode)
  = fun uu___ -> Vale_X64_Machine_s.Block []
let (va_codegen_success_Stack_lemma : unit -> Vale_X64_Decls.va_pbool) =
  fun uu___ -> Vale_X64_Decls.va_ttrue ()
type ('base, 'offset, 't, 'vaus0, 'vauk) va_wp_Stack_lemma = unit

let (va_code_Pop :
  Vale_X64_Machine_s.operand64 ->
    (Vale_X64_Decls.ins, Vale_X64_Decls.ocmp) Vale_X64_Machine_s.precode)
  =
  fun dst ->
    Vale_X64_Machine_s.Ins
      (Vale_X64_Bytes_Code_s.Pop (dst, Vale_Arch_HeapTypes_s.Public))
let (va_codegen_success_Pop :
  Vale_X64_Machine_s.operand64 -> Vale_X64_Decls.va_pbool) =
  fun dst -> Vale_X64_Decls.va_ttrue ()
type ('dst, 'vaus0, 'vauk) va_wp_Pop = unit

let (va_code_Push :
  Vale_X64_Decls.va_operand_reg_opr64 ->
    (Vale_X64_Decls.ins, Vale_X64_Decls.ocmp) Vale_X64_Machine_s.precode)
  =
  fun src ->
    Vale_X64_Machine_s.Ins
      (Vale_X64_Bytes_Code_s.Push (src, Vale_Arch_HeapTypes_s.Public))
let (va_codegen_success_Push :
  Vale_X64_Decls.va_operand_reg_opr64 -> Vale_X64_Decls.va_pbool) =
  fun src -> Vale_X64_Decls.va_ttrue ()
type ('src, 'vaus0, 'vauk) va_wp_Push = unit

let (va_code_Pop_Secret :
  Vale_X64_Machine_s.operand64 ->
    (Vale_X64_Decls.ins, Vale_X64_Decls.ocmp) Vale_X64_Machine_s.precode)
  =
  fun dst ->
    Vale_X64_Machine_s.Ins
      (Vale_X64_Bytes_Code_s.Pop (dst, Vale_Arch_HeapTypes_s.Secret))
let (va_codegen_success_Pop_Secret :
  Vale_X64_Machine_s.operand64 -> Vale_X64_Decls.va_pbool) =
  fun dst -> Vale_X64_Decls.va_ttrue ()
type ('dst, 'vaus0, 'vauk) va_wp_Pop_Secret = unit

let (va_code_Push_Secret :
  Vale_X64_Decls.va_operand_reg_opr64 ->
    (Vale_X64_Decls.ins, Vale_X64_Decls.ocmp) Vale_X64_Machine_s.precode)
  =
  fun src ->
    Vale_X64_Machine_s.Ins
      (Vale_X64_Bytes_Code_s.Push (src, Vale_Arch_HeapTypes_s.Secret))
let (va_codegen_success_Push_Secret :
  Vale_X64_Decls.va_operand_reg_opr64 -> Vale_X64_Decls.va_pbool) =
  fun src -> Vale_X64_Decls.va_ttrue ()
type ('src, 'vaus0, 'vauk) va_wp_Push_Secret = unit

let (va_code_Load64_stack :
  Vale_X64_Machine_s.operand64 ->
    Vale_X64_Decls.va_operand_reg_opr64 ->
      Prims.int ->
        (Vale_X64_Decls.ins, Vale_X64_Decls.ocmp) Vale_X64_Machine_s.precode)
  =
  fun dst ->
    fun src ->
      fun offset ->
        Vale_X64_Taint_Semantics.mk_ins
          (Obj.magic
             ((fun uu___1 ->
                 fun uu___ ->
                   (Obj.magic
                      (Vale_X64_InsLemmas.make_instr_annotate
                         [(Vale_X64_Instruction_s.Out,
                            (Vale_X64_Instruction_s.IOpEx
                               Vale_X64_Instruction_s.IOp64))]
                         [Vale_X64_Instruction_s.IOpEx
                            Vale_X64_Instruction_s.IOp64]
                         Vale_X64_Instruction_s.PreserveFlags
                         Vale_X64_Instructions_s.ins_Mov64
                         (Vale_X64_Machine_Semantics_s.AnnotateMov64 ())))
                     uu___1 uu___) (Obj.magic dst)
                (Obj.magic
                   (Vale_X64_Machine_s.OStack
                      ((Vale_X64_Machine_s.MReg
                          ((Vale_X64_Machine_s.Reg
                              (Prims.int_zero,
                                (Vale_X64_Machine_s.__proj__OReg__item__r src))),
                            offset)), Vale_Arch_HeapTypes_s.Public)))))
let (va_codegen_success_Load64_stack :
  Vale_X64_Machine_s.operand64 ->
    Vale_X64_Decls.va_operand_reg_opr64 ->
      Prims.int -> Vale_X64_Decls.va_pbool)
  = fun dst -> fun src -> fun offset -> Vale_X64_Decls.va_ttrue ()
type ('dst, 'src, 'offset, 'vaus0, 'vauk) va_wp_Load64_stack = unit

let (va_code_PushXmm :
  Vale_X64_Machine_s.reg_xmm ->
    Vale_X64_Decls.va_operand_reg_opr64 ->
      (Vale_X64_Decls.ins, Vale_X64_Decls.ocmp) Vale_X64_Machine_s.precode)
  =
  fun src ->
    fun tmp ->
      Vale_X64_Machine_s.Block
        [Vale_X64_InsVector.va_code_Pextrq tmp src Prims.int_zero;
        va_code_Push tmp;
        Vale_X64_InsVector.va_code_Pextrq tmp src Prims.int_one;
        va_code_Push tmp]
let (va_codegen_success_PushXmm :
  Vale_X64_Machine_s.reg_xmm ->
    Vale_X64_Decls.va_operand_reg_opr64 -> Vale_X64_Decls.va_pbool)
  =
  fun src ->
    fun tmp ->
      Vale_X64_Decls.va_pbool_and
        (Vale_X64_InsVector.va_codegen_success_Pextrq tmp src Prims.int_zero)
        (Vale_X64_Decls.va_pbool_and (va_codegen_success_Push tmp)
           (Vale_X64_Decls.va_pbool_and
              (Vale_X64_InsVector.va_codegen_success_Pextrq tmp src
                 Prims.int_one)
              (Vale_X64_Decls.va_pbool_and (va_codegen_success_Push tmp)
                 (Vale_X64_Decls.va_ttrue ()))))
type ('src, 'tmp, 'vaus0, 'vauk) va_wp_PushXmm = unit

let (va_code_PopXmm :
  Vale_X64_Machine_s.reg_xmm ->
    Vale_X64_Decls.va_operand_reg_opr64 ->
      (Vale_X64_Decls.ins, Vale_X64_Decls.ocmp) Vale_X64_Machine_s.precode)
  =
  fun dst ->
    fun tmp ->
      Vale_X64_Machine_s.Block
        [va_code_Pop tmp;
        Vale_X64_InsVector.va_code_Pinsrq dst tmp Prims.int_one;
        va_code_Pop tmp;
        Vale_X64_InsVector.va_code_Pinsrq dst tmp Prims.int_zero]
let (va_codegen_success_PopXmm :
  Vale_X64_Machine_s.reg_xmm ->
    Vale_X64_Decls.va_operand_reg_opr64 -> Vale_X64_Decls.va_pbool)
  =
  fun dst ->
    fun tmp ->
      Vale_X64_Decls.va_pbool_and (va_codegen_success_Pop tmp)
        (Vale_X64_Decls.va_pbool_and
           (Vale_X64_InsVector.va_codegen_success_Pinsrq dst tmp
              Prims.int_one)
           (Vale_X64_Decls.va_pbool_and (va_codegen_success_Pop tmp)
              (Vale_X64_Decls.va_pbool_and
                 (Vale_X64_InsVector.va_codegen_success_Pinsrq dst tmp
                    Prims.int_zero) (Vale_X64_Decls.va_ttrue ()))))
type ('dst, 'tmp, 'expecteduxmm, 'vaus0, 'vauk) va_wp_PopXmm = unit

let (va_code_PushXmm_Secret :
  Vale_X64_Machine_s.reg_xmm ->
    Vale_X64_Decls.va_operand_reg_opr64 ->
      (Vale_X64_Decls.ins, Vale_X64_Decls.ocmp) Vale_X64_Machine_s.precode)
  =
  fun src ->
    fun tmp ->
      Vale_X64_Machine_s.Block
        [Vale_X64_InsVector.va_code_Pextrq tmp src Prims.int_zero;
        va_code_Push_Secret tmp;
        Vale_X64_InsVector.va_code_Pextrq tmp src Prims.int_one;
        va_code_Push_Secret tmp]
let (va_codegen_success_PushXmm_Secret :
  Vale_X64_Machine_s.reg_xmm ->
    Vale_X64_Decls.va_operand_reg_opr64 -> Vale_X64_Decls.va_pbool)
  =
  fun src ->
    fun tmp ->
      Vale_X64_Decls.va_pbool_and
        (Vale_X64_InsVector.va_codegen_success_Pextrq tmp src Prims.int_zero)
        (Vale_X64_Decls.va_pbool_and (va_codegen_success_Push_Secret tmp)
           (Vale_X64_Decls.va_pbool_and
              (Vale_X64_InsVector.va_codegen_success_Pextrq tmp src
                 Prims.int_one)
              (Vale_X64_Decls.va_pbool_and
                 (va_codegen_success_Push_Secret tmp)
                 (Vale_X64_Decls.va_ttrue ()))))
type ('src, 'tmp, 'vaus0, 'vauk) va_wp_PushXmm_Secret = unit

let (va_code_PopXmm_Secret :
  Vale_X64_Machine_s.reg_xmm ->
    Vale_X64_Decls.va_operand_reg_opr64 ->
      (Vale_X64_Decls.ins, Vale_X64_Decls.ocmp) Vale_X64_Machine_s.precode)
  =
  fun dst ->
    fun tmp ->
      Vale_X64_Machine_s.Block
        [va_code_Pop_Secret tmp;
        Vale_X64_InsVector.va_code_Pinsrq dst tmp Prims.int_one;
        va_code_Pop_Secret tmp;
        Vale_X64_InsVector.va_code_Pinsrq dst tmp Prims.int_zero]
let (va_codegen_success_PopXmm_Secret :
  Vale_X64_Machine_s.reg_xmm ->
    Vale_X64_Decls.va_operand_reg_opr64 -> Vale_X64_Decls.va_pbool)
  =
  fun dst ->
    fun tmp ->
      Vale_X64_Decls.va_pbool_and (va_codegen_success_Pop_Secret tmp)
        (Vale_X64_Decls.va_pbool_and
           (Vale_X64_InsVector.va_codegen_success_Pinsrq dst tmp
              Prims.int_one)
           (Vale_X64_Decls.va_pbool_and (va_codegen_success_Pop_Secret tmp)
              (Vale_X64_Decls.va_pbool_and
                 (Vale_X64_InsVector.va_codegen_success_Pinsrq dst tmp
                    Prims.int_zero) (Vale_X64_Decls.va_ttrue ()))))
type ('dst, 'tmp, 'expecteduxmm, 'vaus0, 'vauk) va_wp_PopXmm_Secret = unit
