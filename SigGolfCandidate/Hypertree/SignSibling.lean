import SigGolfCandidate.Hypertree.SignCaptureUpper

namespace SigGolfCandidate.Hypertree.Signing
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 Expansion
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false

def siblingInstructions : List Instr := [
  .LUI .x28 0x80,
  .ADDI .x28 .x28 0x420,
  .LD .x6 .x28 0,
  .XORI .x6 .x6 1,
  .SLLI .x6 .x6 4,
  .LUI .x7 0x80,
  .ADDI .x7 .x7 0x520,
  .ADD .x7 .x7 .x6,
  .LUI .x28 0x80,
  .ADDI .x28 .x28 0x448,
  .LD .x10 .x28 0,
  .LUI .x28 0x80,
  .ADDI .x28 .x28 0x400,
  .LD .x11 .x28 0,
  .BEQ .x11 .x0 12,
  .ADDI .x10 .x10 736,
  .JAL .x0 8,
  .ADDI .x10 .x10 16,
  .LD .x11 .x7 0,
  .LD .x12 .x7 8,
  .SD .x10 .x11 0,
  .SD .x10 .x12 8]

def SiblingPrepareCode (image : Image) (base : Word) : Prop :=
  ∀ (s : MachineState) (i : Fin 18), s.pc = base + BitVec.ofNat 64 (4 * i.val) →
    fetch image s = some (.base (siblingInstructions[i.val]'(by simp [siblingInstructions]; omega)))

def siblingReadState (s : MachineState) : MachineState :=
  let s := execInstrBr s (.LUI .x28 0x80)
  let s := execInstrBr s (.ADDI .x28 .x28 0x420)
  let s := execInstrBr s (.LD .x6 .x28 0)
  let s := execInstrBr s (.XORI .x6 .x6 1)
  let s := execInstrBr s (.SLLI .x6 .x6 4)
  let s := execInstrBr s (.LUI .x7 0x80)
  let s := execInstrBr s (.ADDI .x7 .x7 0x520)
  let s := execInstrBr s (.ADD .x7 .x7 .x6)
  let s := execInstrBr s (.LUI .x28 0x80)
  let s := execInstrBr s (.ADDI .x28 .x28 0x448)
  let s := execInstrBr s (.LD .x10 .x28 0)
  let s := execInstrBr s (.LUI .x28 0x80)
  let s := execInstrBr s (.ADDI .x28 .x28 0x400)
  execInstrBr s (.LD .x11 .x28 0)

theorem siblingRead_block (image : Image) (base : Word) (code : SiblingPrepareCode image base)
    (s : MachineState) (pc : s.pc = base + 0) :
    OrdinarySteps image s 14 (siblingReadState s) := by
  let s1 := execInstrBr s (.LUI .x28 0x80)
  let s2 := execInstrBr s1 (.ADDI .x28 .x28 0x420)
  let s3 := execInstrBr s2 (.LD .x6 .x28 0)
  let s4 := execInstrBr s3 (.XORI .x6 .x6 1)
  let s5 := execInstrBr s4 (.SLLI .x6 .x6 4)
  let s6 := execInstrBr s5 (.LUI .x7 0x80)
  let s7 := execInstrBr s6 (.ADDI .x7 .x7 0x520)
  let s8 := execInstrBr s7 (.ADD .x7 .x7 .x6)
  let s9 := execInstrBr s8 (.LUI .x28 0x80)
  let s10 := execInstrBr s9 (.ADDI .x28 .x28 0x448)
  let s11 := execInstrBr s10 (.LD .x10 .x28 0)
  let s12 := execInstrBr s11 (.LUI .x28 0x80)
  let s13 := execInstrBr s12 (.ADDI .x28 .x28 0x400)
  let s14 := execInstrBr s13 (.LD .x11 .x28 0)
  apply OrdinarySteps.step s s1 _ (.base (.LUI .x28 0x80)) 13
  · apply code _ 0
    simp [execInstrBr, pc, BitVec.add_assoc]
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.ADDI .x28 .x28 0x420)) 12
  · apply code _ 1
    simp [s1, execInstrBr, pc, BitVec.add_assoc]
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.LD .x6 .x28 0)) 11
  · apply code _ 2
    simp [s1, s2, execInstrBr, pc, BitVec.add_assoc]
  · simp [s1, s2, s3, ordinaryStep, memoryArgumentsValid, execInstrBr, signExtend12, accessValid, rangeValid, MEMORY_BYTES, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s3 s4 _ (.base (.XORI .x6 .x6 1)) 10
  · apply code _ 3
    simp [s1, s2, s3, execInstrBr, pc, BitVec.add_assoc]
  · rfl
  apply OrdinarySteps.step s4 s5 _ (.base (.SLLI .x6 .x6 4)) 9
  · apply code _ 4
    simp [s1, s2, s3, s4, execInstrBr, pc, BitVec.add_assoc]
  · rfl
  apply OrdinarySteps.step s5 s6 _ (.base (.LUI .x7 0x80)) 8
  · apply code _ 5
    simp [s1, s2, s3, s4, s5, execInstrBr, pc, BitVec.add_assoc]
  · rfl
  apply OrdinarySteps.step s6 s7 _ (.base (.ADDI .x7 .x7 0x520)) 7
  · apply code _ 6
    simp [s1, s2, s3, s4, s5, s6, execInstrBr, pc, BitVec.add_assoc]
  · rfl
  apply OrdinarySteps.step s7 s8 _ (.base (.ADD .x7 .x7 .x6)) 6
  · apply code _ 7
    simp [s1, s2, s3, s4, s5, s6, s7, execInstrBr, pc, BitVec.add_assoc]
  · rfl
  apply OrdinarySteps.step s8 s9 _ (.base (.LUI .x28 0x80)) 5
  · apply code _ 8
    simp [s1, s2, s3, s4, s5, s6, s7, s8, execInstrBr, pc, BitVec.add_assoc]
  · rfl
  apply OrdinarySteps.step s9 s10 _ (.base (.ADDI .x28 .x28 0x448)) 4
  · apply code _ 9
    simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, execInstrBr, pc, BitVec.add_assoc]
  · rfl
  apply OrdinarySteps.step s10 s11 _ (.base (.LD .x10 .x28 0)) 3
  · apply code _ 10
    simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, execInstrBr, pc, BitVec.add_assoc]
  · simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, ordinaryStep, memoryArgumentsValid, execInstrBr, signExtend12, accessValid, rangeValid, MEMORY_BYTES, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s11 s12 _ (.base (.LUI .x28 0x80)) 2
  · apply code _ 11
    simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, execInstrBr, pc, BitVec.add_assoc]
  · rfl
  apply OrdinarySteps.step s12 s13 _ (.base (.ADDI .x28 .x28 0x400)) 1
  · apply code _ 12
    simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, execInstrBr, pc, BitVec.add_assoc]
  · rfl
  apply OrdinarySteps.step s13 s14 _ (.base (.LD .x11 .x28 0)) 0
  · apply code _ 13
    simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, execInstrBr, pc, BitVec.add_assoc]
  · simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, ordinaryStep, memoryArgumentsValid, execInstrBr, signExtend12, accessValid, rangeValid, MEMORY_BYTES, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  exact OrdinarySteps.refl _

def SiblingCopyCode (image : Image) (base : Word) : Prop :=
  ∀ (s : MachineState) (i : Fin 4), s.pc = base + BitVec.ofNat 64 (4 * (18 + i.val)) →
    fetch image s = some (.base (siblingInstructions[18 + i.val]'(by simp [siblingInstructions]; omega)))

structure SiblingCode (image : Image) (base : Word) : Prop where
  prepare : SiblingPrepareCode image base
  copy : SiblingCopyCode image base

def siblingCopyState (s : MachineState) : MachineState :=
  let s := execInstrBr s (.LD .x11 .x7 0)
  let s := execInstrBr s (.LD .x12 .x7 8)
  let s := execInstrBr s (.SD .x10 .x11 0)
  execInstrBr s (.SD .x10 .x12 8)

theorem siblingCopy_block (image : Image) (base : Word) (code : SiblingCopyCode image base)
    (s : MachineState) (pc : s.pc = base + 72)
    (src : accessValid (s.getReg .x7) 8 = true)
    (srcNext : accessValid (s.getReg .x7 + 8) 8 = true)
    (dst : accessValid (s.getReg .x10) 8 = true)
    (dstNext : accessValid (s.getReg .x10 + 8) 8 = true) :
    OrdinarySteps image s 4 (siblingCopyState s) := by
  let s1 := execInstrBr s (.LD .x11 .x7 0)
  let s2 := execInstrBr s1 (.LD .x12 .x7 8)
  let s3 := execInstrBr s2 (.SD .x10 .x11 0)
  let s4 := execInstrBr s3 (.SD .x10 .x12 8)
  apply OrdinarySteps.step s s1 _ (.base (.LD .x11 .x7 0)) 3
  · apply code _ 0
    simp [execInstrBr, pc, BitVec.add_assoc]
  · simp [s1, ordinaryStep, memoryArgumentsValid, execInstrBr, signExtend12, src, srcNext, dst, dstNext, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s1 s2 _ (.base (.LD .x12 .x7 8)) 2
  · apply code _ 1
    simp [s1, execInstrBr, pc, BitVec.add_assoc]
  · simp [s1, s2, ordinaryStep, memoryArgumentsValid, execInstrBr, signExtend12, src, srcNext, dst, dstNext, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
    exact srcNext
  apply OrdinarySteps.step s2 s3 _ (.base (.SD .x10 .x11 0)) 1
  · apply code _ 2
    simp [s1, s2, execInstrBr, pc, BitVec.add_assoc]
  · simp [s1, s2, s3, ordinaryStep, memoryArgumentsValid, execInstrBr, signExtend12, src, srcNext, dst, dstNext, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s3 s4 _ (.base (.SD .x10 .x12 8)) 0
  · apply code _ 3
    simp [s1, s2, s3, execInstrBr, pc, BitVec.add_assoc]
  · simp [s1, s2, s3, s4, ordinaryStep, memoryArgumentsValid, execInstrBr, signExtend12, src, srcNext, dst, dstNext, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
    exact dstNext
  exact OrdinarySteps.refl _

def siblingPointerState (s : MachineState) : MachineState :=
  let branched := execInstrBr s (.BEQ .x11 .x0 12)
  if s.getReg .x11 = 0 then execInstrBr branched (.ADDI .x10 .x10 16)
  else execInstrBr (execInstrBr branched (.ADDI .x10 .x10 736)) (.JAL .x0 8)

theorem siblingPointerState_block (image : Image) (base : Word) (code : SiblingPrepareCode image base)
    (s : MachineState) (pc : s.pc = base + 56) :
    OrdinarySteps image s (if s.getReg .x11 = 0 then 2 else 3) (siblingPointerState s) := by
  let branched := execInstrBr s (.BEQ .x11 .x0 12)
  by_cases zero : s.getReg .x11 = 0
  · simp only [zero, if_true, siblingPointerState]
    apply OrdinarySteps.step s branched _ (.base (.BEQ .x11 .x0 12)) 1
    · apply code _ 14; exact pc
    · rfl
    apply OrdinarySteps.step branched _ _ (.base (.ADDI .x10 .x10 16)) 0
    · apply code _ 17
      simp [branched, execInstrBr, zero, signExtend13, pc, BitVec.add_assoc]
    · rfl
    exact OrdinarySteps.refl _
  · have zero' : s.getReg .x11 ≠ 0#64 := zero
    simp only [zero, if_false, siblingPointerState]
    apply OrdinarySteps.step s branched _ (.base (.BEQ .x11 .x0 12)) 2
    · apply code _ 14; exact pc
    · rfl
    let incremented := execInstrBr branched (.ADDI .x10 .x10 736)
    apply OrdinarySteps.step branched incremented _ (.base (.ADDI .x10 .x10 736)) 1
    · apply code _ 15
      simp [branched, execInstrBr, zero', signExtend13, pc, BitVec.add_assoc]
    · rfl
    apply OrdinarySteps.step incremented _ _ (.base (.JAL .x0 8)) 0
    · apply code _ 16
      simp [incremented, branched, execInstrBr, zero', signExtend13, pc, BitVec.add_assoc]
    · rfl
    exact OrdinarySteps.refl _

theorem siblingRead_pc (s : MachineState) : (siblingReadState s).pc = s.pc + 56 := by
  simp [siblingReadState, execInstrBr, BitVec.add_assoc]

theorem siblingRead_regs (s : MachineState) :
    (siblingReadState s).getReg .x7 = 0x80520 + ((s.getMem 0x80420 ^^^ 1) <<< 4) ∧
    (siblingReadState s).getReg .x10 = s.getMem 0x80448 ∧
    (siblingReadState s).getReg .x11 = s.getMem 0x80400 := by
  simp [siblingReadState, execInstrBr, signExtend12,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]

theorem siblingRead_mem (s : MachineState) (a : Word) :
    (siblingReadState s).getMem a = s.getMem a := by
  simp [siblingReadState, execInstrBr]

theorem siblingRead_sp (s : MachineState) :
    (siblingReadState s).getReg .x2 = s.getReg .x2 := by
  simp [siblingReadState, execInstrBr, MachineState.getReg_setReg_ne]

theorem siblingPointer_pc (s : MachineState) (base : Word) (pc : s.pc = base + 56) :
    (siblingPointerState s).pc = base + 72 := by
  simp [siblingPointerState, execInstrBr, signExtend12, signExtend13, signExtend21,
    pc, BitVec.add_assoc]
  split <;> simp [BitVec.add_assoc]

theorem siblingPointer_regs (s : MachineState) :
    (siblingPointerState s).getReg .x7 = s.getReg .x7 ∧
    (siblingPointerState s).getReg .x10 = s.getReg .x10 + (if s.getReg .x11 = 0 then 16 else 736) := by
  unfold siblingPointerState
  split <;> simp_all [execInstrBr, signExtend12,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]

theorem siblingPointer_mem (s : MachineState) (a : Word) :
    (siblingPointerState s).getMem a = s.getMem a := by
  unfold siblingPointerState
  split <;> simp [execInstrBr]

theorem siblingPointer_sp (s : MachineState) :
    (siblingPointerState s).getReg .x2 = s.getReg .x2 := by
  unfold siblingPointerState
  split <;> simp [execInstrBr, MachineState.getReg_setReg_ne]

theorem siblingCopy_pc (s : MachineState) : (siblingCopyState s).pc = s.pc + 16 := by
  simp [siblingCopyState, execInstrBr, BitVec.add_assoc]

theorem siblingCopy_mem (s : MachineState) (a : Word) :
    (siblingCopyState s).getMem a =
      if a = s.getReg .x10 + 8 then s.getMem (s.getReg .x7 + 8) else
      if a = s.getReg .x10 then s.getMem (s.getReg .x7) else s.getMem a := by
  simp [siblingCopyState, execInstrBr, signExtend12, Expansion.mem_setMem,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]

theorem siblingCopy_sp (s : MachineState) :
    (siblingCopyState s).getReg .x2 = s.getReg .x2 := by
  simp [siblingCopyState, execInstrBr, MachineState.getReg_setReg_ne]


end SigGolfCandidate.Hypertree.Signing
