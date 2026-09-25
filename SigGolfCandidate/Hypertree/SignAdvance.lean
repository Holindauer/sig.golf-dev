import SigGolfCandidate.Hypertree.SignEncodeSubroutine

namespace SigGolfCandidate.Hypertree.Signing
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 Expansion
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false

def advanceInstructions : List Instr := [
  .LUI .x28 0x80,
  .ADDI .x28 .x28 0x400,
  .LD .x6 .x28 0,
  .LUI .x28 0x80,
  .ADDI .x28 .x28 0x448,
  .LD .x7 .x28 0,
  .BEQ .x6 .x0 12,
  .ADDI .x7 .x7 752,
  .JAL .x0 8,
  .ADDI .x7 .x7 32,
  .LUI .x28 0x80,
  .ADDI .x28 .x28 0x448,
  .SD .x28 .x7 0,
  .ADDI .x6 .x6 1,
  .LUI .x28 0x80,
  .ADDI .x28 .x28 0x400,
  .SD .x28 .x6 0,
  .ADDI .x7 .x0 160,
  .BNE .x6 .x7 (-212)]

def AdvanceCode (image : Image) (base : Word) : Prop :=
  ∀ (s : MachineState) (i : Fin 19), s.pc = base + BitVec.ofNat 64 (4 * i.val) →
    fetch image s = some (.base (advanceInstructions[i.val]'(by simp [advanceInstructions])))

def advanceReadState (s : MachineState) : MachineState :=
  let s := execInstrBr s (.LUI .x28 0x80)
  let s := execInstrBr s (.ADDI .x28 .x28 0x400)
  let s := execInstrBr s (.LD .x6 .x28 0)
  let s := execInstrBr s (.LUI .x28 0x80)
  let s := execInstrBr s (.ADDI .x28 .x28 0x448)
  execInstrBr s (.LD .x7 .x28 0)

theorem advanceReadState_block (image : Image) (base : Word) (code : AdvanceCode image base)
    (s : MachineState) (pc : s.pc = base + 0) :
    OrdinarySteps image s 6 (advanceReadState s) := by
  let s1 := execInstrBr s (.LUI .x28 0x80)
  let s2 := execInstrBr s1 (.ADDI .x28 .x28 0x400)
  let s3 := execInstrBr s2 (.LD .x6 .x28 0)
  let s4 := execInstrBr s3 (.LUI .x28 0x80)
  let s5 := execInstrBr s4 (.ADDI .x28 .x28 0x448)
  let s6 := execInstrBr s5 (.LD .x7 .x28 0)
  apply OrdinarySteps.step s s1 _ (.base (.LUI .x28 0x80)) 5
  · apply code _ 0
    simp [execInstrBr, pc, BitVec.add_assoc]
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.ADDI .x28 .x28 0x400)) 4
  · apply code _ 1
    simp [s1, execInstrBr, pc, BitVec.add_assoc]
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.LD .x6 .x28 0)) 3
  · apply code _ 2
    simp [s1, s2, execInstrBr, pc, BitVec.add_assoc]
  · simp [s1, s2, s3, ordinaryStep, memoryArgumentsValid, execInstrBr, signExtend12, accessValid, rangeValid, MEMORY_BYTES, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s3 s4 _ (.base (.LUI .x28 0x80)) 2
  · apply code _ 3
    simp [s1, s2, s3, execInstrBr, pc, BitVec.add_assoc]
  · rfl
  apply OrdinarySteps.step s4 s5 _ (.base (.ADDI .x28 .x28 0x448)) 1
  · apply code _ 4
    simp [s1, s2, s3, s4, execInstrBr, pc, BitVec.add_assoc]
  · rfl
  apply OrdinarySteps.step s5 s6 _ (.base (.LD .x7 .x28 0)) 0
  · apply code _ 5
    simp [s1, s2, s3, s4, s5, execInstrBr, pc, BitVec.add_assoc]
  · simp [s1, s2, s3, s4, s5, s6, ordinaryStep, memoryArgumentsValid, execInstrBr, signExtend12, accessValid, rangeValid, MEMORY_BYTES, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  exact OrdinarySteps.refl _

def advanceTailState (s : MachineState) : MachineState :=
  let s := execInstrBr s (.LUI .x28 0x80)
  let s := execInstrBr s (.ADDI .x28 .x28 0x448)
  let s := execInstrBr s (.SD .x28 .x7 0)
  let s := execInstrBr s (.ADDI .x6 .x6 1)
  let s := execInstrBr s (.LUI .x28 0x80)
  let s := execInstrBr s (.ADDI .x28 .x28 0x400)
  let s := execInstrBr s (.SD .x28 .x6 0)
  let s := execInstrBr s (.ADDI .x7 .x0 160)
  execInstrBr s (.BNE .x6 .x7 (-212))

theorem advanceTailState_block (image : Image) (base : Word) (code : AdvanceCode image base)
    (s : MachineState) (pc : s.pc = base + 40) :
    OrdinarySteps image s 9 (advanceTailState s) := by
  let s1 := execInstrBr s (.LUI .x28 0x80)
  let s2 := execInstrBr s1 (.ADDI .x28 .x28 0x448)
  let s3 := execInstrBr s2 (.SD .x28 .x7 0)
  let s4 := execInstrBr s3 (.ADDI .x6 .x6 1)
  let s5 := execInstrBr s4 (.LUI .x28 0x80)
  let s6 := execInstrBr s5 (.ADDI .x28 .x28 0x400)
  let s7 := execInstrBr s6 (.SD .x28 .x6 0)
  let s8 := execInstrBr s7 (.ADDI .x7 .x0 160)
  let s9 := execInstrBr s8 (.BNE .x6 .x7 (-212))
  apply OrdinarySteps.step s s1 _ (.base (.LUI .x28 0x80)) 8
  · apply code _ 10
    simp [execInstrBr, pc, BitVec.add_assoc]
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.ADDI .x28 .x28 0x448)) 7
  · apply code _ 11
    simp [s1, execInstrBr, pc, BitVec.add_assoc]
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.SD .x28 .x7 0)) 6
  · apply code _ 12
    simp [s1, s2, execInstrBr, pc, BitVec.add_assoc]
  · simp [s1, s2, s3, ordinaryStep, memoryArgumentsValid, execInstrBr, signExtend12, accessValid, rangeValid, MEMORY_BYTES, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s3 s4 _ (.base (.ADDI .x6 .x6 1)) 5
  · apply code _ 13
    simp [s1, s2, s3, execInstrBr, pc, BitVec.add_assoc]
  · rfl
  apply OrdinarySteps.step s4 s5 _ (.base (.LUI .x28 0x80)) 4
  · apply code _ 14
    simp [s1, s2, s3, s4, execInstrBr, pc, BitVec.add_assoc]
  · rfl
  apply OrdinarySteps.step s5 s6 _ (.base (.ADDI .x28 .x28 0x400)) 3
  · apply code _ 15
    simp [s1, s2, s3, s4, s5, execInstrBr, pc, BitVec.add_assoc]
  · rfl
  apply OrdinarySteps.step s6 s7 _ (.base (.SD .x28 .x6 0)) 2
  · apply code _ 16
    simp [s1, s2, s3, s4, s5, s6, execInstrBr, pc, BitVec.add_assoc]
  · simp [s1, s2, s3, s4, s5, s6, s7, ordinaryStep, memoryArgumentsValid, execInstrBr, signExtend12, accessValid, rangeValid, MEMORY_BYTES, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s7 s8 _ (.base (.ADDI .x7 .x0 160)) 1
  · apply code _ 17
    simp [s1, s2, s3, s4, s5, s6, s7, execInstrBr, pc, BitVec.add_assoc]
  · rfl
  apply OrdinarySteps.step s8 s9 _ (.base (.BNE .x6 .x7 (-212))) 0
  · apply code _ 18
    simp [s1, s2, s3, s4, s5, s6, s7, s8, execInstrBr, pc, BitVec.add_assoc]
  · rfl
  exact OrdinarySteps.refl _

def advancePointerState (s : MachineState) : MachineState :=
  let branched := execInstrBr s (.BEQ .x6 .x0 12)
  if s.getReg .x6 = 0 then execInstrBr branched (.ADDI .x7 .x7 32)
  else execInstrBr (execInstrBr branched (.ADDI .x7 .x7 752)) (.JAL .x0 8)

theorem advancePointerState_block (image : Image) (base : Word) (code : AdvanceCode image base)
    (s : MachineState) (pc : s.pc = base + 24) :
    OrdinarySteps image s (if s.getReg .x6 = 0 then 2 else 3) (advancePointerState s) := by
  let branched := execInstrBr s (.BEQ .x6 .x0 12)
  by_cases zero : s.getReg .x6 = 0
  · simp only [zero, if_true, advancePointerState]
    apply OrdinarySteps.step s branched _ (.base (.BEQ .x6 .x0 12)) 1
    · apply code _ 6; exact pc
    · rfl
    apply OrdinarySteps.step branched _ _ (.base (.ADDI .x7 .x7 32)) 0
    · apply code _ 9
      simp [branched, execInstrBr, zero, signExtend13, pc, BitVec.add_assoc]
    · rfl
    exact OrdinarySteps.refl _
  · have zero' : s.getReg .x6 ≠ 0#64 := zero
    simp only [zero, if_false, advancePointerState]
    apply OrdinarySteps.step s branched _ (.base (.BEQ .x6 .x0 12)) 2
    · apply code _ 6; exact pc
    · rfl
    let incremented := execInstrBr branched (.ADDI .x7 .x7 752)
    apply OrdinarySteps.step branched incremented _ (.base (.ADDI .x7 .x7 752)) 1
    · apply code _ 7
      simp [branched, execInstrBr, zero', signExtend13, pc, BitVec.add_assoc]
    · rfl
    apply OrdinarySteps.step incremented _ _ (.base (.JAL .x0 8)) 0
    · apply code _ 8
      simp [incremented, branched, execInstrBr, zero', signExtend13, pc, BitVec.add_assoc]
    · rfl
    exact OrdinarySteps.refl _

theorem advanceReadState_pc (s : MachineState) : (advanceReadState s).pc = s.pc + 24 := by
  simp [advanceReadState, execInstrBr, BitVec.add_assoc]

theorem advanceReadState_regs (s : MachineState) :
    (advanceReadState s).getReg .x6 = s.getMem 0x80400 ∧
    (advanceReadState s).getReg .x7 = s.getMem 0x80448 := by
  simp [advanceReadState, execInstrBr, signExtend12,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]

theorem advancePointerState_pc (s : MachineState) (base : Word) (pc : s.pc = base + 24) :
    (advancePointerState s).pc = base + 40 := by
  simp [advancePointerState, execInstrBr, signExtend12, signExtend13, signExtend21,
    pc, BitVec.add_assoc]
  split <;> simp [BitVec.add_assoc]

theorem advancePointerState_regs (s : MachineState) :
    (advancePointerState s).getReg .x6 = s.getReg .x6 ∧
    (advancePointerState s).getReg .x7 = s.getReg .x7 + (if s.getReg .x6 = 0 then 32 else 752) := by
  unfold advancePointerState
  split <;> simp_all [execInstrBr, signExtend12,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]

def advanceState (s : MachineState) : MachineState := advanceTailState (advancePointerState (advanceReadState s))

theorem advance_block (image : Image) (base : Word) (code : AdvanceCode image base)
    (s : MachineState) (pc : s.pc = base) :
    OrdinarySteps image s (if s.getMem 0x80400 = 0 then 17 else 18) (advanceState s) := by
  have readpc : (advanceReadState s).pc = base + 24 := by rw [advanceReadState_pc, pc]
  have pointerpc := advancePointerState_pc (advanceReadState s) base readpc
  have block := Keygen.ordinary_trans image s _ _ 6 _
    (advanceReadState_block image base code s (by simpa using pc))
    (Keygen.ordinary_trans image (advanceReadState s) _ _ _ 9
      (advancePointerState_block image base code (advanceReadState s) readpc)
      (advanceTailState_block image base code _ pointerpc))
  rw [(advanceReadState_regs s).1] at block
  have count : 9 + (if s.getMem 0x80400 = 0 then 2 else 3) + 6 =
      (if s.getMem 0x80400 = 0 then 17 else 18) := by split <;> rfl
  rw [count] at block
  exact block

theorem advanceReadState_mem (s : MachineState) (a : Word) :
    (advanceReadState s).getMem a = s.getMem a := by
  simp [advanceReadState, execInstrBr]

theorem advancePointerState_mem (s : MachineState) (a : Word) :
    (advancePointerState s).getMem a = s.getMem a := by
  unfold advancePointerState
  split <;> simp [execInstrBr]

theorem advanceTailState_mem (s : MachineState) (a : Word) :
    (advanceTailState s).getMem a =
      if a = 0x80400 then s.getReg .x6 + 1 else
      if a = 0x80448 then s.getReg .x7 else s.getMem a := by
  simp [advanceTailState, execInstrBr, signExtend12, Expansion.mem_setMem,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]

/-- Exact counter/pointer changes, together with a frame for every other word. -/
theorem advanceState_mem (s : MachineState) (a : Word) :
    (advanceState s).getMem a =
      if a = 0x80400 then s.getMem 0x80400 + 1 else
      if a = 0x80448 then s.getMem 0x80448 + (if s.getMem 0x80400 = 0 then 32 else 752)
      else s.getMem a := by
  simp only [advanceState, advanceTailState_mem, advancePointerState_regs,
    advanceReadState_regs, advancePointerState_mem, advanceReadState_mem]

theorem advanceTailState_pc (s : MachineState) :
    (advanceTailState s).pc =
      if s.getReg .x6 + 1 = 160 then s.pc + 36 else s.pc - 180 := by
  simp [advanceTailState, execInstrBr, signExtend12, signExtend13,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne, BitVec.add_assoc]
  split <;> simp_all [BitVec.sub_eq_add_neg, BitVec.add_assoc]

theorem advanceState_pc (s : MachineState) (base : Word) (pc : s.pc = base) :
    (advanceState s).pc =
      if s.getMem 0x80400 + 1 = 160 then base + 76 else base - 140 := by
  have readpc : (advanceReadState s).pc = base + 24 := by rw [advanceReadState_pc, pc]
  rw [advanceState, advanceTailState_pc, (advancePointerState_regs _).1,
    (advanceReadState_regs _).1, advancePointerState_pc _ base readpc]
  split <;> simp [BitVec.sub_eq_add_neg, BitVec.add_assoc]

theorem advanceReadState_sp (s : MachineState) :
    (advanceReadState s).getReg .x2 = s.getReg .x2 := by
  simp [advanceReadState, execInstrBr, MachineState.getReg_setReg_ne]

theorem advancePointerState_sp (s : MachineState) :
    (advancePointerState s).getReg .x2 = s.getReg .x2 := by
  unfold advancePointerState
  split <;> simp [execInstrBr, MachineState.getReg_setReg_ne]

theorem advanceTailState_sp (s : MachineState) :
    (advanceTailState s).getReg .x2 = s.getReg .x2 := by
  simp [advanceTailState, execInstrBr, MachineState.getReg_setReg_ne]

theorem advanceState_sp (s : MachineState) :
    (advanceState s).getReg .x2 = s.getReg .x2 := by
  simp only [advanceState, advanceTailState_sp, advancePointerState_sp, advanceReadState_sp]

/-- The body offset after `level` completed layers; the randomizer occupies bytes 0–31. -/
def layerOffset (level : Nat) : Nat := if level = 0 then 32 else 64 + 752 * (level - 1)

theorem layerOffset_succ (level : Nat) :
    layerOffset (level + 1) = layerOffset level + (if level = 0 then 32 else 752) := by
  unfold layerOffset
  split <;> split <;> omega

theorem layerOffset_last : layerOffset 160 = signatureBytes := by rfl

/-- The exact machine updates agree with the compact wire format's layer boundaries. -/
theorem advanceState_layer (s : MachineState) (input level : Nat) (bound : level < 160)
    (counter : s.getMem 0x80400 = BitVec.ofNat 64 level)
    (pointer : s.getMem 0x80448 = BitVec.ofNat 64 (input + layerOffset level)) :
    (advanceState s).getMem 0x80400 = BitVec.ofNat 64 (level + 1) ∧
    (advanceState s).getMem 0x80448 = BitVec.ofNat 64 (input + layerOffset (level + 1)) := by
  have zero : (BitVec.ofNat 64 level = (0 : Word)) ↔ level = 0 := by
    have small : level < 2 ^ 64 := by omega
    change (BitVec.ofNat 64 level = BitVec.ofNat 64 0) ↔ _
    simp only [BitVec.toNat_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt small]
  constructor
  · rw [advanceState_mem, if_pos rfl, counter]
    exact (BitVec.ofNat_add _ _).symm
  · rw [advanceState_mem, if_neg (by decide), if_pos rfl, counter, pointer]
    simp only [zero, layerOffset_succ]
    by_cases h : level = 0 <;> simp only [h, if_true, if_false]
    · exact (BitVec.ofNat_add _ _).symm.trans (by congr 1)
    · exact (BitVec.ofNat_add _ _).symm.trans (by congr 1)

theorem advanceState_layer_pc (s : MachineState) (base : Word) (level : Nat)
    (pc : s.pc = base) (bound : level < 160)
    (counter : s.getMem 0x80400 = BitVec.ofNat 64 level) :
    (advanceState s).pc = if level + 1 = 160 then base + 76 else base - 140 := by
  rw [advanceState_pc s base pc, counter]
  have add : BitVec.ofNat 64 level + 1 = BitVec.ofNat 64 (level + 1) := (BitVec.ofNat_add _ _).symm
  rw [add]
  have eq : (BitVec.ofNat 64 (level + 1) = (160 : Word)) ↔ level + 1 = 160 := by
    have small : level + 1 < 2 ^ 64 := by omega
    change (BitVec.ofNat 64 (level + 1) = BitVec.ofNat 64 160) ↔ _
    simp only [BitVec.toNat_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt small]
  simp only [eq]

theorem sign_advance_code : AdvanceCode sign 0x12ac := by
  intro s i pc
  simp only [fetch, pc]
  fin_cases i <;> decide

theorem verify_advance_code : AdvanceCode verify 0x11d4 := by
  intro s i pc
  simp only [fetch, pc]
  fin_cases i <;> decide

end SigGolfCandidate.Hypertree.Signing
