import SigGolfCandidate.Hypertree.SignEncodeFinish

namespace SigGolfCandidate.Hypertree.Signing
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false

def encodeSetupState (s : MachineState) : MachineState :=
  let s := execInstrBr s (.LUI .x28 0x80)
  let s := execInstrBr s (.ADDI .x28 .x28 0x500)
  let s := execInstrBr s (.LD .x6 .x28 0)
  let s := execInstrBr s (.LUI .x28 0x80)
  let s := execInstrBr s (.ADDI .x28 .x28 0x508)
  let s := execInstrBr s (.LD .x7 .x28 0)
  let s := execInstrBr s (.LUI .x10 0x80)
  let s := execInstrBr s (.ADDI .x10 .x10 0x600)
  let s := execInstrBr s (.ADDI .x11 .x0 43)
  execInstrBr s (.ADDI .x12 .x0 301)

def encodeSetupInstructions : List Instr := [
  .LUI .x28 0x80,
  .ADDI .x28 .x28 0x500,
  .LD .x6 .x28 0,
  .LUI .x28 0x80,
  .ADDI .x28 .x28 0x508,
  .LD .x7 .x28 0,
  .LUI .x10 0x80,
  .ADDI .x10 .x10 0x600,
  .ADDI .x11 .x0 43,
  .ADDI .x12 .x0 301]

def EncodeSetupCode (image : Image) (base : Word) : Prop :=
  ∀ (s : MachineState) (i : Fin 10), s.pc = base + BitVec.ofNat 64 (4 * i.val) →
    fetch image s = some (.base (encodeSetupInstructions[i.val]'(by simp [encodeSetupInstructions])))

theorem encodeSetupState_block (image : Image) (base : Word) (code : EncodeSetupCode image base)
    (s : MachineState) (pc : s.pc = base) : OrdinarySteps image s 10 (encodeSetupState s) := by
  let s1 := execInstrBr s (.LUI .x28 0x80)
  let s2 := execInstrBr s1 (.ADDI .x28 .x28 0x500)
  let s3 := execInstrBr s2 (.LD .x6 .x28 0)
  let s4 := execInstrBr s3 (.LUI .x28 0x80)
  let s5 := execInstrBr s4 (.ADDI .x28 .x28 0x508)
  let s6 := execInstrBr s5 (.LD .x7 .x28 0)
  let s7 := execInstrBr s6 (.LUI .x10 0x80)
  let s8 := execInstrBr s7 (.ADDI .x10 .x10 0x600)
  let s9 := execInstrBr s8 (.ADDI .x11 .x0 43)
  let s10 := execInstrBr s9 (.ADDI .x12 .x0 301)
  apply OrdinarySteps.step s s1 _ (.base (.LUI .x28 0x80)) 9
  · apply code _ 0
    simp [execInstrBr, pc, BitVec.add_assoc]
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.ADDI .x28 .x28 0x500)) 8
  · apply code _ 1
    simp [s1, execInstrBr, pc, BitVec.add_assoc]
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.LD .x6 .x28 0)) 7
  · apply code _ 2
    simp [s1, s2, execInstrBr, pc, BitVec.add_assoc]
  · simp [s1, s2, s3, ordinaryStep, memoryArgumentsValid, execInstrBr, signExtend12, accessValid, rangeValid, MEMORY_BYTES, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s3 s4 _ (.base (.LUI .x28 0x80)) 6
  · apply code _ 3
    simp [s1, s2, s3, execInstrBr, pc, BitVec.add_assoc]
  · rfl
  apply OrdinarySteps.step s4 s5 _ (.base (.ADDI .x28 .x28 0x508)) 5
  · apply code _ 4
    simp [s1, s2, s3, s4, execInstrBr, pc, BitVec.add_assoc]
  · rfl
  apply OrdinarySteps.step s5 s6 _ (.base (.LD .x7 .x28 0)) 4
  · apply code _ 5
    simp [s1, s2, s3, s4, s5, execInstrBr, pc, BitVec.add_assoc]
  · simp [s1, s2, s3, s4, s5, s6, ordinaryStep, memoryArgumentsValid, execInstrBr, signExtend12, accessValid, rangeValid, MEMORY_BYTES, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s6 s7 _ (.base (.LUI .x10 0x80)) 3
  · apply code _ 6
    simp [s1, s2, s3, s4, s5, s6, execInstrBr, pc, BitVec.add_assoc]
  · rfl
  apply OrdinarySteps.step s7 s8 _ (.base (.ADDI .x10 .x10 0x600)) 2
  · apply code _ 7
    simp [s1, s2, s3, s4, s5, s6, s7, execInstrBr, pc, BitVec.add_assoc]
  · rfl
  apply OrdinarySteps.step s8 s9 _ (.base (.ADDI .x11 .x0 43)) 1
  · apply code _ 8
    simp [s1, s2, s3, s4, s5, s6, s7, s8, execInstrBr, pc, BitVec.add_assoc]
  · rfl
  apply OrdinarySteps.step s9 s10 _ (.base (.ADDI .x12 .x0 301)) 0
  · apply code _ 9
    simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, execInstrBr, pc, BitVec.add_assoc]
  · rfl
  exact OrdinarySteps.refl _

theorem encodeSetupState_pc (s : MachineState) : (encodeSetupState s).pc = s.pc + 40 := by
  simp [encodeSetupState, execInstrBr, BitVec.add_assoc]

theorem encodeSetupState_mem (s : MachineState) (a : Word) :
    (encodeSetupState s).getMem a = s.getMem a := by simp [encodeSetupState, execInstrBr]

theorem encodeSetupState_byte (s : MachineState) (a : Word) :
    (encodeSetupState s).getByte a = s.getByte a := by simp only [MachineState.getByte, encodeSetupState_mem]

theorem encodeSetupState_sp (s : MachineState) : (encodeSetupState s).getReg .x2 = s.getReg .x2 := by
  simp [encodeSetupState, execInstrBr, MachineState.getReg_setReg_ne]

theorem encodeSetupState_regs (s : MachineState) :
    (encodeSetupState s).getReg .x6 = s.getMem 0x80500 ∧
    (encodeSetupState s).getReg .x7 = s.getMem 0x80508 ∧
    (encodeSetupState s).getReg .x10 = 0x80600 ∧
    (encodeSetupState s).getReg .x11 = 43 ∧
    (encodeSetupState s).getReg .x12 = 301 := by
  simp [encodeSetupState, execInstrBr, signExtend12,
    MachineState.getReg_setReg_ne, MachineState.getReg_setReg_eq]

/-- Code conditions for the complete relocated encoding subroutine. -/
structure EncodeCode (image : Image) (base : Word) : Prop where
  enter : Keygen.EnterCode image base
  setup : EncodeSetupCode image (base + 8)
  loop : EncodeLoopCode image (base + 48)
  checksum : ChecksumCode image (base + 88)
  leave : Keygen.ReturnCode image (base + 124)

/-- Equal bytes in an aligned word imply equal word memory, for rebuilding a saved return address. -/
theorem word_eq_of_bytes (original final : MachineState) (base : Nat)
    (align : base % 8 = 0) (bound : base + 8 < 2 ^ 64)
    (same : ∀ i : Fin 8, final.getByte (BitVec.ofNat 64 (base + i.val)) =
      original.getByte (BitVec.ofNat 64 (base + i.val))) :
    final.getMem (BitVec.ofNat 64 base) = original.getMem (BitVec.ofNat 64 base) := by
  apply eq_of_forall_extractByte
  intro i hi
  have h := same ⟨i, hi⟩
  rw [getByte_word final base i align (by omega), getByte_word original base i align (by omega)] at h
  simpa [wordAddress, Nat.div_eq_of_lt hi, Nat.mod_eq_of_lt hi] using h

/-- The complete shared encode subroutine: real entry, all 46 digits, restored stack
and return address, with a byte frame outside the digit buffer. -/
theorem encode_subroutine (image : Image) (base : Word) (code : EncodeCode image base)
    (s : MachineState) (message : Reference.Digest) (pc : s.pc = base)
    (stack : s.getReg .x2 = 0x1000000)
    (lo : s.getMem 0x80500 = message.extractLsb' 0 64)
    (hi : s.getMem 0x80508 = message.extractLsb' 64 64) :
    ∃ final, OrdinarySteps image s 454 final ∧ final.pc = s.getReg .x1 &&& ~~~1#64 ∧
      final.getReg .x2 = s.getReg .x2 ∧
      (∀ i : Reference.Chain, final.getByte (BitVec.ofNat 64 (0x80600 + i.val)) =
        BitVec.ofNat 8 (Reference.digit message i).val) ∧
      (∀ a, (∀ i : Fin 46, a ≠ BitVec.ofNat 64 (0x80600 + i.val)) →
        final.getByte a = (Keygen.enterState s).getByte a) := by
  have enter := Keygen.enter_block image base code.enter s pc (by rw [stack]; decide)
  have enterPC : (Keygen.enterState s).pc = base + 8 := by rw [Keygen.enter_pc, pc]
  have setup := encodeSetupState_block image (base + 8) code.setup (Keygen.enterState s) enterPC
  have setupPC : (encodeSetupState (Keygen.enterState s)).pc = base + 48 := by
    rw [encodeSetupState_pc, enterPC]; simp [BitVec.add_assoc]
  obtain ⟨rlo, rhi, rptr, rcount, rsum⟩ := encodeSetupState_regs (Keygen.enterState s)
  have low : (encodeSetupState (Keygen.enterState s)).getReg .x6 = message.extractLsb' 0 64 := by
    rw [rlo, Keygen.enter_mem, stack, if_neg (by decide), lo]
  have high : (encodeSetupState (Keygen.enterState s)).getReg .x7 = message.extractLsb' 64 64 := by
    rw [rhi, Keygen.enter_mem, stack, if_neg (by decide), hi]
  obtain ⟨digits, rounds, digitsPC, digitsPtr, digitsSum, digitsOut, digitsFrame, digitsSP⟩ :=
    encode_message_refines image (base + 48) code.loop message (encodeSetupState (Keygen.enterState s))
      setupPC low high rptr rcount rsum
  have checksumPC : digits.pc = base + 88 := by simpa [BitVec.add_assoc] using digitsPC
  have checksumBlock := checksumState_block image (base + 88) code.checksum digits checksumPC digitsPtr
  have returnPC : (checksumState digits).pc = base + 124 := by
    rw [checksumState_pc, checksumPC]; simp [BitVec.add_assoc]
  have savedSP : (checksumState digits).getReg .x2 = 0xfffff0 := by
    rw [checksumState_sp, digitsSP, encodeSetupState_sp, Keygen.enter_sp, stack]; rfl
  have bodyFrame (a : Word) (outside : ∀ i : Fin 46, a ≠ BitVec.ofNat 64 (0x80600 + i.val)) :
      (checksumState digits).getByte a = (Keygen.enterState s).getByte a := by
    rw [checksumState_frame digits digitsPtr, digitsFrame, encodeSetupState_byte]
    · intro i; exact outside ⟨i.val, by have := i.isLt; omega⟩
    · intro i
      have eq : 0x8062b + i.val = 0x80600 + (43 + i.val) := by omega
      rw [eq]; exact outside ⟨43 + i.val, by have := i.isLt; omega⟩
  have savedRA : (checksumState digits).getMem 0xfffff0 = s.getReg .x1 := by
    have unchanged := word_eq_of_bytes (Keygen.enterState s) (checksumState digits) 0xfffff0
      (by decide) (by decide) (fun i => bodyFrame _ (by
        intro j eq
        have same := congrArg BitVec.toNat eq
        have ib := i.isLt
        have jb := j.isLt
        simp only [BitVec.toNat_ofNat] at same
        omega))
    calc
      _ = (Keygen.enterState s).getMem 0xfffff0 := unchanged
      _ = s.getReg .x1 := by rw [Keygen.enter_mem, stack, if_pos (by decide)]
  have ret := Keygen.return_block image (base + 124) code.leave (checksumState digits) returnPC
    (by rw [savedSP]; decide)
  refine ⟨Keygen.returnState (checksumState digits), ?_, ?_, ?_, ?_, ?_⟩
  · exact Keygen.ordinary_trans image s _ _ 12 442
      (Keygen.ordinary_trans image s _ _ 2 10 enter setup)
      (Keygen.ordinary_trans image _ _ _ 430 12 rounds
        (Keygen.ordinary_trans image _ _ _ 9 3 checksumBlock ret))
  · rw [Keygen.return_pc, savedSP, savedRA]
  · rw [Keygen.return_sp, savedSP, stack]; rfl
  · intro i
    have output := checksumState_refines digits message digitsPtr digitsSum digitsOut i
    simpa only [MachineState.getByte, Keygen.return_mem] using output
  · intro a outside
    simpa only [MachineState.getByte, Keygen.return_mem] using bodyFrame a outside

theorem sign_encode_code : EncodeCode sign 0x1340 := by
  refine ⟨by decide, ?_, sign_encode_loop_code, sign_checksum_code, by decide⟩
  intro s i pc
  simp only [fetch, pc]
  fin_cases i <;> decide

theorem verify_encode_code : EncodeCode verify 0x1268 := by
  refine ⟨by decide, ?_, verify_encode_loop_code, verify_checksum_code, by decide⟩
  intro s i pc
  simp only [fetch, pc]
  fin_cases i <;> decide

set_option format.width 200
/-- info: 'SigGolfCandidate.Hypertree.Signing.encode_subroutine' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms encode_subroutine

end SigGolfCandidate.Hypertree.Signing
