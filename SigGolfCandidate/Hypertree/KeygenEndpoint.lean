import SigGolfCandidate.Hypertree.KeygenDomain

namespace SigGolfCandidate.Hypertree.KeygenEndpoint

open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 OracleComp Keygen

set_option maxRecDepth 4096

set_option linter.unusedSimpArgs false

def Code (image : Image) (p : Word) (offset : BitVec 13) : Prop :=
  instructionAt image (p + 0) = some (.base (.LUI .x28 128)) ∧
  instructionAt image (p + 4) = some (.base (.ADDI .x28 .x28 1072)) ∧
  instructionAt image (p + 8) = some (.base (.LD .x6 .x28 0)) ∧
  instructionAt image (p + 12) = some (.base (.SLLI .x7 .x6 4)) ∧
  instructionAt image (p + 16) = some (.base (.LUI .x10 129)) ∧
  instructionAt image (p + 20) = some (.base (.ADDI .x10 .x10 2048)) ∧
  instructionAt image (p + 24) = some (.base (.ADD .x7 .x7 .x10)) ∧
  instructionAt image (p + 28) = some (.base (.LUI .x28 128)) ∧
  instructionAt image (p + 32) = some (.base (.ADDI .x28 .x28 1296)) ∧
  instructionAt image (p + 36) = some (.base (.LD .x10 .x28 0)) ∧
  instructionAt image (p + 40) = some (.base (.LUI .x28 128)) ∧
  instructionAt image (p + 44) = some (.base (.ADDI .x28 .x28 1304)) ∧
  instructionAt image (p + 48) = some (.base (.LD .x11 .x28 0)) ∧
  instructionAt image (p + 52) = some (.base (.SD .x7 .x10 0)) ∧
  instructionAt image (p + 56) = some (.base (.SD .x7 .x11 8)) ∧
  instructionAt image (p + 60) = some (.base (.ADDI .x6 .x6 1)) ∧
  instructionAt image (p + 64) = some (.base (.LUI .x28 128)) ∧
  instructionAt image (p + 68) = some (.base (.ADDI .x28 .x28 1072)) ∧
  instructionAt image (p + 72) = some (.base (.SD .x28 .x6 0)) ∧
  instructionAt image (p + 76) = some (.base (.ADDI .x7 .x0 46)) ∧
  instructionAt image (p + 80) = some (.base (.BNE .x6 .x7 offset))

instance (image : Image) (p : Word) (offset : BitVec 13) : Decidable (Code image p offset) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))

def state (s : MachineState) (offset : BitVec 13) : MachineState :=
  let s := execInstrBr s (.LUI .x28 128)
  let s := execInstrBr s (.ADDI .x28 .x28 1072)
  let s := execInstrBr s (.LD .x6 .x28 0)
  let s := execInstrBr s (.SLLI .x7 .x6 4)
  let s := execInstrBr s (.LUI .x10 129)
  let s := execInstrBr s (.ADDI .x10 .x10 2048)
  let s := execInstrBr s (.ADD .x7 .x7 .x10)
  let s := execInstrBr s (.LUI .x28 128)
  let s := execInstrBr s (.ADDI .x28 .x28 1296)
  let s := execInstrBr s (.LD .x10 .x28 0)
  let s := execInstrBr s (.LUI .x28 128)
  let s := execInstrBr s (.ADDI .x28 .x28 1304)
  let s := execInstrBr s (.LD .x11 .x28 0)
  let s := execInstrBr s (.SD .x7 .x10 0)
  let s := execInstrBr s (.SD .x7 .x11 8)
  let s := execInstrBr s (.ADDI .x6 .x6 1)
  let s := execInstrBr s (.LUI .x28 128)
  let s := execInstrBr s (.ADDI .x28 .x28 1072)
  let s := execInstrBr s (.SD .x28 .x6 0)
  let s := execInstrBr s (.ADDI .x7 .x0 46)
  execInstrBr s (.BNE .x6 .x7 offset)

def address (s : MachineState) : Word := (s.getMem 0x80430 <<< 4) + 0x80800

theorem block (image : Image) (p : Word) (offset : BitVec 13) (code : Code image p offset)
    (s : MachineState) (pc : s.pc = p)
    (safe : accessValid (address s) 8 = true) (safeNext : accessValid (address s + 8) 8 = true) :
    OrdinarySteps image s 21 (state s offset) := by
  simp only [address] at safe safeNext
  obtain ⟨c0,c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,c20⟩ := code
  let s1 := execInstrBr s (.LUI .x28 128)
  let s2 := execInstrBr s1 (.ADDI .x28 .x28 1072)
  let s3 := execInstrBr s2 (.LD .x6 .x28 0)
  let s4 := execInstrBr s3 (.SLLI .x7 .x6 4)
  let s5 := execInstrBr s4 (.LUI .x10 129)
  let s6 := execInstrBr s5 (.ADDI .x10 .x10 2048)
  let s7 := execInstrBr s6 (.ADD .x7 .x7 .x10)
  let s8 := execInstrBr s7 (.LUI .x28 128)
  let s9 := execInstrBr s8 (.ADDI .x28 .x28 1296)
  let s10 := execInstrBr s9 (.LD .x10 .x28 0)
  let s11 := execInstrBr s10 (.LUI .x28 128)
  let s12 := execInstrBr s11 (.ADDI .x28 .x28 1304)
  let s13 := execInstrBr s12 (.LD .x11 .x28 0)
  let s14 := execInstrBr s13 (.SD .x7 .x10 0)
  let s15 := execInstrBr s14 (.SD .x7 .x11 8)
  let s16 := execInstrBr s15 (.ADDI .x6 .x6 1)
  let s17 := execInstrBr s16 (.LUI .x28 128)
  let s18 := execInstrBr s17 (.ADDI .x28 .x28 1072)
  let s19 := execInstrBr s18 (.SD .x28 .x6 0)
  let s20 := execInstrBr s19 (.ADDI .x7 .x0 46)
  let s21 := execInstrBr s20 (.BNE .x6 .x7 offset)
  apply OrdinarySteps.step s s1 _ (.base (.LUI .x28 128)) 20
  · have hp : s.pc = p + 0 := by simp [execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c0
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.ADDI .x28 .x28 1072)) 19
  · have hp : s1.pc = p + 4 := by simp [s1, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c1
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.LD .x6 .x28 0)) 18
  · have hp : s2.pc = p + 8 := by simp [s1, s2, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c2
  · simp [s1, s2, s3, ordinaryStep, memoryArgumentsValid, execInstrBr, signExtend12,
      accessValid,rangeValid,MEMORY_BYTES, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s3 s4 _ (.base (.SLLI .x7 .x6 4)) 17
  · have hp : s3.pc = p + 12 := by simp [s1, s2, s3, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c3
  · rfl
  apply OrdinarySteps.step s4 s5 _ (.base (.LUI .x10 129)) 16
  · have hp : s4.pc = p + 16 := by simp [s1, s2, s3, s4, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c4
  · rfl
  apply OrdinarySteps.step s5 s6 _ (.base (.ADDI .x10 .x10 2048)) 15
  · have hp : s5.pc = p + 20 := by simp [s1, s2, s3, s4, s5, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c5
  · rfl
  apply OrdinarySteps.step s6 s7 _ (.base (.ADD .x7 .x7 .x10)) 14
  · have hp : s6.pc = p + 24 := by simp [s1, s2, s3, s4, s5, s6, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c6
  · rfl
  apply OrdinarySteps.step s7 s8 _ (.base (.LUI .x28 128)) 13
  · have hp : s7.pc = p + 28 := by simp [s1, s2, s3, s4, s5, s6, s7, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c7
  · rfl
  apply OrdinarySteps.step s8 s9 _ (.base (.ADDI .x28 .x28 1296)) 12
  · have hp : s8.pc = p + 32 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c8
  · rfl
  apply OrdinarySteps.step s9 s10 _ (.base (.LD .x10 .x28 0)) 11
  · have hp : s9.pc = p + 36 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c9
  · simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, ordinaryStep, memoryArgumentsValid, execInstrBr, signExtend12,
      accessValid,rangeValid,MEMORY_BYTES, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s10 s11 _ (.base (.LUI .x28 128)) 10
  · have hp : s10.pc = p + 40 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c10
  · rfl
  apply OrdinarySteps.step s11 s12 _ (.base (.ADDI .x28 .x28 1304)) 9
  · have hp : s11.pc = p + 44 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c11
  · rfl
  apply OrdinarySteps.step s12 s13 _ (.base (.LD .x11 .x28 0)) 8
  · have hp : s12.pc = p + 48 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c12
  · simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, ordinaryStep, memoryArgumentsValid, execInstrBr, signExtend12,
      accessValid,rangeValid,MEMORY_BYTES, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s13 s14 _ (.base (.SD .x7 .x10 0)) 7
  · have hp : s13.pc = p + 52 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c13
  · simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, ordinaryStep, memoryArgumentsValid, execInstrBr, signExtend12,
      safe,safeNext, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
    exact safe
  apply OrdinarySteps.step s14 s15 _ (.base (.SD .x7 .x11 8)) 6
  · have hp : s14.pc = p + 56 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c14
  · simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, ordinaryStep, memoryArgumentsValid, execInstrBr, signExtend12,
      safe,safeNext, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
    exact safeNext
  apply OrdinarySteps.step s15 s16 _ (.base (.ADDI .x6 .x6 1)) 5
  · have hp : s15.pc = p + 60 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c15
  · rfl
  apply OrdinarySteps.step s16 s17 _ (.base (.LUI .x28 128)) 4
  · have hp : s16.pc = p + 64 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c16
  · rfl
  apply OrdinarySteps.step s17 s18 _ (.base (.ADDI .x28 .x28 1072)) 3
  · have hp : s17.pc = p + 68 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c17
  · rfl
  apply OrdinarySteps.step s18 s19 _ (.base (.SD .x28 .x6 0)) 2
  · have hp : s18.pc = p + 72 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c18
  · simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, ordinaryStep, memoryArgumentsValid, execInstrBr, signExtend12,
      accessValid,rangeValid,MEMORY_BYTES, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s19 s20 _ (.base (.ADDI .x7 .x0 46)) 1
  · have hp : s19.pc = p + 76 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c19
  · rfl
  apply OrdinarySteps.step s20 s21 _ (.base (.BNE .x6 .x7 offset)) 0
  · have hp : s20.pc = p + 80 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c20
  · rfl
  exact OrdinarySteps.refl _

theorem pc (s : MachineState) (offset : BitVec 13) :
    (state s offset).pc = if s.getMem 0x80430 + 1 = 46 then s.pc+84 else s.pc+80+signExtend13 offset := by
  simp [state,execInstrBr,signExtend12,MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,BitVec.add_assoc]

theorem mem (s : MachineState) (offset : BitVec 13) (a : Word) :
    (state s offset).getMem a = if a = 0x80430 then s.getMem 0x80430+1 else
      if a = address s+8 then s.getMem 0x80518 else
      if a = address s then s.getMem 0x80510 else s.getMem a := by
  simp [state,address,execInstrBr,signExtend12,MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  rfl

theorem stack (s : MachineState) (offset : BitVec 13) :
    (state s offset).getReg .x1 = s.getReg .x1 ∧ (state s offset).getReg .x2 = s.getReg .x2 := by
  simp [state,execInstrBr,MachineState.getReg_setReg_ne]

theorem keygen_code : Code keygen 0x14f4 (-832) := by decide


theorem address_eq (s : MachineState) (n : Nat) (chain : s.getMem 0x80430 = BitVec.ofNat 64 n) :
    address s = BitVec.ofNat 64 (0x80800+16*n) := by
  unfold address
  rw [chain,KeygenDomain.shift_ofNat]
  change BitVec.ofNat 64 (n*16) + BitVec.ofNat 64 0x80800 = _
  rw [← BitVec.ofNat_add]
  congr 1
  omega

theorem address_safe (s : MachineState) (n : Nat) (bound : n < 46)
    (chain : s.getMem 0x80430 = BitVec.ofNat 64 n) :
    accessValid (address s) 8 = true ∧ accessValid (address s+8) 8 = true := by
  rw [address_eq s n chain]
  have sum : BitVec.ofNat 64 (0x80800+16*n) + 8 = BitVec.ofNat 64 (0x80800+16*n+8) :=
    (BitVec.ofNat_add _ _).symm
  rw [sum]
  have small : 0x80800+16*n < 2^64 := by omega
  have smallNext : 0x80800+16*n+8 < 2^64 := by omega
  simp [accessValid,rangeValid,MEMORY_BYTES,BitVec.toNat_ofNat,Nat.mod_eq_of_lt small,
    Nat.mod_eq_of_lt smallNext]
  omega

end SigGolfCandidate.Hypertree.KeygenEndpoint
