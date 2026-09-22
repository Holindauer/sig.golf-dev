import SigGolfCandidate.Hypertree.KeygenDomain

namespace SigGolfCandidate.Hypertree.KeygenSavePublic

open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 OracleComp Keygen

set_option maxRecDepth 4096

set_option linter.unusedSimpArgs false

def Code (image : Image) (p : Word) : Prop :=
  instructionAt image (p + 0) = some (.base (.LUI .x28 128)) ∧
  instructionAt image (p + 4) = some (.base (.ADDI .x28 .x28 1064)) ∧
  instructionAt image (p + 8) = some (.base (.LD .x6 .x28 0)) ∧
  instructionAt image (p + 12) = some (.base (.SLLI .x6 .x6 4)) ∧
  instructionAt image (p + 16) = some (.base (.LUI .x7 128)) ∧
  instructionAt image (p + 20) = some (.base (.ADDI .x7 .x7 1312)) ∧
  instructionAt image (p + 24) = some (.base (.ADD .x7 .x7 .x6)) ∧
  instructionAt image (p + 28) = some (.base (.LUI .x28 128)) ∧
  instructionAt image (p + 32) = some (.base (.ADDI .x28 .x28 768)) ∧
  instructionAt image (p + 36) = some (.base (.LD .x10 .x28 0)) ∧
  instructionAt image (p + 40) = some (.base (.LUI .x28 128)) ∧
  instructionAt image (p + 44) = some (.base (.ADDI .x28 .x28 776)) ∧
  instructionAt image (p + 48) = some (.base (.LD .x11 .x28 0)) ∧
  instructionAt image (p + 52) = some (.base (.SD .x7 .x10 0)) ∧
  instructionAt image (p + 56) = some (.base (.SD .x7 .x11 8))

instance (image : Image) (p : Word) : Decidable (Code image p) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))

def state (s : MachineState) : MachineState :=
  let s := execInstrBr s (.LUI .x28 128)
  let s := execInstrBr s (.ADDI .x28 .x28 1064)
  let s := execInstrBr s (.LD .x6 .x28 0)
  let s := execInstrBr s (.SLLI .x6 .x6 4)
  let s := execInstrBr s (.LUI .x7 128)
  let s := execInstrBr s (.ADDI .x7 .x7 1312)
  let s := execInstrBr s (.ADD .x7 .x7 .x6)
  let s := execInstrBr s (.LUI .x28 128)
  let s := execInstrBr s (.ADDI .x28 .x28 768)
  let s := execInstrBr s (.LD .x10 .x28 0)
  let s := execInstrBr s (.LUI .x28 128)
  let s := execInstrBr s (.ADDI .x28 .x28 776)
  let s := execInstrBr s (.LD .x11 .x28 0)
  let s := execInstrBr s (.SD .x7 .x10 0)
  execInstrBr s (.SD .x7 .x11 8)

def address (s : MachineState) : Word := 0x80520 + (s.getMem 0x80428 <<< 4)

theorem block (image : Image) (p : Word) (code : Code image p)
    (s : MachineState) (pc : s.pc = p)
    (safe : accessValid (address s) 8 = true) (safeNext : accessValid (address s + 8) 8 = true) :
    OrdinarySteps image s 15 (state s) := by
  simp only [address] at safe safeNext
  obtain ⟨c0,c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14⟩ := code
  let s1 := execInstrBr s (.LUI .x28 128)
  let s2 := execInstrBr s1 (.ADDI .x28 .x28 1064)
  let s3 := execInstrBr s2 (.LD .x6 .x28 0)
  let s4 := execInstrBr s3 (.SLLI .x6 .x6 4)
  let s5 := execInstrBr s4 (.LUI .x7 128)
  let s6 := execInstrBr s5 (.ADDI .x7 .x7 1312)
  let s7 := execInstrBr s6 (.ADD .x7 .x7 .x6)
  let s8 := execInstrBr s7 (.LUI .x28 128)
  let s9 := execInstrBr s8 (.ADDI .x28 .x28 768)
  let s10 := execInstrBr s9 (.LD .x10 .x28 0)
  let s11 := execInstrBr s10 (.LUI .x28 128)
  let s12 := execInstrBr s11 (.ADDI .x28 .x28 776)
  let s13 := execInstrBr s12 (.LD .x11 .x28 0)
  let s14 := execInstrBr s13 (.SD .x7 .x10 0)
  let s15 := execInstrBr s14 (.SD .x7 .x11 8)
  apply OrdinarySteps.step s s1 _ (.base (.LUI .x28 128)) 14
  · have hp : s.pc = p + 0 := by simp [execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c0
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.ADDI .x28 .x28 1064)) 13
  · have hp : s1.pc = p + 4 := by simp [s1, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c1
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.LD .x6 .x28 0)) 12
  · have hp : s2.pc = p + 8 := by simp [s1, s2, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c2
  · simp [s1, s2, s3, ordinaryStep, memoryArgumentsValid, execInstrBr, signExtend12,
      accessValid,rangeValid,MEMORY_BYTES, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s3 s4 _ (.base (.SLLI .x6 .x6 4)) 11
  · have hp : s3.pc = p + 12 := by simp [s1, s2, s3, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c3
  · rfl
  apply OrdinarySteps.step s4 s5 _ (.base (.LUI .x7 128)) 10
  · have hp : s4.pc = p + 16 := by simp [s1, s2, s3, s4, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c4
  · rfl
  apply OrdinarySteps.step s5 s6 _ (.base (.ADDI .x7 .x7 1312)) 9
  · have hp : s5.pc = p + 20 := by simp [s1, s2, s3, s4, s5, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c5
  · rfl
  apply OrdinarySteps.step s6 s7 _ (.base (.ADD .x7 .x7 .x6)) 8
  · have hp : s6.pc = p + 24 := by simp [s1, s2, s3, s4, s5, s6, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c6
  · rfl
  apply OrdinarySteps.step s7 s8 _ (.base (.LUI .x28 128)) 7
  · have hp : s7.pc = p + 28 := by simp [s1, s2, s3, s4, s5, s6, s7, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c7
  · rfl
  apply OrdinarySteps.step s8 s9 _ (.base (.ADDI .x28 .x28 768)) 6
  · have hp : s8.pc = p + 32 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c8
  · rfl
  apply OrdinarySteps.step s9 s10 _ (.base (.LD .x10 .x28 0)) 5
  · have hp : s9.pc = p + 36 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c9
  · simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, ordinaryStep, memoryArgumentsValid, execInstrBr, signExtend12,
      accessValid,rangeValid,MEMORY_BYTES, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s10 s11 _ (.base (.LUI .x28 128)) 4
  · have hp : s10.pc = p + 40 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c10
  · rfl
  apply OrdinarySteps.step s11 s12 _ (.base (.ADDI .x28 .x28 776)) 3
  · have hp : s11.pc = p + 44 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c11
  · rfl
  apply OrdinarySteps.step s12 s13 _ (.base (.LD .x11 .x28 0)) 2
  · have hp : s12.pc = p + 48 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c12
  · simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, ordinaryStep, memoryArgumentsValid, execInstrBr, signExtend12,
      accessValid,rangeValid,MEMORY_BYTES, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s13 s14 _ (.base (.SD .x7 .x10 0)) 1
  · have hp : s13.pc = p + 52 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c13
  · simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, ordinaryStep, memoryArgumentsValid, execInstrBr, signExtend12,
      safe,safeNext, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
    exact safe
  apply OrdinarySteps.step s14 s15 _ (.base (.SD .x7 .x11 8)) 0
  · have hp : s14.pc = p + 56 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c14
  · simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, ordinaryStep, memoryArgumentsValid, execInstrBr, signExtend12,
      safe,safeNext, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
    exact safeNext
  exact OrdinarySteps.refl _

theorem pc (s : MachineState) : (state s).pc = s.pc+60 := by
  simp [state,execInstrBr,BitVec.add_assoc]

theorem mem (s : MachineState) (a : Word) :
    (state s).getMem a = if a = address s+8 then s.getMem 0x80308 else
      if a = address s then s.getMem 0x80300 else s.getMem a := by
  simp [state,address,execInstrBr,signExtend12,MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  rfl

theorem stack (s : MachineState) :
    (state s).getReg .x1 = s.getReg .x1 ∧ (state s).getReg .x2 = s.getReg .x2 := by
  simp [state,execInstrBr,MachineState.getReg_setReg_ne]


theorem safe (s : MachineState) (side : Bool)
    (leaf : s.getMem 0x80428 = BitVec.ofNat 64 (Reference.sideNumber side)) :
    accessValid (address s) 8 = true ∧ accessValid (address s+8) 8 = true := by
  rw [address,leaf]
  cases side <;> decide

def wordAddress (side : Bool) (i : Nat) : Word :=
  Signing.wordAddress (0x80520+16*Reference.sideNumber side) i

theorem content (s : MachineState) (side : Bool)
    (leaf : s.getMem 0x80428 = BitVec.ofNat 64 (Reference.sideNumber side)) (i : Fin 2) :
    (state s).getMem (wordAddress side i.val) = s.getMem (Signing.wordAddress 0x80300 i.val) := by
  rw [mem,address,leaf]
  cases side <;> fin_cases i <;> simp [wordAddress,Signing.wordAddress,Reference.sideNumber]

theorem frame (s : MachineState) (side : Bool)
    (leaf : s.getMem 0x80428 = BitVec.ofNat 64 (Reference.sideNumber side)) (a : Word)
    (outside : ∀ i : Fin 2, a ≠ wordAddress side i.val) : (state s).getMem a = s.getMem a := by
  have h0 : a ≠ address s := by
    rw [address,leaf]
    cases side <;> simpa [wordAddress,Signing.wordAddress,Reference.sideNumber] using outside 0
  have h1 : a ≠ address s+8 := by
    rw [address,leaf]
    cases side <;> simpa [wordAddress,Signing.wordAddress,Reference.sideNumber] using outside 1
  rw [mem,if_neg h1,if_neg h0]

theorem keygen_code : Code keygen 0x1614 := by decide

end SigGolfCandidate.Hypertree.KeygenSavePublic
