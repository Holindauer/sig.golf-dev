import SigGolfCandidate.Hypertree.SignRandomizer

namespace SigGolfCandidate.Hypertree.Signing
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 OracleComp Keygen
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false

def initializeState (s : MachineState) : MachineState :=
  let s := execInstrBr s (.ADDI .x6 .x0 1)
  let s := execInstrBr s (.LUI .x28 0x80)
  let s := execInstrBr s (.ADDI .x28 .x28 0x440)
  let s := execInstrBr s (.SD .x28 .x6 0)
  let s := execInstrBr s (.LUI .x6 0x20)
  let s := execInstrBr s (.ADDI .x6 .x6 0x80)
  let s := execInstrBr s (.LUI .x28 0x80)
  let s := execInstrBr s (.ADDI .x28 .x28 0x448)
  let s := execInstrBr s (.SD .x28 .x6 0)
  let s := execInstrBr s (.ADDI .x6 .x0 0x20)
  let s := execInstrBr s (.LUI .x7 0x80)
  let s := execInstrBr s (.ADDI .x7 .x7 0x20)
  execInstrBr s (.ADDI .x10 .x0 4)

theorem initializeState_block (s : MachineState) (pc : s.pc = 0x1000) :
    OrdinarySteps sign s 13 (initializeState s) := by
  let s1 := execInstrBr s (.ADDI .x6 .x0 1)
  let s2 := execInstrBr s1 (.LUI .x28 0x80)
  let s3 := execInstrBr s2 (.ADDI .x28 .x28 0x440)
  let s4 := execInstrBr s3 (.SD .x28 .x6 0)
  let s5 := execInstrBr s4 (.LUI .x6 0x20)
  let s6 := execInstrBr s5 (.ADDI .x6 .x6 0x80)
  let s7 := execInstrBr s6 (.LUI .x28 0x80)
  let s8 := execInstrBr s7 (.ADDI .x28 .x28 0x448)
  let s9 := execInstrBr s8 (.SD .x28 .x6 0)
  let s10 := execInstrBr s9 (.ADDI .x6 .x0 0x20)
  let s11 := execInstrBr s10 (.LUI .x7 0x80)
  let s12 := execInstrBr s11 (.ADDI .x7 .x7 0x20)
  let s13 := execInstrBr s12 (.ADDI .x10 .x0 4)
  apply OrdinarySteps.step s s1 _ (.base (.ADDI .x6 .x0 1)) 12
  · have hp : s.pc = 0x1000 := by simp [execInstrBr, pc]
    simp only [fetch, hp]; decide
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.LUI .x28 0x80)) 11
  · have hp : s1.pc = 0x1004 := by simp [s1, execInstrBr, pc]
    simp only [fetch, hp]; decide
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.ADDI .x28 .x28 0x440)) 10
  · have hp : s2.pc = 0x1008 := by simp [s1, s2, execInstrBr, pc]
    simp only [fetch, hp]; decide
  · rfl
  apply OrdinarySteps.step s3 s4 _ (.base (.SD .x28 .x6 0)) 9
  · have hp : s3.pc = 0x100c := by simp [s1, s2, s3, execInstrBr, pc]
    simp only [fetch, hp]; decide
  · simp [s1, s2, s3, s4, ordinaryStep, memoryArgumentsValid, execInstrBr, signExtend12, accessValid, rangeValid, MEMORY_BYTES, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s4 s5 _ (.base (.LUI .x6 0x20)) 8
  · have hp : s4.pc = 0x1010 := by simp [s1, s2, s3, s4, execInstrBr, pc]
    simp only [fetch, hp]; decide
  · rfl
  apply OrdinarySteps.step s5 s6 _ (.base (.ADDI .x6 .x6 0x80)) 7
  · have hp : s5.pc = 0x1014 := by simp [s1, s2, s3, s4, s5, execInstrBr, pc]
    simp only [fetch, hp]; decide
  · rfl
  apply OrdinarySteps.step s6 s7 _ (.base (.LUI .x28 0x80)) 6
  · have hp : s6.pc = 0x1018 := by simp [s1, s2, s3, s4, s5, s6, execInstrBr, pc]
    simp only [fetch, hp]; decide
  · rfl
  apply OrdinarySteps.step s7 s8 _ (.base (.ADDI .x28 .x28 0x448)) 5
  · have hp : s7.pc = 0x101c := by simp [s1, s2, s3, s4, s5, s6, s7, execInstrBr, pc]
    simp only [fetch, hp]; decide
  · rfl
  apply OrdinarySteps.step s8 s9 _ (.base (.SD .x28 .x6 0)) 4
  · have hp : s8.pc = 0x1020 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, execInstrBr, pc]
    simp only [fetch, hp]; decide
  · simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, ordinaryStep, memoryArgumentsValid, execInstrBr, signExtend12, accessValid, rangeValid, MEMORY_BYTES, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s9 s10 _ (.base (.ADDI .x6 .x0 0x20)) 3
  · have hp : s9.pc = 0x1024 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, execInstrBr, pc]
    simp only [fetch, hp]; decide
  · rfl
  apply OrdinarySteps.step s10 s11 _ (.base (.LUI .x7 0x80)) 2
  · have hp : s10.pc = 0x1028 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, execInstrBr, pc]
    simp only [fetch, hp]; decide
  · rfl
  apply OrdinarySteps.step s11 s12 _ (.base (.ADDI .x7 .x7 0x20)) 1
  · have hp : s11.pc = 0x102c := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, execInstrBr, pc]
    simp only [fetch, hp]; decide
  · rfl
  apply OrdinarySteps.step s12 s13 _ (.base (.ADDI .x10 .x0 4)) 0
  · have hp : s12.pc = 0x1030 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, execInstrBr, pc]
    simp only [fetch, hp]; decide
  · rfl
  exact OrdinarySteps.refl _

def messageCopyState (s : MachineState) : MachineState :=
  let s := execInstrBr s (.ADDI .x6 .x0 0)
  let s := execInstrBr s (.LUI .x7 0x80)
  let s := execInstrBr s (.ADDI .x7 .x7 0x40)
  execInstrBr s (.ADDI .x10 .x0 4)

theorem messageCopyState_block (s : MachineState) (pc : s.pc = 0x104c) :
    OrdinarySteps sign s 4 (messageCopyState s) := by
  let s1 := execInstrBr s (.ADDI .x6 .x0 0)
  let s2 := execInstrBr s1 (.LUI .x7 0x80)
  let s3 := execInstrBr s2 (.ADDI .x7 .x7 0x40)
  let s4 := execInstrBr s3 (.ADDI .x10 .x0 4)
  apply OrdinarySteps.step s s1 _ (.base (.ADDI .x6 .x0 0)) 3
  · have hp : s.pc = 0x104c := by simp [execInstrBr, pc]
    simp only [fetch, hp]; decide
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.LUI .x7 0x80)) 2
  · have hp : s1.pc = 0x1050 := by simp [s1, execInstrBr, pc]
    simp only [fetch, hp]; decide
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.ADDI .x7 .x7 0x40)) 1
  · have hp : s2.pc = 0x1054 := by simp [s1, s2, execInstrBr, pc]
    simp only [fetch, hp]; decide
  · rfl
  apply OrdinarySteps.step s3 s4 _ (.base (.ADDI .x10 .x0 4)) 0
  · have hp : s3.pc = 0x1058 := by simp [s1, s2, s3, execInstrBr, pc]
    simp only [fetch, hp]; decide
  · rfl
  exact OrdinarySteps.refl _

def randomizerHeaderState (s : MachineState) : MachineState :=
  let s := execInstrBr s (.ADDI .x10 .x0 6)
  let s := execInstrBr s (.LUI .x28 0x80)
  let s := execInstrBr s (.ADDI .x28 .x28 0)
  let s := execInstrBr s (.SD .x28 .x10 0)
  let s := execInstrBr s (.ADDI .x11 .x0 0)
  let s := execInstrBr s (.LUI .x28 0x80)
  let s := execInstrBr s (.ADDI .x28 .x28 8)
  let s := execInstrBr s (.SD .x28 .x11 0)
  let s := execInstrBr s (.ADDI .x11 .x0 0)
  let s := execInstrBr s (.LUI .x28 0x80)
  let s := execInstrBr s (.ADDI .x28 .x28 16)
  let s := execInstrBr s (.SD .x28 .x11 0)
  let s := execInstrBr s (.ADDI .x11 .x0 0)
  let s := execInstrBr s (.LUI .x28 0x80)
  let s := execInstrBr s (.ADDI .x28 .x28 24)
  execInstrBr s (.SD .x28 .x11 0)

theorem randomizerHeaderState_block (s : MachineState) (pc : s.pc = 0x1074) :
    OrdinarySteps sign s 16 (randomizerHeaderState s) := by
  let s1 := execInstrBr s (.ADDI .x10 .x0 6)
  let s2 := execInstrBr s1 (.LUI .x28 0x80)
  let s3 := execInstrBr s2 (.ADDI .x28 .x28 0)
  let s4 := execInstrBr s3 (.SD .x28 .x10 0)
  let s5 := execInstrBr s4 (.ADDI .x11 .x0 0)
  let s6 := execInstrBr s5 (.LUI .x28 0x80)
  let s7 := execInstrBr s6 (.ADDI .x28 .x28 8)
  let s8 := execInstrBr s7 (.SD .x28 .x11 0)
  let s9 := execInstrBr s8 (.ADDI .x11 .x0 0)
  let s10 := execInstrBr s9 (.LUI .x28 0x80)
  let s11 := execInstrBr s10 (.ADDI .x28 .x28 16)
  let s12 := execInstrBr s11 (.SD .x28 .x11 0)
  let s13 := execInstrBr s12 (.ADDI .x11 .x0 0)
  let s14 := execInstrBr s13 (.LUI .x28 0x80)
  let s15 := execInstrBr s14 (.ADDI .x28 .x28 24)
  let s16 := execInstrBr s15 (.SD .x28 .x11 0)
  apply OrdinarySteps.step s s1 _ (.base (.ADDI .x10 .x0 6)) 15
  · have hp : s.pc = 0x1074 := by simp [execInstrBr, pc]
    simp only [fetch, hp]; decide
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.LUI .x28 0x80)) 14
  · have hp : s1.pc = 0x1078 := by simp [s1, execInstrBr, pc]
    simp only [fetch, hp]; decide
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.ADDI .x28 .x28 0)) 13
  · have hp : s2.pc = 0x107c := by simp [s1, s2, execInstrBr, pc]
    simp only [fetch, hp]; decide
  · rfl
  apply OrdinarySteps.step s3 s4 _ (.base (.SD .x28 .x10 0)) 12
  · have hp : s3.pc = 0x1080 := by simp [s1, s2, s3, execInstrBr, pc]
    simp only [fetch, hp]; decide
  · simp [s1, s2, s3, s4, ordinaryStep, memoryArgumentsValid, execInstrBr, signExtend12, accessValid, rangeValid, MEMORY_BYTES, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s4 s5 _ (.base (.ADDI .x11 .x0 0)) 11
  · have hp : s4.pc = 0x1084 := by simp [s1, s2, s3, s4, execInstrBr, pc]
    simp only [fetch, hp]; decide
  · rfl
  apply OrdinarySteps.step s5 s6 _ (.base (.LUI .x28 0x80)) 10
  · have hp : s5.pc = 0x1088 := by simp [s1, s2, s3, s4, s5, execInstrBr, pc]
    simp only [fetch, hp]; decide
  · rfl
  apply OrdinarySteps.step s6 s7 _ (.base (.ADDI .x28 .x28 8)) 9
  · have hp : s6.pc = 0x108c := by simp [s1, s2, s3, s4, s5, s6, execInstrBr, pc]
    simp only [fetch, hp]; decide
  · rfl
  apply OrdinarySteps.step s7 s8 _ (.base (.SD .x28 .x11 0)) 8
  · have hp : s7.pc = 0x1090 := by simp [s1, s2, s3, s4, s5, s6, s7, execInstrBr, pc]
    simp only [fetch, hp]; decide
  · simp [s1, s2, s3, s4, s5, s6, s7, s8, ordinaryStep, memoryArgumentsValid, execInstrBr, signExtend12, accessValid, rangeValid, MEMORY_BYTES, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s8 s9 _ (.base (.ADDI .x11 .x0 0)) 7
  · have hp : s8.pc = 0x1094 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, execInstrBr, pc]
    simp only [fetch, hp]; decide
  · rfl
  apply OrdinarySteps.step s9 s10 _ (.base (.LUI .x28 0x80)) 6
  · have hp : s9.pc = 0x1098 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, execInstrBr, pc]
    simp only [fetch, hp]; decide
  · rfl
  apply OrdinarySteps.step s10 s11 _ (.base (.ADDI .x28 .x28 16)) 5
  · have hp : s10.pc = 0x109c := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, execInstrBr, pc]
    simp only [fetch, hp]; decide
  · rfl
  apply OrdinarySteps.step s11 s12 _ (.base (.SD .x28 .x11 0)) 4
  · have hp : s11.pc = 0x10a0 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, execInstrBr, pc]
    simp only [fetch, hp]; decide
  · simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, ordinaryStep, memoryArgumentsValid, execInstrBr, signExtend12, accessValid, rangeValid, MEMORY_BYTES, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s12 s13 _ (.base (.ADDI .x11 .x0 0)) 3
  · have hp : s12.pc = 0x10a4 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, execInstrBr, pc]
    simp only [fetch, hp]; decide
  · rfl
  apply OrdinarySteps.step s13 s14 _ (.base (.LUI .x28 0x80)) 2
  · have hp : s13.pc = 0x10a8 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, execInstrBr, pc]
    simp only [fetch, hp]; decide
  · rfl
  apply OrdinarySteps.step s14 s15 _ (.base (.ADDI .x28 .x28 24)) 1
  · have hp : s14.pc = 0x10ac := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, execInstrBr, pc]
    simp only [fetch, hp]; decide
  · rfl
  apply OrdinarySteps.step s15 s16 _ (.base (.SD .x28 .x11 0)) 0
  · have hp : s15.pc = 0x10b0 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, execInstrBr, pc]
    simp only [fetch, hp]; decide
  · simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, ordinaryStep, memoryArgumentsValid, execInstrBr, signExtend12, accessValid, rangeValid, MEMORY_BYTES, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  exact OrdinarySteps.refl _

theorem initializeState_mem (s : MachineState) (a : Word) :
    (initializeState s).getMem a =
      if a = 0x80448 then 0x20080 else if a = 0x80440 then 1 else s.getMem a := by
  simp [initializeState, execInstrBr, signExtend12, Expansion.mem_setMem,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]

theorem initializeState_invariant (s : MachineState) (pc : s.pc = 0x1000) :
    CopyInvariant 0x1034 0x20 0x80020 4 4 (initializeState s) := by
  simp [CopyInvariant, initializeState, execInstrBr, signExtend12, pc,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]

theorem messageCopyState_mem (s : MachineState) (a : Word) :
    (messageCopyState s).getMem a = s.getMem a := by simp [messageCopyState, execInstrBr]

theorem messageCopyState_invariant (s : MachineState) (pc : s.pc = 0x104c) :
    CopyInvariant 0x105c 0 0x80040 4 4 (messageCopyState s) := by
  simp [CopyInvariant, messageCopyState, execInstrBr, signExtend12, pc,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]

theorem randomizerHeaderState_pc (s : MachineState) :
    (randomizerHeaderState s).pc = s.pc + 64 := by
  simp [randomizerHeaderState, execInstrBr, BitVec.add_assoc]

theorem randomizerHeaderState_mem (s : MachineState) (a : Word) :
    (randomizerHeaderState s).getMem a =
      if a = 0x80018 then 0 else if a = 0x80010 then 0 else
        if a = 0x80008 then 0 else if a = 0x80000 then 6 else s.getMem a := by
  simp [randomizerHeaderState, execInstrBr, signExtend12, Expansion.mem_setMem,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]

/-- The twelve words of the precise 96-byte tag6/secret key/message query. -/
def randomizerInputWord (s : MachineState) (i : Fin 12) : Word :=
  if i.val = 0 then 6 else if i.val < 4 then 0 else
    if i.val < 8 then s.getMem (wordAddress 0x20 (i.val - 4))
    else s.getMem (wordAddress 0 (i.val - 8))

/-- A mathematical address outside a destination interval cannot alias its words. -/
theorem outside_copy_word (address base count i : Nat)
    (ha : address < 2 ^ 64) (hb : base + 8 * count ≤ MEMORY_BYTES)
    (hi : i < count) (outside : address < base ∨ base + 8 * count ≤ address) :
    BitVec.ofNat 64 address ≠ wordAddress base i := by
  intro eq
  have values := congrArg BitVec.toNat eq
  have hbi : base + 8 * i < 2 ^ 64 := by simp only [MEMORY_BYTES] at hb; omega
  change address % 2 ^ 64 = (base + 8 * i) % 2 ^ 64 at values
  rw [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hbi] at values
  omega

/-- Real bytecode preparation of the randomizer oracle input for arbitrary initial memory. -/
theorem randomizer_prepare (s : MachineState) (pc : s.pc = 0x1000) :
    ∃ ready, OrdinarySteps sign s 81 ready ∧ ready.pc = 0x10b4 ∧
      (∀ i : Fin 12, ready.getMem (wordAddress 0x80000 i.val) = randomizerInputWord s i) ∧
      (∀ a, a ≠ 0x80440 → a ≠ 0x80448 →
        (∀ i : Fin 12, a ≠ wordAddress 0x80000 i.val) → ready.getMem a = s.getMem a) := by
  have secretKeyCode : CopyCode sign 0x1034 := by decide
  have msgCode : CopyCode sign 0x105c := by decide
  obtain ⟨secretKey, secretKeyLoop, secretKeyInv, secretKeyOutput, secretKeyFrame⟩ := copy_all sign 0x1034 secretKeyCode
    0x20 0x80020 4 (initializeState s) (initializeState_invariant s pc)
    (by decide) (by decide) (by decide) (by decide) (by decide)
  have secretKeypc : secretKey.pc = 0x104c := by simpa [CopyInvariant] using secretKeyInv.2.2.1
  obtain ⟨msg, msgLoop, msgInv, msgOutput, msgFrame⟩ := copy_all sign 0x105c msgCode
    0 0x80040 4 (messageCopyState secretKey) (messageCopyState_invariant secretKey secretKeypc)
    (by decide) (by decide) (by decide) (by decide) (by decide)
  have msgpc : msg.pc = 0x1074 := by simpa [CopyInvariant] using msgInv.2.2.1
  have secretKeyPreserved (i : Fin 4) :
      msg.getMem (wordAddress 0x80020 i.val) = s.getMem (wordAddress 0x20 i.val) := by
    rw [msgFrame, messageCopyState_mem, secretKeyOutput i.val i.isLt, initializeState_mem]
    · fin_cases i <;> simp [wordAddress]
    · intro j hj
      apply outside_copy_word (0x80020 + 8 * i.val) 0x80040 4 j
      · have := i.isLt; omega
      · decide
      · exact hj
      · have := i.isLt; left; omega
  have messageCopied (i : Fin 4) :
      msg.getMem (wordAddress 0x80040 i.val) = s.getMem (wordAddress 0 i.val) := by
    rw [msgOutput i.val i.isLt, messageCopyState_mem, secretKeyFrame, initializeState_mem]
    · fin_cases i <;> simp [wordAddress]
    · intro j hj
      apply outside_copy_word (0 + 8 * i.val) 0x80020 4 j
      · have := i.isLt; omega
      · decide
      · exact hj
      · have := i.isLt; left; omega
  refine ⟨randomizerHeaderState msg, ?_, ?_, ?_, ?_⟩
  · exact ordinary_trans sign s _ _ 37 44
      (ordinary_trans sign s _ _ 13 24 (initializeState_block s pc) secretKeyLoop)
      (ordinary_trans sign secretKey _ _ 4 40 (messageCopyState_block secretKey secretKeypc)
        (ordinary_trans sign (messageCopyState secretKey) _ _ 24 16 msgLoop (randomizerHeaderState_block msg msgpc)))
  · simp [randomizerHeaderState_pc, msgpc]
  · intro i
    fin_cases i <;> simp only [randomizerHeaderState_mem]
    all_goals simp only [wordAddress, randomizerInputWord, Fin.val_zero, Fin.val_one, Nat.mul_zero,
      Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT, Nat.reduceEqDiff,
      ↓reduceIte]
    all_goals first | rfl | simpa [wordAddress] using secretKeyPreserved 0 | simpa [wordAddress] using secretKeyPreserved 1 |
      simpa [wordAddress] using secretKeyPreserved 2 | simpa [wordAddress] using secretKeyPreserved 3 |
      simpa [wordAddress] using messageCopied 0 | simpa [wordAddress] using messageCopied 1 |
      simpa [wordAddress] using messageCopied 2 | simpa [wordAddress] using messageCopied 3

  · intro a mode pointer outside
    have h0 : a ≠ 0x80000 := by simpa [wordAddress] using outside 0
    have h1 : a ≠ 0x80008 := by simpa [wordAddress] using outside 1
    have h2 : a ≠ 0x80010 := by simpa [wordAddress] using outside 2
    have h3 : a ≠ 0x80018 := by simpa [wordAddress] using outside 3
    rw [randomizerHeaderState_mem, if_neg h3, if_neg h2, if_neg h1, if_neg h0,
      msgFrame, messageCopyState_mem, secretKeyFrame, initializeState_mem, if_neg pointer, if_neg mode]
    · intro j hj
      have eq : wordAddress 0x80020 j = wordAddress 0x80000 (j + 4) := by
        unfold wordAddress; congr 1; omega
      rw [eq]
      exact outside ⟨j + 4, by omega⟩
    · intro j hj
      have eq : wordAddress 0x80040 j = wordAddress 0x80000 (j + 8) := by
        unfold wordAddress; congr 1; omega
      rw [eq]
      exact outside ⟨j + 8, by omega⟩

/-- info: 'SigGolfCandidate.Hypertree.Signing.randomizer_prepare' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms randomizer_prepare

/-- From the actual entry point through the randomized signature prefix, with a
checked oracle query buffer and exact costs. -/
theorem entry_randomizer_trace (hash : Hash) (s : MachineState) (pc : s.pc = 0x1000) :
    ∃ ready final, Trace hash sign s 117 132 1 2 final ∧ final.pc = 0x10fc ∧
      (∀ i : Fin 12, ready.getMem (wordAddress 0x80000 i.val) = randomizerInputWord s i) ∧
      (∀ i : Fin 4, final.getMem (wordAddress 0x20060 i.val) =
        (hash (hashInput (randomizerHashState ready))).extractLsb' (64 * i.val) 64) := by
  obtain ⟨ready, prepared, readypc, words, _⟩ := randomizer_prepare s pc
  obtain ⟨final, trace, finalpc, output⟩ := randomizer_trace hash ready readypc
  exact ⟨ready, final, prepared.trace.trans trace, finalpc, words, output⟩

/-- info: 'SigGolfCandidate.Hypertree.Signing.entry_randomizer_trace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms entry_randomizer_trace

end SigGolfCandidate.Hypertree.Signing
