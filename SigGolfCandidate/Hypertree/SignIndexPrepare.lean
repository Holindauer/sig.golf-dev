import SigGolfCandidate.Hypertree.SignIndex

namespace SigGolfCandidate.Hypertree.Signing
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 OracleComp Keygen
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false

def pkCopyState (s : MachineState) : MachineState :=
  let s := execInstrBr s (.ADDI .x6 .x0 0x40)
  let s := execInstrBr s (.LUI .x7 0x80)
  let s := execInstrBr s (.ADDI .x7 .x7 0x20)
  execInstrBr s (.ADDI .x10 .x0 2)

theorem pkCopyState_block (s : MachineState) (pc : s.pc = 0x10fc) :
    OrdinarySteps sign s 4 (pkCopyState s) := by
  let s1 := execInstrBr s (.ADDI .x6 .x0 0x40)
  let s2 := execInstrBr s1 (.LUI .x7 0x80)
  let s3 := execInstrBr s2 (.ADDI .x7 .x7 0x20)
  let s4 := execInstrBr s3 (.ADDI .x10 .x0 2)
  apply OrdinarySteps.step s s1 _ (.base (.ADDI .x6 .x0 0x40)) 3
  · have hp : s.pc = 0x10fc := by simp [execInstrBr, pc]
    simp only [fetch, hp]; decide
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.LUI .x7 0x80)) 2
  · have hp : s1.pc = 0x1100 := by simp [s1, execInstrBr, pc]
    simp only [fetch, hp]; decide
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.ADDI .x7 .x7 0x20)) 1
  · have hp : s2.pc = 0x1104 := by simp [s1, s2, execInstrBr, pc]
    simp only [fetch, hp]; decide
  · rfl
  apply OrdinarySteps.step s3 s4 _ (.base (.ADDI .x10 .x0 2)) 0
  · have hp : s3.pc = 0x1108 := by simp [s1, s2, s3, execInstrBr, pc]
    simp only [fetch, hp]; decide
  · rfl
  exact OrdinarySteps.refl _

def indexMessageCopyState (s : MachineState) : MachineState :=
  let s := execInstrBr s (.ADDI .x6 .x0 0)
  let s := execInstrBr s (.LUI .x7 0x80)
  let s := execInstrBr s (.ADDI .x7 .x7 0x30)
  execInstrBr s (.ADDI .x10 .x0 4)

theorem indexMessageCopyState_block (s : MachineState) (pc : s.pc = 0x1124) :
    OrdinarySteps sign s 4 (indexMessageCopyState s) := by
  let s1 := execInstrBr s (.ADDI .x6 .x0 0)
  let s2 := execInstrBr s1 (.LUI .x7 0x80)
  let s3 := execInstrBr s2 (.ADDI .x7 .x7 0x30)
  let s4 := execInstrBr s3 (.ADDI .x10 .x0 4)
  apply OrdinarySteps.step s s1 _ (.base (.ADDI .x6 .x0 0)) 3
  · have hp : s.pc = 0x1124 := by simp [execInstrBr, pc]
    simp only [fetch, hp]; decide
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.LUI .x7 0x80)) 2
  · have hp : s1.pc = 0x1128 := by simp [s1, execInstrBr, pc]
    simp only [fetch, hp]; decide
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.ADDI .x7 .x7 0x30)) 1
  · have hp : s2.pc = 0x112c := by simp [s1, s2, execInstrBr, pc]
    simp only [fetch, hp]; decide
  · rfl
  apply OrdinarySteps.step s3 s4 _ (.base (.ADDI .x10 .x0 4)) 0
  · have hp : s3.pc = 0x1130 := by simp [s1, s2, s3, execInstrBr, pc]
    simp only [fetch, hp]; decide
  · rfl
  exact OrdinarySteps.refl _

def inputRandomizerCopyState (s : MachineState) : MachineState :=
  let s := execInstrBr s (.LUI .x6 0x20)
  let s := execInstrBr s (.ADDI .x6 .x6 0x60)
  let s := execInstrBr s (.LUI .x7 0x80)
  let s := execInstrBr s (.ADDI .x7 .x7 0x50)
  execInstrBr s (.ADDI .x10 .x0 4)

theorem inputRandomizerCopyState_block (s : MachineState) (pc : s.pc = 0x114c) :
    OrdinarySteps sign s 5 (inputRandomizerCopyState s) := by
  let s1 := execInstrBr s (.LUI .x6 0x20)
  let s2 := execInstrBr s1 (.ADDI .x6 .x6 0x60)
  let s3 := execInstrBr s2 (.LUI .x7 0x80)
  let s4 := execInstrBr s3 (.ADDI .x7 .x7 0x50)
  let s5 := execInstrBr s4 (.ADDI .x10 .x0 4)
  apply OrdinarySteps.step s s1 _ (.base (.LUI .x6 0x20)) 4
  · have hp : s.pc = 0x114c := by simp [execInstrBr, pc]
    simp only [fetch, hp]; decide
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.ADDI .x6 .x6 0x60)) 3
  · have hp : s1.pc = 0x1150 := by simp [s1, execInstrBr, pc]
    simp only [fetch, hp]; decide
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.LUI .x7 0x80)) 2
  · have hp : s2.pc = 0x1154 := by simp [s1, s2, execInstrBr, pc]
    simp only [fetch, hp]; decide
  · rfl
  apply OrdinarySteps.step s3 s4 _ (.base (.ADDI .x7 .x7 0x50)) 1
  · have hp : s3.pc = 0x1158 := by simp [s1, s2, s3, execInstrBr, pc]
    simp only [fetch, hp]; decide
  · rfl
  apply OrdinarySteps.step s4 s5 _ (.base (.ADDI .x10 .x0 4)) 0
  · have hp : s4.pc = 0x115c := by simp [s1, s2, s3, s4, execInstrBr, pc]
    simp only [fetch, hp]; decide
  · rfl
  exact OrdinarySteps.refl _

def indexHeaderState (s : MachineState) : MachineState :=
  let s := execInstrBr s (.ADDI .x10 .x0 5)
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

theorem indexHeaderState_block (s : MachineState) (pc : s.pc = 0x1178) :
    OrdinarySteps sign s 16 (indexHeaderState s) := by
  let s1 := execInstrBr s (.ADDI .x10 .x0 5)
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
  apply OrdinarySteps.step s s1 _ (.base (.ADDI .x10 .x0 5)) 15
  · have hp : s.pc = 0x1178 := by simp [execInstrBr, pc]
    simp only [fetch, hp]; decide
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.LUI .x28 0x80)) 14
  · have hp : s1.pc = 0x117c := by simp [s1, execInstrBr, pc]
    simp only [fetch, hp]; decide
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.ADDI .x28 .x28 0)) 13
  · have hp : s2.pc = 0x1180 := by simp [s1, s2, execInstrBr, pc]
    simp only [fetch, hp]; decide
  · rfl
  apply OrdinarySteps.step s3 s4 _ (.base (.SD .x28 .x10 0)) 12
  · have hp : s3.pc = 0x1184 := by simp [s1, s2, s3, execInstrBr, pc]
    simp only [fetch, hp]; decide
  · simp [s1, s2, s3, s4, ordinaryStep, memoryArgumentsValid, execInstrBr, signExtend12, accessValid, rangeValid, MEMORY_BYTES, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s4 s5 _ (.base (.ADDI .x11 .x0 0)) 11
  · have hp : s4.pc = 0x1188 := by simp [s1, s2, s3, s4, execInstrBr, pc]
    simp only [fetch, hp]; decide
  · rfl
  apply OrdinarySteps.step s5 s6 _ (.base (.LUI .x28 0x80)) 10
  · have hp : s5.pc = 0x118c := by simp [s1, s2, s3, s4, s5, execInstrBr, pc]
    simp only [fetch, hp]; decide
  · rfl
  apply OrdinarySteps.step s6 s7 _ (.base (.ADDI .x28 .x28 8)) 9
  · have hp : s6.pc = 0x1190 := by simp [s1, s2, s3, s4, s5, s6, execInstrBr, pc]
    simp only [fetch, hp]; decide
  · rfl
  apply OrdinarySteps.step s7 s8 _ (.base (.SD .x28 .x11 0)) 8
  · have hp : s7.pc = 0x1194 := by simp [s1, s2, s3, s4, s5, s6, s7, execInstrBr, pc]
    simp only [fetch, hp]; decide
  · simp [s1, s2, s3, s4, s5, s6, s7, s8, ordinaryStep, memoryArgumentsValid, execInstrBr, signExtend12, accessValid, rangeValid, MEMORY_BYTES, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s8 s9 _ (.base (.ADDI .x11 .x0 0)) 7
  · have hp : s8.pc = 0x1198 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, execInstrBr, pc]
    simp only [fetch, hp]; decide
  · rfl
  apply OrdinarySteps.step s9 s10 _ (.base (.LUI .x28 0x80)) 6
  · have hp : s9.pc = 0x119c := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, execInstrBr, pc]
    simp only [fetch, hp]; decide
  · rfl
  apply OrdinarySteps.step s10 s11 _ (.base (.ADDI .x28 .x28 16)) 5
  · have hp : s10.pc = 0x11a0 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, execInstrBr, pc]
    simp only [fetch, hp]; decide
  · rfl
  apply OrdinarySteps.step s11 s12 _ (.base (.SD .x28 .x11 0)) 4
  · have hp : s11.pc = 0x11a4 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, execInstrBr, pc]
    simp only [fetch, hp]; decide
  · simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, ordinaryStep, memoryArgumentsValid, execInstrBr, signExtend12, accessValid, rangeValid, MEMORY_BYTES, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s12 s13 _ (.base (.ADDI .x11 .x0 0)) 3
  · have hp : s12.pc = 0x11a8 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, execInstrBr, pc]
    simp only [fetch, hp]; decide
  · rfl
  apply OrdinarySteps.step s13 s14 _ (.base (.LUI .x28 0x80)) 2
  · have hp : s13.pc = 0x11ac := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, execInstrBr, pc]
    simp only [fetch, hp]; decide
  · rfl
  apply OrdinarySteps.step s14 s15 _ (.base (.ADDI .x28 .x28 24)) 1
  · have hp : s14.pc = 0x11b0 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, execInstrBr, pc]
    simp only [fetch, hp]; decide
  · rfl
  apply OrdinarySteps.step s15 s16 _ (.base (.SD .x28 .x11 0)) 0
  · have hp : s15.pc = 0x11b4 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, execInstrBr, pc]
    simp only [fetch, hp]; decide
  · simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, ordinaryStep, memoryArgumentsValid, execInstrBr, signExtend12, accessValid, rangeValid, MEMORY_BYTES, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  exact OrdinarySteps.refl _

theorem pkCopyState_mem (s : MachineState) (a : Word) :
    (pkCopyState s).getMem a = s.getMem a := by simp [pkCopyState, execInstrBr]

theorem pkCopyState_invariant (s : MachineState) (pc : s.pc = 0x10fc) :
    CopyInvariant 0x110c 0x40 0x80020 2 2 (pkCopyState s) := by
  simp [CopyInvariant, pkCopyState, execInstrBr, signExtend12, pc,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]

theorem indexMessageCopyState_mem (s : MachineState) (a : Word) :
    (indexMessageCopyState s).getMem a = s.getMem a := by simp [indexMessageCopyState, execInstrBr]

theorem indexMessageCopyState_invariant (s : MachineState) (pc : s.pc = 0x1124) :
    CopyInvariant 0x1134 0x0 0x80030 4 4 (indexMessageCopyState s) := by
  simp [CopyInvariant, indexMessageCopyState, execInstrBr, signExtend12, pc,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]

theorem inputRandomizerCopyState_mem (s : MachineState) (a : Word) :
    (inputRandomizerCopyState s).getMem a = s.getMem a := by simp [inputRandomizerCopyState, execInstrBr]

theorem inputRandomizerCopyState_invariant (s : MachineState) (pc : s.pc = 0x114c) :
    CopyInvariant 0x1160 0x20060 0x80050 4 4 (inputRandomizerCopyState s) := by
  simp [CopyInvariant, inputRandomizerCopyState, execInstrBr, signExtend12, pc,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]

theorem indexHeaderState_pc (s : MachineState) : (indexHeaderState s).pc = s.pc + 64 := by
  simp [indexHeaderState, execInstrBr, BitVec.add_assoc]

theorem indexHeaderState_mem (s : MachineState) (a : Word) :
    (indexHeaderState s).getMem a =
      if a = 0x80018 then 0 else if a = 0x80010 then 0 else
        if a = 0x80008 then 0 else if a = 0x80000 then 5 else s.getMem a := by
  simp [indexHeaderState, execInstrBr, signExtend12, Expansion.mem_setMem,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]

def indexInputWord (s : MachineState) (i : Fin 14) : Word :=
  if i.val = 0 then 5 else if i.val < 4 then 0 else
    if i.val < 6 then s.getMem (wordAddress 0x40 (i.val - 4))
    else if i.val < 10 then s.getMem (wordAddress 0 (i.val - 6))
    else s.getMem (wordAddress 0x20060 (i.val - 10))

/-- Preparation of the complete tag5/public-key/message/randomizer input. -/
theorem index_prepare (s : MachineState) (pc : s.pc = 0x10fc) :
    ∃ ready, OrdinarySteps sign s 89 ready ∧ ready.pc = 0x11b8 ∧
      (∀ i : Fin 14, ready.getMem (wordAddress 0x80000 i.val) = indexInputWord s i) ∧
      (∀ a, (∀ i : Fin 14, a ≠ wordAddress 0x80000 i.val) → ready.getMem a = s.getMem a) := by
  obtain ⟨pk, pkLoop, pkInv, pkOutput, pkFrame⟩ := copy_all sign 0x110c (by decide)
    0x40 0x80020 2 (pkCopyState s) (pkCopyState_invariant s pc)
    (by decide) (by decide) (by decide) (by decide) (by decide)
  have pkpc : pk.pc = 0x1124 := by simpa [CopyInvariant] using pkInv.2.2.1
  obtain ⟨msg, msgLoop, msgInv, msgOutput, msgFrame⟩ := copy_all sign 0x1134 (by decide)
    0 0x80030 4 (indexMessageCopyState pk) (indexMessageCopyState_invariant pk pkpc)
    (by decide) (by decide) (by decide) (by decide) (by decide)
  have msgpc : msg.pc = 0x114c := by simpa [CopyInvariant] using msgInv.2.2.1
  obtain ⟨rand, randLoop, randInv, randOutput, randFrame⟩ := copy_all sign 0x1160 (by decide)
    0x20060 0x80050 4 (inputRandomizerCopyState msg) (inputRandomizerCopyState_invariant msg msgpc)
    (by decide) (by decide) (by decide) (by decide) (by decide)
  have randpc : rand.pc = 0x1178 := by simpa [CopyInvariant] using randInv.2.2.1
  have pkPreserved (i : Fin 2) :
      rand.getMem (wordAddress 0x80020 i.val) = s.getMem (wordAddress 0x40 i.val) := by
    rw [randFrame, inputRandomizerCopyState_mem, msgFrame, indexMessageCopyState_mem,
      pkOutput i.val i.isLt, pkCopyState_mem]
    · intro j hj
      apply outside_copy_word (0x80020 + 8 * i.val) 0x80030 4 j
      · have := i.isLt; omega
      · decide
      · exact hj
      · have := i.isLt; left; omega
    · intro j hj
      apply outside_copy_word (0x80020 + 8 * i.val) 0x80050 4 j
      · have := i.isLt; omega
      · decide
      · exact hj
      · have := i.isLt; left; omega
  have messagePreserved (i : Fin 4) :
      rand.getMem (wordAddress 0x80030 i.val) = s.getMem (wordAddress 0 i.val) := by
    rw [randFrame, inputRandomizerCopyState_mem, msgOutput i.val i.isLt,
      indexMessageCopyState_mem, pkFrame, pkCopyState_mem]
    · intro j hj
      apply outside_copy_word (0 + 8 * i.val) 0x80020 2 j
      · have := i.isLt; omega
      · decide
      · exact hj
      · have := i.isLt; left; omega
    · intro j hj
      apply outside_copy_word (0x80030 + 8 * i.val) 0x80050 4 j
      · have := i.isLt; omega
      · decide
      · exact hj
      · have := i.isLt; left; omega
  have randomizerCopied (i : Fin 4) :
      rand.getMem (wordAddress 0x80050 i.val) = s.getMem (wordAddress 0x20060 i.val) := by
    rw [randOutput i.val i.isLt, inputRandomizerCopyState_mem, msgFrame,
      indexMessageCopyState_mem, pkFrame, pkCopyState_mem]
    · intro j hj
      apply outside_copy_word (0x20060 + 8 * i.val) 0x80020 2 j
      · have := i.isLt; omega
      · decide
      · exact hj
      · have := i.isLt; left; omega
    · intro j hj
      apply outside_copy_word (0x20060 + 8 * i.val) 0x80030 4 j
      · have := i.isLt; omega
      · decide
      · exact hj
      · have := i.isLt; left; omega
  refine ⟨indexHeaderState rand, ?_, ?_, ?_, ?_⟩
  · exact ordinary_trans sign s _ _ 16 73
      (ordinary_trans sign s _ _ 4 12 (pkCopyState_block s pc) pkLoop)
      (ordinary_trans sign pk _ _ 28 45
        (ordinary_trans sign pk _ _ 4 24 (indexMessageCopyState_block pk pkpc) msgLoop)
        (ordinary_trans sign msg _ _ 29 16
          (ordinary_trans sign msg _ _ 5 24 (inputRandomizerCopyState_block msg msgpc) randLoop)
          (indexHeaderState_block rand randpc)))
  · simp [indexHeaderState_pc, randpc]
  · intro i
    fin_cases i <;> simp only [indexHeaderState_mem]
    all_goals simp only [wordAddress, indexInputWord, Fin.val_zero, Fin.val_one, Nat.mul_zero,
      Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT, Nat.reduceEqDiff,
      ↓reduceIte]
    all_goals first | rfl | simpa [wordAddress] using pkPreserved 0 | simpa [wordAddress] using pkPreserved 1 |
      simpa [wordAddress] using messagePreserved 0 | simpa [wordAddress] using messagePreserved 1 |
      simpa [wordAddress] using messagePreserved 2 | simpa [wordAddress] using messagePreserved 3 |
      simpa [wordAddress] using randomizerCopied 0 | simpa [wordAddress] using randomizerCopied 1 |
      simpa [wordAddress] using randomizerCopied 2 | simpa [wordAddress] using randomizerCopied 3
  · intro a outside
    have h0 : a ≠ 0x80000 := by simpa [wordAddress] using outside 0
    have h1 : a ≠ 0x80008 := by simpa [wordAddress] using outside 1
    have h2 : a ≠ 0x80010 := by simpa [wordAddress] using outside 2
    have h3 : a ≠ 0x80018 := by simpa [wordAddress] using outside 3
    rw [indexHeaderState_mem, if_neg h3, if_neg h2, if_neg h1, if_neg h0,
      randFrame, inputRandomizerCopyState_mem, msgFrame, indexMessageCopyState_mem, pkFrame, pkCopyState_mem]
    · intro j hj
      have eq : wordAddress 0x80020 j = wordAddress 0x80000 (j + 4) := by
        unfold wordAddress; congr 1; omega
      rw [eq]; exact outside ⟨j + 4, by omega⟩
    · intro j hj
      have eq : wordAddress 0x80030 j = wordAddress 0x80000 (j + 6) := by
        unfold wordAddress; congr 1; omega
      rw [eq]; exact outside ⟨j + 6, by omega⟩
    · intro j hj
      have eq : wordAddress 0x80050 j = wordAddress 0x80000 (j + 10) := by
        unfold wordAddress; congr 1; omega
      rw [eq]; exact outside ⟨j + 10, by omega⟩

/-- info: 'SigGolfCandidate.Hypertree.Signing.index_prepare' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms index_prepare

end SigGolfCandidate.Hypertree.Signing
