import SigGolfCandidate.Hypertree.SignMemory

namespace SigGolfCandidate.Hypertree.Signing
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 OracleComp Keygen
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false

def indexHashState (s : MachineState) : MachineState :=
  let s := execInstrBr s (.LUI .x10 0x80)
  let s := execInstrBr s (.ADDI .x10 .x10 0)
  let s := execInstrBr s (.ADDI .x11 .x0 896)
  let s := execInstrBr s (.LUI .x12 0x80)
  let s := execInstrBr s (.ADDI .x12 .x12 0x300)
  execInstrBr s (.ADDI .x5 .x0 1)

theorem indexHashState_block (s : MachineState) (pc : s.pc = 0x11b8) :
    OrdinarySteps sign s 6 (indexHashState s) := by
  let s1 := execInstrBr s (.LUI .x10 0x80)
  let s2 := execInstrBr s1 (.ADDI .x10 .x10 0)
  let s3 := execInstrBr s2 (.ADDI .x11 .x0 896)
  let s4 := execInstrBr s3 (.LUI .x12 0x80)
  let s5 := execInstrBr s4 (.ADDI .x12 .x12 0x300)
  let s6 := execInstrBr s5 (.ADDI .x5 .x0 1)
  apply OrdinarySteps.step s s1 _ (.base (.LUI .x10 0x80)) 5
  · have hp : s.pc = 0x11b8 := by simp [execInstrBr, pc]
    simp only [fetch, hp]; decide
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.ADDI .x10 .x10 0)) 4
  · have hp : s1.pc = 0x11bc := by simp [s1, execInstrBr, pc]
    simp only [fetch, hp]; decide
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.ADDI .x11 .x0 896)) 3
  · have hp : s2.pc = 0x11c0 := by simp [s1, s2, execInstrBr, pc]
    simp only [fetch, hp]; decide
  · rfl
  apply OrdinarySteps.step s3 s4 _ (.base (.LUI .x12 0x80)) 2
  · have hp : s3.pc = 0x11c4 := by simp [s1, s2, s3, execInstrBr, pc]
    simp only [fetch, hp]; decide
  · rfl
  apply OrdinarySteps.step s4 s5 _ (.base (.ADDI .x12 .x12 0x300)) 1
  · have hp : s4.pc = 0x11c8 := by simp [s1, s2, s3, s4, execInstrBr, pc]
    simp only [fetch, hp]; decide
  · rfl
  apply OrdinarySteps.step s5 s6 _ (.base (.ADDI .x5 .x0 1)) 0
  · have hp : s5.pc = 0x11cc := by simp [s1, s2, s3, s4, s5, execInstrBr, pc]
    simp only [fetch, hp]; decide
  · rfl
  exact OrdinarySteps.refl _

def indexCopyState (s : MachineState) : MachineState :=
  let s := execInstrBr s (.LUI .x6 0x80)
  let s := execInstrBr s (.ADDI .x6 .x6 0x300)
  let s := execInstrBr s (.LUI .x7 0x80)
  let s := execInstrBr s (.ADDI .x7 .x7 0x408)
  execInstrBr s (.ADDI .x10 .x0 2)

theorem indexCopyState_block (s : MachineState) (pc : s.pc = 0x11d4) :
    OrdinarySteps sign s 5 (indexCopyState s) := by
  let s1 := execInstrBr s (.LUI .x6 0x80)
  let s2 := execInstrBr s1 (.ADDI .x6 .x6 0x300)
  let s3 := execInstrBr s2 (.LUI .x7 0x80)
  let s4 := execInstrBr s3 (.ADDI .x7 .x7 0x408)
  let s5 := execInstrBr s4 (.ADDI .x10 .x0 2)
  apply OrdinarySteps.step s s1 _ (.base (.LUI .x6 0x80)) 4
  · have hp : s.pc = 0x11d4 := by simp [execInstrBr, pc]
    simp only [fetch, hp]; decide
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.ADDI .x6 .x6 0x300)) 3
  · have hp : s1.pc = 0x11d8 := by simp [s1, execInstrBr, pc]
    simp only [fetch, hp]; decide
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.LUI .x7 0x80)) 2
  · have hp : s2.pc = 0x11dc := by simp [s1, s2, execInstrBr, pc]
    simp only [fetch, hp]; decide
  · rfl
  apply OrdinarySteps.step s3 s4 _ (.base (.ADDI .x7 .x7 0x408)) 1
  · have hp : s3.pc = 0x11e0 := by simp [s1, s2, s3, execInstrBr, pc]
    simp only [fetch, hp]; decide
  · rfl
  apply OrdinarySteps.step s4 s5 _ (.base (.ADDI .x10 .x0 2)) 0
  · have hp : s4.pc = 0x11e4 := by simp [s1, s2, s3, s4, execInstrBr, pc]
    simp only [fetch, hp]; decide
  · rfl
  exact OrdinarySteps.refl _

def indexStoreState (s : MachineState) : MachineState :=
  let s := execInstrBr s (.LUI .x28 0x80)
  let s := execInstrBr s (.ADDI .x28 .x28 0x310)
  let s := execInstrBr s (.LD .x6 .x28 0)
  let s := execInstrBr s (.SLLI .x6 .x6 32)
  let s := execInstrBr s (.SRLI .x6 .x6 32)
  let s := execInstrBr s (.LUI .x28 0x80)
  let s := execInstrBr s (.ADDI .x28 .x28 0x418)
  execInstrBr s (.SD .x28 .x6 0)

theorem indexStoreState_block (s : MachineState) (pc : s.pc = 0x1200) :
    OrdinarySteps sign s 8 (indexStoreState s) := by
  let s1 := execInstrBr s (.LUI .x28 0x80)
  let s2 := execInstrBr s1 (.ADDI .x28 .x28 0x310)
  let s3 := execInstrBr s2 (.LD .x6 .x28 0)
  let s4 := execInstrBr s3 (.SLLI .x6 .x6 32)
  let s5 := execInstrBr s4 (.SRLI .x6 .x6 32)
  let s6 := execInstrBr s5 (.LUI .x28 0x80)
  let s7 := execInstrBr s6 (.ADDI .x28 .x28 0x418)
  let s8 := execInstrBr s7 (.SD .x28 .x6 0)
  apply OrdinarySteps.step s s1 _ (.base (.LUI .x28 0x80)) 7
  · have hp : s.pc = 0x1200 := by simp [execInstrBr, pc]
    simp only [fetch, hp]; decide
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.ADDI .x28 .x28 0x310)) 6
  · have hp : s1.pc = 0x1204 := by simp [s1, execInstrBr, pc]
    simp only [fetch, hp]; decide
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.LD .x6 .x28 0)) 5
  · have hp : s2.pc = 0x1208 := by simp [s1, s2, execInstrBr, pc]
    simp only [fetch, hp]; decide
  · simp [s1, s2, s3, ordinaryStep, memoryArgumentsValid, execInstrBr, signExtend12, accessValid, rangeValid, MEMORY_BYTES, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s3 s4 _ (.base (.SLLI .x6 .x6 32)) 4
  · have hp : s3.pc = 0x120c := by simp [s1, s2, s3, execInstrBr, pc]
    simp only [fetch, hp]; decide
  · rfl
  apply OrdinarySteps.step s4 s5 _ (.base (.SRLI .x6 .x6 32)) 3
  · have hp : s4.pc = 0x1210 := by simp [s1, s2, s3, s4, execInstrBr, pc]
    simp only [fetch, hp]; decide
  · rfl
  apply OrdinarySteps.step s5 s6 _ (.base (.LUI .x28 0x80)) 2
  · have hp : s5.pc = 0x1214 := by simp [s1, s2, s3, s4, s5, execInstrBr, pc]
    simp only [fetch, hp]; decide
  · rfl
  apply OrdinarySteps.step s6 s7 _ (.base (.ADDI .x28 .x28 0x418)) 1
  · have hp : s6.pc = 0x1218 := by simp [s1, s2, s3, s4, s5, s6, execInstrBr, pc]
    simp only [fetch, hp]; decide
  · rfl
  apply OrdinarySteps.step s7 s8 _ (.base (.SD .x28 .x6 0)) 0
  · have hp : s7.pc = 0x121c := by simp [s1, s2, s3, s4, s5, s6, s7, execInstrBr, pc]
    simp only [fetch, hp]; decide
  · simp [s1, s2, s3, s4, s5, s6, s7, s8, ordinaryStep, memoryArgumentsValid, execInstrBr, signExtend12, accessValid, rangeValid, MEMORY_BYTES, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  exact OrdinarySteps.refl _

theorem indexHashState_regs (s : MachineState) :
    (indexHashState s).getReg .x5 = 1 ∧ (indexHashState s).getReg .x10 = 0x80000 ∧
    (indexHashState s).getReg .x11 = 896 ∧ (indexHashState s).getReg .x12 = 0x80300 := by
  simp [indexHashState, execInstrBr, signExtend12,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]

theorem indexHashState_pc (s : MachineState) : (indexHashState s).pc = s.pc + 24 := by
  simp [indexHashState, execInstrBr, BitVec.add_assoc]

theorem indexCopyState_mem (s : MachineState) (a : Word) :
    (indexCopyState s).getMem a = s.getMem a := by simp [indexCopyState, execInstrBr]

theorem indexCopyState_invariant (s : MachineState) (pc : s.pc = 0x11d4) :
    CopyInvariant 0x11e8 0x80300 0x80408 2 2 (indexCopyState s) := by
  simp [CopyInvariant, indexCopyState, execInstrBr, signExtend12, pc,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]

theorem indexStoreState_mem (s : MachineState) (a : Word) :
    (indexStoreState s).getMem a =
      if a = 0x80418 then (s.getMem 0x80310 <<< 32) >>> 32 else s.getMem a := by
  simp [indexStoreState, execInstrBr, signExtend12, Expansion.mem_setMem,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]

theorem indexStoreState_pc (s : MachineState) : (indexStoreState s).pc = s.pc + 32 := by
  simp [indexStoreState, execInstrBr, BitVec.add_assoc]

theorem index_copy (s : MachineState) (pc : s.pc = 0x11d4) :
    ∃ final, OrdinarySteps sign s 17 final ∧ final.pc = 0x1200 ∧
      (∀ i : Fin 2, final.getMem (wordAddress 0x80408 i.val) = s.getMem (wordAddress 0x80300 i.val)) ∧
      final.getMem 0x80310 = s.getMem 0x80310 := by
  have code : CopyCode sign 0x11e8 := by decide
  obtain ⟨final, loop, inv, output, frame⟩ := copy_all sign 0x11e8 code 0x80300 0x80408 2
    (indexCopyState s) (indexCopyState_invariant s pc)
    (by decide) (by decide) (by decide) (by decide) (by decide)
  refine ⟨final, ordinary_trans sign s _ final 5 12 (indexCopyState_block s pc) loop,
    by simpa [CopyInvariant] using inv.2.2.1, ?_, ?_⟩
  · intro i; simpa only [indexCopyState_mem] using output i.val i.isLt
  · rw [frame, indexCopyState_mem]
    intro i hi
    apply outside_copy_word 0x80310 0x80408 2 i (by decide) (by decide) hi (by decide)

/-- The exact index HASH and extraction block stores the low 160 answer bits in
three aligned words, with zeroed upper half of the third word. -/
theorem index_trace (hash : Hash) (s : MachineState) (pc : s.pc = 0x11b8) :
    ∃ final, Trace hash sign s 32 47 1 2 final ∧ final.pc = 0x1220 ∧
      (∀ i : Fin 2, final.getMem (wordAddress 0x80408 i.val) =
        (hash (hashInput (indexHashState s))).extractLsb' (64 * i.val) 64) ∧
      final.getMem 0x80418 =
        ((hash (hashInput (indexHashState s))).extractLsb' 128 64 <<< 32) >>> 32 := by
  let hs := indexHashState s
  have hpc : hs.pc = 0x11d0 := by simp [hs, indexHashState_pc, pc]
  obtain ⟨service, src, len, dst⟩ := indexHashState_regs s
  have hf : fetch sign hs = some (.base .ECALL) := by simp only [fetch, hpc]; decide
  have hv : hashArgumentsValid hs = true := hash_arguments hs 896 src len dst (by decide)
  have hlen : (hashInput hs).1 = 896 := by simp [hashInput, hs, len]
  let answer := hash (hashInput hs)
  have outpc : (writeHash hs answer).pc = 0x11d4 := by simp [hash_pc, hpc]
  obtain ⟨copied, copy, copypc, words, upper⟩ := index_copy (writeHash hs answer) outpc
  have call : Trace hash sign hs 1 16 1 2 (writeHash hs answer) := by
    simpa [hlen, compressions] using Trace.hash hs (writeHash hs answer) 0 0 0 0 hf service hv
      (Trace.refl (writeHash hs answer))
  refine ⟨indexStoreState copied, ?_, ?_, ?_, ?_⟩
  · exact (((indexHashState_block s pc).trace.trans call).trans copy.trace).trans
      (indexStoreState_block copied copypc).trace
  · simp [indexStoreState_pc, copypc]
  · intro i
    rw [indexStoreState_mem, if_neg, words i]
    · exact hash_answer_word hs answer dst ⟨i.val, by have := i.isLt; omega⟩
    · fin_cases i <;> decide
  · rw [indexStoreState_mem, if_pos rfl, upper]
    rw [show (writeHash hs answer).getMem 0x80310 = answer.extractLsb' 128 64 from
      hash_answer_word hs answer dst 2]

/-- info: 'SigGolfCandidate.Hypertree.Signing.index_trace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms index_trace

end SigGolfCandidate.Hypertree.Signing
