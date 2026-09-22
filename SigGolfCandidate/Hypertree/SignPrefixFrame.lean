import SigGolfCandidate.Hypertree.SignIndexRefine
import SigGolfCandidate.Hypertree.KeygenCopyFrame
import SigGolfCandidate.Hypertree.SignShift

namespace SigGolfCandidate.Hypertree.Signing
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 OracleComp Keygen
set_option maxRecDepth 4096

theorem index_copy_full (s : MachineState) (pc : s.pc = 0x11d4) :
    ∃ final, OrdinarySteps sign s 17 final ∧ final.pc = 0x1200 ∧
      (∀ i : Fin 2, final.getMem (wordAddress 0x80408 i.val) = s.getMem (wordAddress 0x80300 i.val)) ∧
      final.getMem 0x80310 = s.getMem 0x80310 ∧
      (∀ a, (∀ i : Fin 2, a ≠ wordAddress 0x80408 i.val) → final.getMem a = s.getMem a) ∧
      final.getReg .x2 = s.getReg .x2 := by
  have code : CopyCode sign 0x11e8 := by decide
  obtain ⟨final, loop, inv, output, frame, _, sp⟩ := copy_all_frame sign 0x11e8 code 0x80300 0x80408 2
    (indexCopyState s) (indexCopyState_invariant s pc)
    (by decide) (by decide) (by decide) (by decide) (by decide)
  refine ⟨final, ordinary_trans sign s _ final 5 12 (indexCopyState_block s pc) loop,
    by simpa [CopyInvariant] using inv.2.2.1, ?_, ?_, ?_, ?_⟩
  · intro i; simpa only [indexCopyState_mem] using output i.val i.isLt
  · rw [frame, indexCopyState_mem]
    intro i hi
    apply outside_copy_word 0x80310 0x80408 2 i (by decide) (by decide) hi (by decide)

  · intro a outside
    rw [frame, indexCopyState_mem]
    intro i hi
    exact outside ⟨i, hi⟩

  · rw [sp]
    simp [indexCopyState, execInstrBr, MachineState.getReg_setReg_ne]

theorem index_trace_full (hash : Hash) (s : MachineState) (pc : s.pc = 0x11b8) :
    ∃ final, Trace hash sign s 32 47 1 2 final ∧ final.pc = 0x1220 ∧
      (∀ i : Fin 2, final.getMem (wordAddress 0x80408 i.val) =
        (hash (hashInput (indexHashState s))).extractLsb' (64 * i.val) 64) ∧
      final.getMem 0x80418 =
        ((hash (hashInput (indexHashState s))).extractLsb' 128 64 <<< 32) >>> 32 ∧
      (∀ a, (∀ i : Fin 4, a ≠ wordAddress 0x80300 i.val) →
        (∀ i : Fin 3, a ≠ wordAddress 0x80408 i.val) → final.getMem a = s.getMem a) ∧
      final.getReg .x2 = s.getReg .x2 := by
  let hs := indexHashState s
  have hpc : hs.pc = 0x11d0 := by simp [hs, indexHashState_pc, pc]
  obtain ⟨service, src, len, dst⟩ := indexHashState_regs s
  have hf : fetch sign hs = some (.base .ECALL) := by simp only [fetch, hpc]; decide
  have hv : hashArgumentsValid hs = true := hash_arguments hs 896 src len dst (by decide)
  have hlen : (hashInput hs).1 = 896 := by simp [hashInput, hs, len]
  let answer := hash (hashInput hs)
  have outpc : (writeHash hs answer).pc = 0x11d4 := by simp [hash_pc, hpc]
  obtain ⟨copied, copy, copypc, words, upper, frame, copySP⟩ := index_copy_full (writeHash hs answer) outpc
  have call : Trace hash sign hs 1 16 1 2 (writeHash hs answer) := by
    simpa [hlen, compressions] using Trace.hash hs (writeHash hs answer) 0 0 0 0 hf service hv
      (Trace.refl (writeHash hs answer))
  refine ⟨indexStoreState copied, ?_, ?_, ?_, ?_, ?_, ?_⟩
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

  · intro a outsideAnswer outsideIndex
    have outsideHigh : a ≠ 0x80418 := outsideIndex 2
    rw [indexStoreState_mem, if_neg outsideHigh, frame]
    · rw [hash_answer_frame hs answer dst a outsideAnswer, indexHashState_mem]
    · intro i
      exact outsideIndex ⟨i.val, by have := i.isLt; omega⟩

  · have store : (indexStoreState copied).getReg .x2 = copied.getReg .x2 := by
      simp [indexStoreState, execInstrBr, MachineState.getReg_setReg_ne]
    rw [store, copySP, hash_registers]
    simp [hs, indexHashState, execInstrBr, MachineState.getReg_setReg_ne]

/-- info: 'SigGolfCandidate.Hypertree.Signing.index_trace_full' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms index_trace_full

end SigGolfCandidate.Hypertree.Signing
