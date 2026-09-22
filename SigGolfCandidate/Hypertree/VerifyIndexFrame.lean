import SigGolfCandidate.Hypertree.VerifyRefine
import SigGolfCandidate.Hypertree.SignShift

namespace SigGolfCandidate.Hypertree.Verifying
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 OracleComp Keygen Signing
set_option maxRecDepth 4096

theorem index_copy_frame (s : MachineState) (pc : s.pc = 0x10fc) :
    ∃ final, OrdinarySteps verify s 17 final ∧ final.pc = 0x1128 ∧
      (∀ i : Fin 2, final.getMem (wordAddress 0x80408 i.val) = s.getMem (wordAddress 0x80300 i.val)) ∧
      final.getMem 0x80310 = s.getMem 0x80310 ∧
      (∀ a, (∀ i : Fin 2, a ≠ wordAddress 0x80408 i.val) → final.getMem a = s.getMem a) := by
  have code : CopyCode verify 0x1110 := by decide
  obtain ⟨final, loop, inv, output, frame⟩ := copy_all verify 0x1110 code 0x80300 0x80408 2
    (indexCopyState s) (indexCopyState_invariant s pc)
    (by decide) (by decide) (by decide) (by decide) (by decide)
  refine ⟨final, ordinary_trans verify s _ final 5 12 (indexCopyState_block s pc) loop,
    by simpa [CopyInvariant] using inv.2.2.1, ?_, ?_, ?_⟩
  · intro i; simpa only [indexCopyState_mem] using output i.val i.isLt
  · rw [frame, indexCopyState_mem]
    intro i hi
    apply outside_copy_word 0x80310 0x80408 2 i (by decide) (by decide) hi (by decide)

  · intro a outside
    rw [frame, indexCopyState_mem]
    intro i hi
    exact outside ⟨i, hi⟩

theorem index_trace_frame (hash : Hash) (s : MachineState) (pc : s.pc = 0x10e0) :
    ∃ final, Trace hash verify s 32 47 1 2 final ∧ final.pc = 0x1148 ∧
      (∀ i : Fin 2, final.getMem (wordAddress 0x80408 i.val) =
        (hash (hashInput (indexHashState s))).extractLsb' (64 * i.val) 64) ∧
      final.getMem 0x80418 =
        ((hash (hashInput (indexHashState s))).extractLsb' 128 64 <<< 32) >>> 32 ∧
      (∀ a, (∀ i : Fin 4, a ≠ wordAddress 0x80300 i.val) →
        (∀ i : Fin 3, a ≠ wordAddress 0x80408 i.val) → final.getMem a = s.getMem a) := by
  let hs := indexHashState s
  have hpc : hs.pc = 0x10f8 := by simp [hs, indexHashState_pc, pc]
  obtain ⟨service, src, len, dst⟩ := indexHashState_regs s
  have hf : fetch verify hs = some (.base .ECALL) := by simp only [fetch, hpc]; decide
  have hv : hashArgumentsValid hs = true := hash_arguments hs 896 src len dst (by decide)
  have hlen : (hashInput hs).1 = 896 := by simp [hashInput, hs, len]
  let answer := hash (hashInput hs)
  have outpc : (writeHash hs answer).pc = 0x10fc := by simp [hash_pc, hpc]
  obtain ⟨copied, copy, copypc, words, upper, frame⟩ := index_copy_frame (writeHash hs answer) outpc
  have call : Trace hash verify hs 1 16 1 2 (writeHash hs answer) := by
    simpa [hlen, compressions] using Trace.hash hs (writeHash hs answer) 0 0 0 0 hf service hv
      (Trace.refl (writeHash hs answer))
  refine ⟨indexStoreState copied, ?_, ?_, ?_, ?_, ?_⟩
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

/-- info: 'SigGolfCandidate.Hypertree.Verifying.index_trace_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms index_trace_frame

end SigGolfCandidate.Hypertree.Verifying
