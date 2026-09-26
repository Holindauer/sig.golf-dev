import SigGolfCandidate.Hypertree.PreludeIndexBlocks

namespace SigGolfCandidate.Hypertree.Signing.Prelude
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 OracleComp Keygen
set_option maxRecDepth 4096
theorem index_prepare (s : MachineState) (pc : s.pc = 0x10fc) :
    ∃ ready, OrdinarySteps signPrelude s 89 ready ∧ ready.pc = 0x11b8 ∧
      (∀ i : Fin 14, ready.getMem (wordAddress 0x80000 i.val) = indexInputWord s i) ∧
      (∀ a, (∀ i : Fin 14, a ≠ wordAddress 0x80000 i.val) → ready.getMem a = s.getMem a) := by
  obtain ⟨pk, pkLoop, pkInv, pkOutput, pkFrame⟩ := copy_all signPrelude 0x110c (by decide)
    0x40 0x80020 2 (pkCopyState s) (pkCopyState_invariant s pc)
    (by decide) (by decide) (by decide) (by decide) (by decide)
  have pkpc : pk.pc = 0x1124 := by simpa [CopyInvariant] using pkInv.2.2.1
  obtain ⟨msg, msgLoop, msgInv, msgOutput, msgFrame⟩ := copy_all signPrelude 0x1134 (by decide)
    0 0x80030 4 (indexMessageCopyState pk) (indexMessageCopyState_invariant pk pkpc)
    (by decide) (by decide) (by decide) (by decide) (by decide)
  have msgpc : msg.pc = 0x114c := by simpa [CopyInvariant] using msgInv.2.2.1
  obtain ⟨rand, randLoop, randInv, randOutput, randFrame⟩ := copy_all signPrelude 0x1160 (by decide)
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
  · exact ordinary_trans signPrelude s _ _ 16 73
      (ordinary_trans signPrelude s _ _ 4 12 (pkCopyState_block s pc) pkLoop)
      (ordinary_trans signPrelude pk _ _ 28 45
        (ordinary_trans signPrelude pk _ _ 4 24 (indexMessageCopyState_block pk pkpc) msgLoop)
        (ordinary_trans signPrelude msg _ _ 29 16
          (ordinary_trans signPrelude msg _ _ 5 24 (inputRandomizerCopyState_block msg msgpc) randLoop)
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


theorem index_prepare_stack (s : MachineState) (pc : s.pc = 0x10fc) :
    ∃ final, OrdinarySteps signPrelude s 89 final ∧ final.getReg .x2 = s.getReg .x2 := by
  obtain ⟨pk, pkLoop, pkInv, _, _, _, pkSP⟩ := copy_all_frame signPrelude 0x110c (by decide)
    0x40 0x80020 2 (pkCopyState s) (pkCopyState_invariant s pc)
    (by decide) (by decide) (by decide) (by decide) (by decide)
  have pkpc : pk.pc = 0x1124 := by simpa [CopyInvariant] using pkInv.2.2.1
  obtain ⟨msg, msgLoop, msgInv, _, _, _, msgSP⟩ := copy_all_frame signPrelude 0x1134 (by decide)
    0 0x80030 4 (indexMessageCopyState pk) (indexMessageCopyState_invariant pk pkpc)
    (by decide) (by decide) (by decide) (by decide) (by decide)
  have msgpc : msg.pc = 0x114c := by simpa [CopyInvariant] using msgInv.2.2.1
  obtain ⟨rand, randLoop, randInv, _, _, _, randSP⟩ := copy_all_frame signPrelude 0x1160 (by decide)
    0x20060 0x80050 4 (inputRandomizerCopyState msg) (inputRandomizerCopyState_invariant msg msgpc)
    (by decide) (by decide) (by decide) (by decide) (by decide)
  have randpc : rand.pc = 0x1178 := by simpa [CopyInvariant] using randInv.2.2.1
  refine ⟨indexHeaderState rand, ?_, ?_⟩
  · exact ordinary_trans signPrelude s _ _ 16 73
      (ordinary_trans signPrelude s _ _ 4 12 (pkCopyState_block s pc) pkLoop)
      (ordinary_trans signPrelude pk _ _ 28 45
        (ordinary_trans signPrelude pk _ _ 4 24 (indexMessageCopyState_block pk pkpc) msgLoop)
        (ordinary_trans signPrelude msg _ _ 29 16
          (ordinary_trans signPrelude msg _ _ 5 24 (inputRandomizerCopyState_block msg msgpc) randLoop)
          (indexHeaderState_block rand randpc)))
  · have header : (indexHeaderState rand).getReg .x2 = rand.getReg .x2 := by
      simp [indexHeaderState, execInstrBr, MachineState.getReg_setReg_ne]
    have rprep : (inputRandomizerCopyState msg).getReg .x2 = msg.getReg .x2 := by
      simp [inputRandomizerCopyState, execInstrBr, MachineState.getReg_setReg_ne]
    have mprep : (indexMessageCopyState pk).getReg .x2 = pk.getReg .x2 := by
      simp [indexMessageCopyState, execInstrBr, MachineState.getReg_setReg_ne]
    have pprep : (pkCopyState s).getReg .x2 = s.getReg .x2 := by
      simp [pkCopyState, execInstrBr, MachineState.getReg_setReg_ne]
    exact header.trans (randSP.trans (rprep.trans (msgSP.trans (mprep.trans (pkSP.trans pprep)))))



theorem index_copy_full (s : MachineState) (pc : s.pc = 0x11d4) :
    ∃ final, OrdinarySteps signPrelude s 17 final ∧ final.pc = 0x1200 ∧
      (∀ i : Fin 2, final.getMem (wordAddress 0x80408 i.val) = s.getMem (wordAddress 0x80300 i.val)) ∧
      final.getMem 0x80310 = s.getMem 0x80310 ∧
      (∀ a, (∀ i : Fin 2, a ≠ wordAddress 0x80408 i.val) → final.getMem a = s.getMem a) ∧
      final.getReg .x2 = s.getReg .x2 := by
  have code : CopyCode signPrelude 0x11e8 := by decide
  obtain ⟨final, loop, inv, output, frame, _, sp⟩ := copy_all_frame signPrelude 0x11e8 code 0x80300 0x80408 2
    (indexCopyState s) (indexCopyState_invariant s pc)
    (by decide) (by decide) (by decide) (by decide) (by decide)
  refine ⟨final, ordinary_trans signPrelude s _ final 5 12 (indexCopyState_block s pc) loop,
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
    ∃ final, Trace hash signPrelude s 32 47 1 2 final ∧ final.pc = 0x1220 ∧
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
  have hf : fetch signPrelude hs = some (.base .ECALL) := by simp only [fetch, hpc]; decide
  have hv : hashArgumentsValid hs = true := hash_arguments hs 112 src len dst (by decide)
  have hlen : (hashInput hs).1 = 896 := by simp [hashInput, hs, len]
  let answer := hash (hashInput hs)
  have outpc : (writeHash hs answer).pc = 0x11d4 := by simp [hash_pc, hpc]
  obtain ⟨copied, copy, copypc, words, upper, frame, copySP⟩ := index_copy_full (writeHash hs answer) outpc
  have call : Trace hash signPrelude hs 1 16 1 2 (writeHash hs answer) := by
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

/-- info: 'SigGolfCandidate.Hypertree.Signing.Prelude.index_prepare' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms index_prepare

/-- info: 'SigGolfCandidate.Hypertree.Signing.Prelude.index_trace_full' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms index_trace_full

end SigGolfCandidate.Hypertree.Signing.Prelude
