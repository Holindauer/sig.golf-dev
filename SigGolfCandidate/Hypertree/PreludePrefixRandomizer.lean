import SigGolfCandidate.Hypertree.PreludeRandomizerBlocks
import SigGolfCandidate.Hypertree.PreludeResume

namespace SigGolfCandidate.Hypertree.Signing.Prelude
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 OracleComp Keygen
set_option maxRecDepth 4096
theorem randomizer_prepare_full (s : MachineState) (pc : s.pc = 0x1004) (entryReady : s.getReg .x6 = 1) :
    ∃ ready, OrdinarySteps signPrelude s 80 ready ∧ ready.pc = 0x10b4 ∧
      (∀ i : Fin 12, ready.getMem (wordAddress 0x80000 i.val) = randomizerInputWord s i) ∧
      (∀ a, a ≠ 0x80440 → a ≠ 0x80448 →
        (∀ i : Fin 12, a ≠ wordAddress 0x80000 i.val) → ready.getMem a = s.getMem a) ∧
      ready.getMem 0x80440 = 1 ∧ ready.getMem 0x80448 = 0x20080 ∧ ready.getReg .x2 = s.getReg .x2 := by
  have secretKeyCode : CopyCode signPrelude 0x1034 := by decide
  have msgCode : CopyCode signPrelude 0x105c := by decide
  obtain ⟨secretKey, secretKeyLoop, secretKeyInv, secretKeyOutput, secretKeyFrame, _, secretKeySP⟩ := copy_all_frame signPrelude 0x1034 secretKeyCode
    0x20 0x80020 4 (initializeState (s.setPC 0x1000)) (initializeState_invariant (s.setPC 0x1000) rfl)
    (by decide) (by decide) (by decide) (by decide) (by decide)
  have secretKeypc : secretKey.pc = 0x104c := by simpa [CopyInvariant] using secretKeyInv.2.2.1
  obtain ⟨msg, msgLoop, msgInv, msgOutput, msgFrame, _, msgSP⟩ := copy_all_frame signPrelude 0x105c msgCode
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
  refine ⟨randomizerHeaderState msg, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ordinary_trans signPrelude s _ _ 36 44
      (ordinary_trans signPrelude s _ _ 12 24 (resumed_initialization s pc entryReady) secretKeyLoop)
      (ordinary_trans signPrelude secretKey _ _ 4 40 (messageCopyState_block secretKey secretKeypc)
        (ordinary_trans signPrelude (messageCopyState secretKey) _ _ 24 16 msgLoop (randomizerHeaderState_block msg msgpc)))
  · simp [randomizerHeaderState_pc, msgpc]
  · intro i
    fin_cases i <;> simp only [randomizerHeaderState_mem]
    all_goals simp only [wordAddress, randomizerInputWord, Nat.mul_zero,
      Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT, Nat.reduceEqDiff,
      ↓reduceIte]
    all_goals first | rfl | simpa [wordAddress] using secretKeyPreserved 0 | simpa [wordAddress] using secretKeyPreserved 1 |
      simpa [wordAddress] using messageCopied 0 | simpa [wordAddress] using messageCopied 1 |
      simpa [wordAddress] using secretKeyPreserved 2 | simpa [wordAddress] using secretKeyPreserved 3 |
      simpa [wordAddress] using messageCopied 2 | simpa [wordAddress] using messageCopied 3

  · intro a mode pointer outside
    have h0 : a ≠ 0x80000 := by simpa [wordAddress] using outside 0
    have h1 : a ≠ 0x80008 := by simpa [wordAddress] using outside 1
    have h2 : a ≠ 0x80010 := by simpa [wordAddress] using outside 2
    have h3 : a ≠ 0x80018 := by simpa [wordAddress] using outside 3
    rw [randomizerHeaderState_mem, if_neg h3, if_neg h2, if_neg h1, if_neg h0,
      msgFrame, messageCopyState_mem, secretKeyFrame, initializeState_mem, if_neg pointer, if_neg mode, MachineState.getMem_setPC]
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

  · rw [randomizerHeaderState_mem, if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide),
      msgFrame _ (by intro i hi; interval_cases i <;> decide), messageCopyState_mem,
      secretKeyFrame _ (by intro i hi; interval_cases i <;> decide), initializeState_mem]
    rfl
  · rw [randomizerHeaderState_mem, if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide),
      msgFrame _ (by intro i hi; interval_cases i <;> decide), messageCopyState_mem,
      secretKeyFrame _ (by intro i hi; interval_cases i <;> decide), initializeState_mem]
    rfl
  · have headSP : (randomizerHeaderState msg).getReg .x2 = msg.getReg .x2 := by
      simp [randomizerHeaderState, execInstrBr, MachineState.getReg_setReg_ne]
    have messageSP : (messageCopyState secretKey).getReg .x2 = secretKey.getReg .x2 := by
      simp [messageCopyState, execInstrBr, MachineState.getReg_setReg_ne]
    rw [headSP,msgSP,messageSP,secretKeySP]
    simp [initializeState, execInstrBr, MachineState.getReg_setReg_ne, MachineState.getReg_setPC]

theorem randomizer_trace_full (hash : Hash) (s : MachineState) (pc : s.pc = 0x10b4) :
    ∃ final, Trace hash signPrelude s 36 51 1 2 final ∧ final.pc = 0x10fc ∧
      (∀ i : Fin 4, final.getMem (wordAddress 0x20060 i.val) =
        (hash (hashInput (randomizerHashState s))).extractLsb' (64 * i.val) 64) ∧
      (∀ a, (∀ i : Fin 4, a ≠ wordAddress 0x20060 i.val) →
        (∀ i : Fin 4, a ≠ wordAddress 0x80300 i.val) → final.getMem a = s.getMem a) ∧
      final.getReg .x2 = s.getReg .x2 := by
  let hs := randomizerHashState s
  have hpc : hs.pc = 0x10cc := by simp [hs, randomizerHashState_pc, pc]
  obtain ⟨service, src, len, dst⟩ := randomizerHashState_regs s
  have hf : fetch signPrelude hs = some (.base .ECALL) := by simp only [fetch, hpc]; decide
  have hv : hashArgumentsValid hs = true := hash_arguments hs 96 src len dst (by decide)
  have hlen : (hashInput hs).1 = 768 := by simp [hashInput, hs, len]
  let answer := hash (hashInput hs)
  have outpc : (writeHash hs answer).pc = 0x10d0 := by simp [hash_pc, hpc]
  obtain ⟨final, loop, inv, output, frame, _, copySP⟩ := copy_all_frame signPrelude 0x10e4 randomizer_copy_code
    0x80300 0x20060 4 (randomizerCopyState (writeHash hs answer))
    (randomizerCopyState_invariant (writeHash hs answer) outpc)
    (by decide) (by decide) (by decide) (by decide) (by decide)
  have copied : OrdinarySteps signPrelude (writeHash hs answer) 29 final :=
    ordinary_trans signPrelude _ _ final 5 24 (randomizerCopyState_block _ outpc) loop
  have call : Trace hash signPrelude hs 1 16 1 2 (writeHash hs answer) := by
    simpa [hlen, compressions] using Trace.hash hs (writeHash hs answer) 0 0 0 0 hf service hv
      (Trace.refl (writeHash hs answer))
  refine ⟨final, ((randomizerHashState_block s pc).trace.trans call).trans copied.trace,
    by simpa [CopyInvariant] using inv.2.2.1, ?_, ?_, ?_⟩
  · intro i
    rw [output i.val i.isLt, randomizerCopyState_mem]
    exact hash_answer_word hs answer dst i
  · intro a sigOutside answerOutside
    rw [frame a (fun i hi => sigOutside ⟨i, hi⟩), randomizerCopyState_mem,
      hash_answer_frame hs answer dst a answerOutside]
    simp [hs, randomizerHashState, execInstrBr]

  · rw [copySP]
    have copySetup : (randomizerCopyState (writeHash hs answer)).getReg .x2 = (writeHash hs answer).getReg .x2 := by
      simp [randomizerCopyState, execInstrBr, MachineState.getReg_setReg_ne]
    rw [copySetup,hash_registers]
    simp [hs,randomizerHashState,execInstrBr,MachineState.getReg_setReg_ne]

theorem randomizer_refines_full (hash : Hash) (s : MachineState) (secretKey : SecretKey) (message : Message)
    (pc : s.pc = 0x1004) (entryReady : s.getReg .x6 = 1)
    (hsecretKey : ∀ i, i < 32 → s.getByte (BitVec.ofNat 64 (0x20+i)) = secretKey.extractLsb' (8*i) 8)
    (hmessage : ∀ i, i < 32 → s.getByte (BitVec.ofNat 64 i) = message.extractLsb' (8*i) 8) :
    ∃ final, Trace hash signPrelude s 116 131 1 2 final ∧ final.pc = 0x10fc ∧
      (∀ i : Fin 4, final.getMem (wordAddress 0x20060 i.val) =
        (Reference.randomizer hash secretKey message).extractLsb' (64*i.val) 64) ∧
      final.getMem 0x80440 = 1 ∧ final.getMem 0x80448 = 0x20080 ∧ final.getReg .x2 = s.getReg .x2 ∧
      (∀ a, (∀ i : Fin 14, a ≠ wordAddress 0x80000 i.val) →
        (∀ i : Fin 4, a ≠ wordAddress 0x80300 i.val) →
        (∀ i : Fin 4, a ≠ wordAddress 0x20060 i.val) →
        a ≠ 0x80440 → a ≠ 0x80448 → final.getMem a = s.getMem a) := by
  obtain ⟨ready,prepare,rpc,words,prepareFrame,mode,pointer,readySP⟩ := randomizer_prepare_full s pc entryReady
  obtain ⟨final,run,fpc,output,frame,finalSP⟩ := randomizer_trace_full hash ready rpc
  have query := randomizer_query s ready secretKey message hsecretKey hmessage words
  refine ⟨final,prepare.trace.trans run,fpc,?_,?_,?_,finalSP.trans readySP,?_⟩
  · intro i; rw [output i,query]; rfl
  · rw [frame _ (by intro i; fin_cases i <;> decide) (by intro i; fin_cases i <;> decide)]; exact mode
  · rw [frame _ (by intro i; fin_cases i <;> decide) (by intro i; fin_cases i <;> decide)]; exact pointer
  · intro a inputOutside answerOutside sigOutside modeOutside pointerOutside
    rw [frame a sigOutside answerOutside]
    exact prepareFrame a modeOutside pointerOutside (fun i => inputOutside ⟨i.val,by have := i.isLt; omega⟩)


/-- info: 'SigGolfCandidate.Hypertree.Signing.Prelude.randomizer_prepare_full' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms randomizer_prepare_full

/-- info: 'SigGolfCandidate.Hypertree.Signing.Prelude.randomizer_trace_full' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms randomizer_trace_full

/-- info: 'SigGolfCandidate.Hypertree.Signing.Prelude.randomizer_refines_full' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms randomizer_refines_full

end SigGolfCandidate.Hypertree.Signing.Prelude
