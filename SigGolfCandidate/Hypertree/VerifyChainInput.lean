import SigGolfCandidate.Hypertree.VerifyChainPrepare

namespace SigGolfCandidate.Hypertree.Verifying
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 Keygen Signing
set_option maxRecDepth 4096

theorem chainValueState_digit (s : MachineState) (chain : Reference.Chain) :
    (chainValueState s).getByte (BitVec.ofNat 64 (0x80600 + chain.val)) =
      s.getByte (BitVec.ofNat 64 (0x80600 + chain.val)) := by
  rw [getByte_word _ 0x80600 chain.val (by decide) (by have := chain.isLt; omega),
    getByte_word s 0x80600 chain.val (by decide) (by have := chain.isLt; omega), chainValueState_mem]
  rw [if_neg (by fin_cases chain <;> decide), if_neg (by fin_cases chain <;> decide)]

/-- Load one witness chain value and the corresponding already-certified encoding digit. -/
theorem chain_prepare (s : MachineState) (level tree : Nat) (side : Bool)
    (chain : Reference.Chain) (digit : Fin 8) (value : Reference.Digest)
    (pc : s.pc = 0x1490)
    (valid0 : accessValid (chainSource s) 8 = true) (valid8 : accessValid (chainSource s + 8) 8 = true)
    (levelEq : s.getMem 0x80400 = BitVec.ofNat 64 level)
    (leafEq : s.getMem 0x80428 = BitVec.ofNat 64 (Reference.sideNumber side))
    (chainEq : s.getMem 0x80430 = BitVec.ofNat 64 chain.val)
    (indexEq : ∀ i : Fin 3, s.getMem (wordAddress 0x80408 i.val) = (BitVec.ofNat 192 tree).extractLsb' (64*i.val) 64)
    (value0 : s.getMem (chainSource s) = value.extractLsb' 0 64)
    (value8 : s.getMem (chainSource s + 8) = value.extractLsb' 64 64)
    (digitEq : s.getByte (BitVec.ofNat 64 (0x80600 + chain.val)) = BitVec.ofNat 8 digit.val) :
    ∃ final, OrdinarySteps verify s 23 final ∧ final.pc = 0x14ec ∧
      ChainData final level tree side chain digit.val value ∧
      final.getReg .x1 = s.getReg .x1 ∧ final.getReg .x2 = s.getReg .x2 ∧
      (∀ a, a ≠ 0x80510 → a ≠ 0x80518 → a ≠ 0x80438 → final.getMem a = s.getMem a) := by
  have valuePC : (chainValueState s).pc = 0x14d0 := by rw [chainValueState_pc, pc]; rfl
  have digitAddress : (0x80600 : Word) + BitVec.ofNat 64 chain.val = BitVec.ofNat 64 (0x80600 + chain.val) :=
    (BitVec.ofNat_add _ _).symm
  have digitValid : accessValid (0x80600 + (chainValueState s).getReg .x6) 1 = true := by
    rw [chainValueState_chain, chainEq, digitAddress]
    simp only [accessValid, rangeValid, BitVec.toNat_ofNat, MEMORY_BYTES, Nat.mod_one,
      decide_true, Bool.and_true, decide_eq_true_eq]
    have := chain.isLt
    omega
  have memory (a : Word) (notStep : a ≠ 0x80438) (notHigh : a ≠ 0x80518) (notLow : a ≠ 0x80510) :
      (chainDigitState (chainValueState s)).getMem a = s.getMem a := by
    rw [chainDigitState_mem, if_neg notStep, chainValueState_mem, if_neg notHigh, if_neg notLow]
  refine ⟨chainDigitState (chainValueState s),
    ordinary_trans verify s _ _ 16 7 (chainValueState_block s pc valid0 valid8)
      (chainDigitState_block _ valuePC digitValid), ?_, ?_, ?_, ?_, ?_⟩
  · rw [chainDigitState_pc, valuePC]; rfl
  · constructor
    · rw [memory _ (by decide) (by decide) (by decide)]; exact levelEq
    · rw [memory _ (by decide) (by decide) (by decide)]; exact leafEq
    · rw [memory _ (by decide) (by decide) (by decide)]; exact chainEq
    · rw [chainDigitState_mem, if_pos rfl, chainValueState_chain, chainEq, digitAddress,
        chainValueState_digit, digitEq]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
      have := digit.isLt
      omega
    · intro i
      rw [memory _ (by fin_cases i <;> decide) (by fin_cases i <;> decide) (by fin_cases i <;> decide)]
      exact indexEq i
    · intro i
      fin_cases i
      · change (chainDigitState (chainValueState s)).getMem 0x80510 = _
        rw [chainDigitState_mem, if_neg (by decide), chainValueState_mem, if_neg (by decide), if_pos rfl]
        exact value0
      · change (chainDigitState (chainValueState s)).getMem 0x80518 = _
        rw [chainDigitState_mem, if_neg (by decide), chainValueState_mem, if_pos rfl]
        exact value8
  · exact (chainDigitState_stack _).1.trans (chainValueState_stack s).1
  · exact (chainDigitState_stack _).2.trans (chainValueState_stack s).2
  · intro a low high step
    exact memory a step high low

/-- info: 'SigGolfCandidate.Hypertree.Verifying.chain_prepare' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms chain_prepare

end SigGolfCandidate.Hypertree.Verifying
