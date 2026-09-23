import SigGolfCandidate.Hypertree.VerifyChainControl

namespace SigGolfCandidate.Hypertree.Verifying
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 Keygen Signing ChainLoopControl
set_option maxRecDepth 4096

structure ChainData (s : MachineState) (level tree : Nat) (side : Bool) (chain : Reference.Chain)
    (step : Nat) (value : Reference.Digest) : Prop where
  levelEq : s.getMem 0x80400 = BitVec.ofNat 64 level
  leafEq : s.getMem 0x80428 = BitVec.ofNat 64 (Reference.sideNumber side)
  chainEq : s.getMem 0x80430 = BitVec.ofNat 64 chain.val
  stepEq : s.getMem 0x80438 = BitVec.ofNat 64 step
  indexEq : ∀ i : Fin 3, s.getMem (wordAddress 0x80408 i.val) = (BitVec.ofNat 192 tree).extractLsb' (64*i.val) 64
  valueEq : ∀ i : Fin 2, s.getMem (wordAddress 0x80510 i.val) = value.extractLsb' (64*i.val) 64

def OutsideChainWork (a : Word) : Prop :=
  (∀ i : Fin 8, a ≠ wordAddress 0x80000 i.val) ∧
  (∀ i : Fin 4, a ≠ wordAddress 0x80300 i.val) ∧
  (∀ i : Fin 2, a ≠ wordAddress 0x80510 i.val) ∧ a ≠ 0x80438

theorem ChainData.check (s : MachineState) (level tree : Nat) (side : Bool) (chain : Reference.Chain)
    (step : Nat) (value : Reference.Digest) (data : ChainData s level tree side chain step value) :
    ChainData (ChainLoopControl.check s) level tree side chain step value := by
  constructor
  · simpa only [check_mem] using data.levelEq
  · simpa only [check_mem] using data.leafEq
  · simpa only [check_mem] using data.chainEq
  · simpa only [check_mem] using data.stepEq
  · intro i; simpa only [check_mem] using data.indexEq i
  · intro i; simpa only [check_mem] using data.valueEq i

/-- One verifier chain iteration, including its test, actual HASH core and increment. -/
theorem chain_step (hash : Hash) (s : MachineState) (level tree step : Nat)
    (side : Bool) (chain : Reference.Chain) (value : Reference.Digest)
    (pc : s.pc = 0x14ec) (bound : step < 7) (data : ChainData s level tree side chain step value) :
    ∃ final, Trace hash verify s 96 103 1 1 final ∧ final.pc = 0x14ec ∧
      ChainData final level tree side chain (step+1) (Reference.chainHash hash level tree side chain step value) ∧
      final.getReg .x1 = s.getReg .x1 ∧ final.getReg .x2 = s.getReg .x2 ∧
      (∀ a, OutsideChainWork a → final.getMem a = s.getMem a) := by
  have ne : s.getMem 0x80438 ≠ 7 := by
    rw [data.stepEq]
    intro eq
    have h := congrArg BitVec.toNat eq
    change step % 2^64 = 7 at h
    omega
  have checkedPC : (check s).pc = 0x1500 := by rw [check_pc, pc, if_neg ne]; rfl
  have checked := data.check
  obtain ⟨hashed, core, hashedPC, valueOut, ra, sp, frame⟩ := KeygenChain.compute verify hash 0x1500 verify_chain_code
    (check s) checkedPC level tree step side chain value checked.levelEq checked.leafEq checked.chainEq
    checked.stepEq checked.indexEq checked.valueEq
  have hashedPC' : hashed.pc = 0x161c := hashedPC
  have tail := increment_block verify 0x161c (-332) verify_chain_increment hashed hashedPC'
  have keep (a : Word)
      (hi : ∀ i : Fin 6, a ≠ wordAddress 0x80000 i.val)
      (ha : ∀ i : Fin 4, a ≠ wordAddress 0x80300 i.val)
      (hv : ∀ i : Fin 2, a ≠ wordAddress 0x80510 i.val) : hashed.getMem a = s.getMem a := by
    rw [frame a hi ha hv, check_mem]
  have nextLevel : hashed.getMem 0x80400 = s.getMem 0x80400 := keep _ (by decide) (by decide) (by decide)
  have nextLeaf : hashed.getMem 0x80428 = s.getMem 0x80428 := keep _ (by decide) (by decide) (by decide)
  have nextChain : hashed.getMem 0x80430 = s.getMem 0x80430 := keep _ (by decide) (by decide) (by decide)
  have nextStep : hashed.getMem 0x80438 = s.getMem 0x80438 := keep _ (by decide) (by decide) (by decide)
  refine ⟨increment hashed (-332), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ((check_block verify 0x14ec verify_chain_check s pc).trace.trans core).trans tail.trace
  · rw [increment_pc, hashedPC']; rfl
  · constructor
    · rw [increment_mem, if_neg (by decide), nextLevel]; exact data.levelEq
    · rw [increment_mem, if_neg (by decide), nextLeaf]; exact data.leafEq
    · rw [increment_mem, if_neg (by decide), nextChain]; exact data.chainEq
    · rw [increment_mem, if_pos rfl, nextStep, data.stepEq, BitVec.ofNat_add]; rfl
    · intro i
      rw [increment_mem, if_neg (by fin_cases i <;> decide), keep]
      · exact data.indexEq i
      · intro j; fin_cases i <;> fin_cases j <;> decide
      · intro j; fin_cases i <;> fin_cases j <;> decide
      · intro j; fin_cases i <;> fin_cases j <;> decide
    · intro i
      rw [increment_mem, if_neg (by fin_cases i <;> decide)]
      exact valueOut i
  · exact (increment_stack hashed (-332)).1.trans (ra.trans (check_stack s).1)
  · exact (increment_stack hashed (-332)).2.trans (sp.trans (check_stack s).2)
  · intro a outside
    rw [increment_mem, if_neg outside.2.2.2, keep a (fun i => outside.1 ⟨i.val, by omega⟩) outside.2.1 outside.2.2.1]

/-- info: 'SigGolfCandidate.Hypertree.Verifying.chain_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms chain_step

end SigGolfCandidate.Hypertree.Verifying
