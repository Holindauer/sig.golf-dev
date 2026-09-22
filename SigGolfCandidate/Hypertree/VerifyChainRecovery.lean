import SigGolfCandidate.Hypertree.VerifyChainInput
import SigGolfCandidate.Hypertree.KeygenEndpoint

namespace SigGolfCandidate.Hypertree.Verifying
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 Keygen Signing
set_option maxRecDepth 4096

theorem chainSource_eq (s : MachineState) (base : Nat) (chain : Reference.Chain)
    (pointer : s.getMem 0x80448 = BitVec.ofNat 64 base)
    (counter : s.getMem 0x80430 = BitVec.ofNat 64 chain.val) :
    chainSource s = BitVec.ofNat 64 (base + 16 * chain.val) := by
  unfold chainSource
  rw [pointer, counter, KeygenDomain.shift_ofNat]
  change BitVec.ofNat 64 base + BitVec.ofNat 64 (chain.val * 16) = _
  rw [← BitVec.ofNat_add]
  congr 1
  omega

theorem chainSource_safe (s : MachineState) (base : Nat) (chain : Reference.Chain)
    (pointer : s.getMem 0x80448 = BitVec.ofNat 64 base)
    (counter : s.getMem 0x80430 = BitVec.ofNat 64 chain.val)
    (aligned : base % 8 = 0) (bound : base + 16 * chain.val + 16 ≤ MEMORY_BYTES) :
    accessValid (chainSource s) 8 = true ∧ accessValid (chainSource s + 8) 8 = true := by
  rw [chainSource_eq s base chain pointer counter]
  have sum : BitVec.ofNat 64 (base + 16 * chain.val) + 8 =
      BitVec.ofNat 64 (base + 16 * chain.val + 8) := (BitVec.ofNat_add _ _).symm
  rw [sum]
  have small : base + 16 * chain.val < 2^64 := by simp only [MEMORY_BYTES] at bound; omega
  have smallNext : base + 16 * chain.val + 8 < 2^64 := by simp only [MEMORY_BYTES] at bound; omega
  simp [accessValid, rangeValid, BitVec.toNat_ofNat, Nat.add_mod, Nat.mul_mod, aligned]
  omega

/-- Witness loading and the full remaining chain computation, with exact cost and endpoint. -/
theorem recover_chain_fragment (hash : Hash) (s : MachineState) (level tree : Nat) (side : Bool)
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
    ∃ final, Trace hash verify s (96*(7-digit.val)+28) (103*(7-digit.val)+28) (7-digit.val) (7-digit.val) final ∧
      final.pc = 0x163c ∧
      ChainData final level tree side chain 7
        (walk (Reference.chainHash hash level tree side chain) digit.val (7-digit.val) value) ∧
      final.getReg .x1 = s.getReg .x1 ∧ final.getReg .x2 = s.getReg .x2 ∧
      (∀ a, OutsideChainWork a → final.getMem a = s.getMem a) := by
  obtain ⟨ready, prepare, readyPC, readyData, readyRA, readySP, prepareFrame⟩ := chain_prepare s level tree side
    chain digit value pc valid0 valid8 levelEq leafEq chainEq indexEq value0 value8 digitEq
  obtain ⟨final, loop, finalPC, finalData, finalRA, finalSP, loopFrame⟩ :=
    chain_from_digit hash ready level tree side chain digit value readyPC readyData
  refine ⟨final, ?_, finalPC, finalData, finalRA.trans readyRA, finalSP.trans readySP, ?_⟩
  · convert prepare.trace.trans loop using 1 <;> omega
  · intro a outside
    rw [loopFrame a outside]
    exact prepareFrame a (outside.2.2.1 0) (outside.2.2.1 1) outside.2.2.2

/-- The verifier's endpoint store is the shared checked store-and-advance block. -/
theorem verify_endpoint_code : KeygenEndpoint.Code verify 0x163c (-508) := by decide

/-- info: 'SigGolfCandidate.Hypertree.Verifying.recover_chain_fragment' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms recover_chain_fragment

end SigGolfCandidate.Hypertree.Verifying
