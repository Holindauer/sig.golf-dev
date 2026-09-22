import SigGolfCandidate.Hypertree.VerifyLoopState

namespace SigGolfCandidate.Hypertree.Verifying
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 Keygen Signing
set_option maxRecDepth 4096

/-- Optional message encoding prepares every input of the complete tree verifier. -/
theorem prepare_tree (s : MachineState) (level index : Nat) (side : Bool)
    (current : Reference.Digest) (witness : Bytes signatureBytes)
    (pc : s.pc = 0x11bc) (small : level < 160)
    (data : LoopData s level index current witness)
    (selector : s.getMem 0x80420 = BitVec.ofNat 64 (Reference.sideNumber side)) :
    ∃ ready steps, OrdinarySteps verify s steps ready ∧ steps ≤ 460 ∧
      ready.pc = 0x12f0 ∧ ready.getReg .x1 = 0x11d4 ∧ ready.getReg .x2 = 0x1000000 ∧
      LayerData ready level index (0x3d3b0+layerOffset level) side current (wireLayer witness level) ∧
      LowFrame s ready := by
  obtain ⟨ready, run, readyPC, readyRA, readySP, digits, frame⟩ :=
    dispatch_to_tree verify 0x11bc verify_dispatch_code verify_encode_code (by decide) s current pc
      data.stack (data.currentEq 0) (data.currentEq 1)
  have words (address : Nat) (aligned : address % 8 = 0) (bound : address+8 < 2^64)
      (separate : address+8 ≤ 0x80600 ∨ 0x80630 ≤ address) (saved : address ≠ 0xfffff0) :
      ready.getMem (BitVec.ofNat 64 address) = s.getMem (BitVec.ofNat 64 address) :=
    dispatch_frame_words s ready data.stack frame address aligned bound separate saved
  have lowFrame : LowFrame s ready := by
    intro address aligned bound
    exact words address aligned (by omega) (Or.inl (by omega)) (by omega)
  have stored : WitnessStored ready witness := data.witnessEq.transfer_words s ready witness lowFrame
  refine ⟨ready, _, run, ?_, readyPC, readyRA, readySP.trans data.stack, ?_, lowFrame⟩
  · split <;> decide
  · constructor
    · exact (words 0x80400 (by decide) (by decide) (by decide) (by decide)).trans data.levelEq
    · intro i
      have keep := words (0x80408+8*i.val) (by omega) (by have := i.isLt; omega)
        (Or.inl (by have := i.isLt; omega)) (by have := i.isLt; omega)
      change ready.getMem (wordAddress 0x80408 i.val) = s.getMem (wordAddress 0x80408 i.val) at keep
      rw [keep]
      exact data.indexEq i
    · exact (words 0x80448 (by decide) (by decide) (by decide) (by decide)).trans data.pointerEq
    · exact (words 0x80420 (by decide) (by decide) (by decide) (by decide)).trans selector
    · intro chain relevant i
      simpa only [Nat.add_assoc] using wire_layer_value ready witness stored level small chain relevant i
    · intro nonzero chain
      apply digits ?_ chain
      rw [data.levelEq]
      exact (level_word_zero level small).not.mpr nonzero
    · intro i
      simpa only [Nat.add_assoc] using wire_layer_sibling ready witness stored level small i

/-- info: 'SigGolfCandidate.Hypertree.Verifying.prepare_tree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms prepare_tree

end SigGolfCandidate.Hypertree.Verifying
