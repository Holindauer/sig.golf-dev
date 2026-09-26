import SigGolfCandidate.Hypertree.SignPreludeSetup
namespace SigGolfCandidate.Hypertree.Signing
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 OracleComp Keygen

/-- Reconstruct all aligned words below the digit buffer from the encoder byte frame. -/
theorem encode_low_word_frame (s final : MachineState)
    (stack : s.getReg .x2 = 0x1000000)
    (frame : ∀ a, (∀ i : Fin 46, a ≠ BitVec.ofNat 64 (0x80600 + i.val)) →
      final.getByte a = (Keygen.enterState s).getByte a)
    (a : Nat) (aligned : a % 8 = 0) (low : a + 8 ≤ 0x80600) :
    final.getMem (BitVec.ofNat 64 a) = s.getMem (BitVec.ofNat 64 a) := by
  have words := word_eq_of_bytes (Keygen.enterState s) final a aligned (by omega) (fun i =>
    frame _ (by
      intro j eq
      have h := congrArg BitVec.toNat eq
      have hi := i.isLt
      have hj := j.isLt
      simp only [BitVec.toNat_ofNat] at h
      omega))
  rw [words, Keygen.enter_mem, stack]
  apply if_neg
  intro eq
  change BitVec.ofNat 64 a = 0xfffff0#64 at eq
  have h := congrArg BitVec.toNat eq
  simp only [BitVec.toNat_ofNat] at h
  norm_num at h
  omega

theorem derive_encode (image : Image) (setup : DeriveSetupCode image)
    (code : EncodeCode image 0x1340) (s : MachineState)
    (pc : s.pc = 0x1c70) (stack : s.getReg .x2 = 0x1000000)
    (lo : s.getMem 0x80500 = 0) (hi : s.getMem 0x80508 = 0) :
    ∃ final, OrdinarySteps image s 468 final ∧ final.pc = 0x1ca8 ∧
      final.getReg .x2 = s.getReg .x2 ∧
      (∀ i : Reference.Chain, final.getByte (BitVec.ofNat 64 (0x80600 + i.val)) =
        BitVec.ofNat 8 (Reference.digit 0 i).val) ∧
      (∀ a : Nat, a % 8 = 0 → a + 8 ≤ 0x80600 →
        final.getMem (BitVec.ofNat 64 a) = (deriveSetupState s).getMem (BitVec.ofNat 64 a)) := by
  have initial := deriveSetup_block image setup s pc
  have sp : (deriveSetupState s).getReg .x2 = 0x1000000 := by
    rw [deriveSetup_stack, stack]
  have low : (deriveSetupState s).getMem 0x80500 = (0 : Reference.Digest).extractLsb' 0 64 := by
    rw [deriveSetup_frame s _ (by decide) (by decide) (by decide), lo]; rfl
  have high : (deriveSetupState s).getMem 0x80508 = (0 : Reference.Digest).extractLsb' 64 64 := by
    rw [deriveSetup_frame s _ (by decide) (by decide) (by decide), hi]; rfl
  obtain ⟨final, steps, ret, spfinal, digits, frame⟩ :=
    encode_subroutine image 0x1340 code (deriveSetupState s) 0
      (deriveSetup_pc s pc) sp low high
  refine ⟨final, ordinary_trans image s _ final 14 454 initial steps, ?_, ?_, digits, ?_⟩
  · rw [ret, deriveSetup_return s pc]; rfl
  · rw [spfinal, deriveSetup_stack]
  · intro a aligned bound
    exact encode_low_word_frame _ _ sp frame a aligned bound

/-- info: 'SigGolfCandidate.Hypertree.Signing.encode_low_word_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms encode_low_word_frame
/-- info: 'SigGolfCandidate.Hypertree.Signing.derive_encode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms derive_encode
end SigGolfCandidate.Hypertree.Signing
