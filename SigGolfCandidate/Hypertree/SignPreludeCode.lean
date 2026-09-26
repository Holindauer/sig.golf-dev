import SigGolfCandidate.Hypertree.ImagesPrelude
import SigGolfCandidate.Hypertree.SignPreludeEntry
namespace SigGolfCandidate.Hypertree.Signing
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 Keygen
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

theorem prelude_setup_code : DeriveSetupCode signPrelude := by unfold DeriveSetupCode; decide

theorem prelude_call_code :
    instructionAt signPrelude 0x1ca8 = some (.base (.JAL .x1 (-2272))) := by decide

theorem prelude_encode_code : EncodeCode signPrelude 0x1340 := by
  refine ⟨by decide, ?_, ?_, ?_, by decide⟩
  all_goals
    intro s i pc
    simp only [fetch, pc]
    fin_cases i <;> decide

/-- Body words are retained exactly, but this alone is not trace transport. -/
theorem prelude_body_words : (signPrelude.code.drop 1).take 795 = sign.code.drop 1 := by decide
theorem prelude_entry
    (s : MachineState) (secretKey : SecretKey)
    (pc : s.pc = 0x1c70) (stack : s.getReg .x2 = 0x1000000)
    (lo : s.getMem 0x80500 = 0) (hi : s.getMem 0x80508 = 0)
    (index : ∀ i : Fin 3, s.getMem (wordAddress 0x80408 i.val) =
      (BitVec.ofNat 192 0).extractLsb' (64*i.val) 64)
    (secret : ∀ i : Fin 4, s.getMem (wordAddress 0x20 i.val) =
      secretKey.extractLsb' (64*i.val) 64)
    (selector : s.getMem 0x80420 = 0) :
    ∃ final, OrdinarySteps signPrelude s 469 final ∧ final.pc = 0x13c8 ∧
      final.getReg .x1 = 0x1cac ∧ final.getReg .x2 = 0x1000000 ∧
      TreeContext final secretKey 159 0 ∧
      final.getMem 0x80448 = 0x20080 ∧ final.getMem 0x80440 ≠ 0 ∧
      final.getMem 0x80420 = 0 ∧
      (∀ i : Reference.Chain, final.getByte (BitVec.ofNat 64 (0x80600 + i.val)) =
        BitVec.ofNat 8 (Reference.digit 0 i).val) ∧
      (∀ a : Nat, a % 8 = 0 → a + 8 ≤ 0x20080 →
        final.getMem (BitVec.ofNat 64 a) = s.getMem (BitVec.ofNat 64 a)) := by
  exact derive_entry signPrelude prelude_setup_code prelude_encode_code prelude_call_code
    s secretKey pc stack lo hi index secret selector

/-- info: 'SigGolfCandidate.Hypertree.Signing.prelude_entry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms prelude_entry
end SigGolfCandidate.Hypertree.Signing
