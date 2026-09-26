import SigGolfCandidate.Hypertree.PreludeCleanup
namespace SigGolfCandidate.Hypertree.Signing.Prelude
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 Keygen
set_option maxRecDepth 4096

theorem prepare_signer (hash : Hash)
    (s : MachineState) (secretKey : SecretKey)
    (pc : s.pc = 0x1c70) (stack : s.getReg .x2 = 0x1000000)
    (lo : s.getMem 0x80500 = 0) (hi : s.getMem 0x80508 = 0)
    (index : ∀ i : Fin 3, s.getMem (wordAddress 0x80408 i.val) =
      (BitVec.ofNat 192 0).extractLsb' (64*i.val) 64)
    (secret : ∀ i : Fin 4, s.getMem (wordAddress 0x20 i.val) =
      secretKey.extractLsb' (64*i.val) 64)
    (selector : s.getMem 0x80420 = 0) :
    ∃ final instructions cycles,
      Trace hash signPrelude s instructions cycles 739 761 final ∧
      instructions ≤ 100421 ∧ cycles ≤ 105770 ∧
      final.pc = 0x1004 ∧ final.getReg .x2 = 0x1000000 ∧ final.getReg .x6 = 1 ∧
      (∀ i : Fin 2, final.getMem (wordAddress 0x40 i.val) =
        (Reference.keygen hash secretKey).extractLsb' (64*i.val) 64) ∧
      final.getMem 0x80400 = 0 ∧
      (∀ i : Fin 3, final.getMem (wordAddress 0x80408 i.val) = 0) ∧
      (∀ i : Fin 2, final.getMem (wordAddress 0x80500 i.val) = 0) ∧
      (∀ a : Nat, a % 8 = 0 → a + 8 ≤ 0x20080 → a ≠ 0x40 → a ≠ 0x48 →
        final.getMem (BitVec.ofNat 64 a) = s.getMem (BitVec.ofNat 64 a)) := by
  obtain ⟨root, n, c, run, nb, cb, rpc, rsp, pk, frame⟩ :=
    derive_public_key hash s secretKey pc stack lo hi index secret selector
  obtain ⟨copied, copy, cpc, words, _, csp, copyFrame⟩ := root_copy root rpc
  refine ⟨cleanupState copied, n+42, c+42, ?_, by omega, by omega,
    cleanup_pc copied cpc, ?_, cleanup_ready copied, ?_, ?_, ?_, ?_, ?_⟩
  · convert run.trans (copy.trace.trans (cleanup_block copied cpc).trace) using 1 <;> omega
  · rw [cleanup_stack, csp, rsp]
  · intro i
    rw [cleanup_low copied _ (by fin_cases i <;> decide), words i]
    exact pk i
  · rw [cleanup_mem]; rfl
  · intro i; fin_cases i <;> rw [cleanup_mem] <;> rfl
  · intro i; fin_cases i <;> rw [cleanup_mem] <;> rfl
  · intro a aligned bound h0 h1
    have low : (BitVec.ofNat 64 a).toNat < 0x80000 := by simp only [BitVec.toNat_ofNat]; omega
    rw [cleanup_low copied _ low, copyFrame]
    · exact frame a aligned bound
    · intro eq
      apply h0
      have h := congrArg BitVec.toNat eq
      change a % 2^64 = 64 at h
      omega
    · intro eq
      apply h1
      have h := congrArg BitVec.toNat eq
      change a % 2^64 = 72 at h
      omega


/-- info: 'SigGolfCandidate.Hypertree.Signing.Prelude.prepare_signer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms prepare_signer
end SigGolfCandidate.Hypertree.Signing.Prelude
