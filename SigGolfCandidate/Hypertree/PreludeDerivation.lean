import SigGolfCandidate.Hypertree.PreludeDeriveRoot
import SigGolfCandidate.Hypertree.SignPreludeCode
namespace SigGolfCandidate.Hypertree.Signing.Prelude
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 Keygen
set_option maxRecDepth 4096

theorem derive_public_key (hash : Hash)
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
      instructions ≤ 100379 ∧ cycles ≤ 105728 ∧
      final.pc = 0x1cac ∧ final.getReg .x2 = 0x1000000 ∧
      (∀ i : Fin 2, final.getMem (wordAddress 0x80500 i.val) =
        (Reference.keygen hash secretKey).extractLsb' (64*i.val) 64) ∧
      (∀ a : Nat, a % 8 = 0 → a + 8 ≤ 0x20080 →
        final.getMem (BitVec.ofNat 64 a) = s.getMem (BitVec.ofNat 64 a)) := by
  obtain ⟨ready, entry, rpc, ra, sp, data, ptr, enabled, selected, digits, entryFrame⟩ :=
    prelude_entry s secretKey pc stack lo hi index secret selector
  obtain ⟨final, n, c, run, nb, cb, fpc, fsp, root, frame⟩ :=
    derive_root hash ready secretKey rpc sp data ptr enabled selected digits
  refine ⟨final, 469+n, 469+c, entry.trace.trans run, by omega, by omega, ?_, ?_, root, ?_⟩
  · rw [fpc, ra]; rfl
  · rw [fsp, sp]
  · intro a aligned bound
    rw [frame _ (by simp only [BitVec.toNat_ofNat]; omega)]
    exact entryFrame a aligned bound

/-- info: 'SigGolfCandidate.Hypertree.Signing.Prelude.derive_public_key' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms derive_public_key
end SigGolfCandidate.Hypertree.Signing.Prelude
