import SigGolfCandidate.Hypertree.SignTree
namespace SigGolfCandidate.Hypertree.Signing
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 Keygen Verifying
set_option maxRecDepth 4096

/-- Reuse the enabled signing tree to derive the public key. The temporary
signature is below scratch space; secret key and message memory are preserved. -/
theorem derive_root (hash : Hash) (s : MachineState) (secretKey : SecretKey)
    (pc : s.pc = 0x13c8) (sp : s.getReg .x2 = 0x1000000)
    (data : TreeContext s secretKey 159 0)
    (ptr : s.getMem 0x80448 = 0x20080) (enabled : s.getMem 0x80440 ≠ 0)
    (selector : s.getMem 0x80420 = 0)
    (digits : ∀ chain : Reference.Chain,
      s.getByte (BitVec.ofNat 64 (0x80600 + chain.val)) =
        BitVec.ofNat 8 (Reference.digit (0 : Reference.Digest) chain).val) :
    ∃ final instructions cycles,
      Trace hash sign s instructions cycles 739 761 final ∧
      instructions ≤ 99910 ∧ cycles ≤ 105259 ∧
      final.pc = s.getReg .x1 &&& ~~~1#64 ∧ final.getReg .x2 = s.getReg .x2 ∧
      (∀ i : Fin 2, final.getMem (wordAddress 0x80500 i.val) =
        (Reference.keygen hash secretKey).extractLsb' (64*i.val) 64) ∧
      (∀ a, a.toNat < 0x20080 → final.getMem a = s.getMem a) := by
  obtain ⟨final,n,c,run,nb,cb,fpc,fsp,root,_stored,frame⟩ :=
    sign_tree hash s secretKey 0x20080 159 0 0 false pc sp (by decide)
      (by unfold CapturePointerValid; decide) data ptr enabled selector (fun _ => digits)
  refine ⟨final,n,c,run,nb,cb,fpc,fsp,root,?_⟩
  intro a low
  apply frame a (outsideTreeWork_low a (by omega))
  exact Or.inl low

/-- info: 'SigGolfCandidate.Hypertree.Signing.derive_root' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms derive_root
end SigGolfCandidate.Hypertree.Signing
