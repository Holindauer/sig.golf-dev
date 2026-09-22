import SigGolfCandidate.Hypertree.KeygenVerifyCountLeaf
import SigGolfCandidate.Hypertree.SecurityVerifyCost

namespace SigGolfCandidate.Hypertree.KeygenVerifyCount
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 Keygen Signing Verifying
set_option maxRecDepth 4096

theorem upper_leaf_calls (level : Nat) (message : Reference.Digest) (nonzero : level ≠ 0) :
    chainCalls message+1 = SecurityVerifyCost.leafCalls level message := by
  simp only [SecurityVerifyCost.leafCalls,if_neg nonzero,chainCalls,Nat.add_comm]

/-- The exact upper verifier leaf executes precisely the reference program's H-call count. -/
theorem upper_leaf_call_counted (hash : Hash) (s : MachineState) (level tree : Nat) (side : Bool) (base : Nat)
    (message : Reference.Digest) (signature : Reference.LayerSignature)
    (pc : s.pc = 0x1458) (sp : s.getReg .x2 = 0xfffff0)
    (data : LeafData s level tree side base message signature.values)
    (nonzero : BitVec.ofNat 64 level ≠ 0) (aligned : base % 8 = 0) (bound : base+736 ≤ 0x80000) :
    ∃ final steps cycles, Trace hash verify s steps cycles (SecurityVerifyCost.leafCalls level message)
        (SecurityVerifyCost.leafCalls level message+11) final ∧
      steps ≤ 33795 ∧ cycles ≤ 36144 ∧ SecurityVerifyCost.leafCalls level message ≤ 323 ∧
      final.pc = s.getReg .x1 &&& ~~~1#64 ∧ final.getReg .x2 = s.getReg .x2 ∧
      (∀ i : Fin 2, final.getMem (KeygenSavePublic.wordAddress side i.val) =
        (Reference.recoverLeaf hash level tree side message signature).extractLsb' (64*i.val) 64) ∧
      (∀ a, a ≠ 0xffffe0 → OutsideUpperLeaf side a → final.getMem a = s.getMem a) := by
  obtain ⟨final,steps,cycles,calls,run,hsteps,hcycles,hcalls,fpc,fsp,words,frame,eq⟩ :=
    upper_leaf_call_exact hash s level tree side base message signature pc sp data nonzero aligned bound
  have nz : level ≠ 0 := by intro h; apply nonzero; rw [h]; rfl
  have count : calls+1 = SecurityVerifyCost.leafCalls level message := by rw [eq,upper_leaf_calls level message nz]
  refine ⟨final,steps,cycles,?_,hsteps,hcycles,by omega,fpc,fsp,words,frame⟩
  convert run using 1 <;> omega

/-- info: 'SigGolfCandidate.Hypertree.KeygenVerifyCount.upper_leaf_call_counted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms upper_leaf_call_counted

end SigGolfCandidate.Hypertree.KeygenVerifyCount
