import SigGolfCandidate.Hypertree.VerifyLeafPrologue

namespace SigGolfCandidate.Hypertree.Verifying
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 Keygen Signing
set_option maxRecDepth 4096

/-- The checked leaf prologue initializes the chain loop and saves its return address. -/
theorem prepare_upper_leaf (hash : Hash) (s : MachineState) (level tree : Nat) (side : Bool) (base : Nat)
    (message : Reference.Digest) (signature : Reference.LayerSignature)
    (pc : s.pc = 0x1458) (sp : s.getReg .x2 = 0xfffff0)
    (data : LeafData s level tree side base message signature.values)
    (nonzero : BitVec.ofNat 64 level ≠ 0) (_aligned : base % 8 = 0) (bound : base+736 ≤ 0x80000) :
    ∃ ready, Trace hash verify s 14 14 0 0 ready ∧ ready.pc = 0x1490 ∧
      LeafData ready level tree side base message signature.values ∧ ready.getMem 0x80430 = 0 ∧
      ready.getReg .x2 = 0xffffe0 ∧ ready.getMem 0xffffe0 = s.getReg .x1 ∧
      (∀ a, a ≠ 0xffffe0 → a ≠ 0x80430 → a ≠ 0x80438 → ready.getMem a = s.getMem a) := by
  exact ⟨VerifyLeafPrologue.ready s, (VerifyLeafPrologue.block s pc sp).trace,
    VerifyLeafPrologue.pc s pc sp level nonzero data.levelEq,
    VerifyLeafPrologue.context s sp level tree side base message signature data bound,
    VerifyLeafPrologue.counter s, VerifyLeafPrologue.stack s sp, VerifyLeafPrologue.saved s sp,
    VerifyLeafPrologue.frame s sp⟩

/-- Complete upper-leaf verification from call entry through the protected return. -/
theorem upper_leaf_call (hash : Hash) (s : MachineState) (level tree : Nat) (side : Bool) (base : Nat)
    (message : Reference.Digest) (signature : Reference.LayerSignature)
    (pc : s.pc = 0x1458) (sp : s.getReg .x2 = 0xfffff0)
    (data : LeafData s level tree side base message signature.values)
    (nonzero : BitVec.ofNat 64 level ≠ 0) (aligned : base % 8 = 0) (bound : base+736 ≤ 0x80000) :
    ∃ final steps cycles calls, Trace hash verify s steps cycles (calls+1) (calls+12) final ∧
      steps ≤ 33795 ∧ cycles ≤ 36144 ∧ calls ≤ 322 ∧
      final.pc = s.getReg .x1 &&& ~~~1#64 ∧ final.getReg .x2 = s.getReg .x2 ∧
      (∀ i : Fin 2, final.getMem (KeygenSavePublic.wordAddress side i.val) =
        (Reference.recoverLeaf hash level tree side message signature).extractLsb' (64*i.val) 64) ∧
      (∀ a, a ≠ 0xffffe0 → OutsideUpperLeaf side a → final.getMem a = s.getMem a) := by
  obtain ⟨ready, pre, rpc, rdata, counter, rsp, saved, entryFrame⟩ :=
    prepare_upper_leaf hash s level tree side base message signature pc sp data nonzero aligned bound
  obtain ⟨final, steps, cycles, calls, body, hsteps, hcycles, hcalls, finalPC, finalSP, output, frame⟩ :=
    upper_leaf_body hash ready level tree side base message signature.values rpc rdata counter rsp aligned bound
  refine ⟨final, 14+steps, 14+cycles, calls, ?_, by omega, by omega, hcalls, ?_, ?_, ?_, ?_⟩
  · simpa only [Nat.zero_add] using pre.trans body
  · rw [finalPC, saved]
  · rw [finalSP, sp]
  · intro i
    have nz : level ≠ 0 := by intro eq; apply nonzero; rw [eq]; rfl
    rw [Reference.recoverLeaf, if_neg nz]
    change final.getMem (KeygenSavePublic.wordAddress side i.val) =
      (Reference.compressLeaf hash level tree side (recoveredEndpoint hash level tree side message signature.values)).extractLsb' (64*i.val) 64
    exact output i
  · intro a hs outside
    rw [frame a outside, entryFrame a hs outside.1.2.2.2.2.1 outside.1.2.2.2.2.2]

/-- info: 'SigGolfCandidate.Hypertree.Verifying.upper_leaf_call' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms upper_leaf_call

end SigGolfCandidate.Hypertree.Verifying
