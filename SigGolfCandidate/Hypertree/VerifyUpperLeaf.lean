import SigGolfCandidate.Hypertree.VerifyLeafLoop
import SigGolfCandidate.Hypertree.KeygenLeafExecution
import SigGolfCandidate.Hypertree.VerifyNode

namespace SigGolfCandidate.Hypertree.Verifying
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 Keygen Signing
set_option maxRecDepth 4096

theorem verify_leaf_hash_code : KeygenLeaf.Code verify 0x1690 := by decide

def OutsideUpperLeaf (side : Bool) (a : Word) : Prop :=
  OutsideLeafWork a ∧ ∀ i : Fin 2, a ≠ KeygenSavePublic.wordAddress side i.val

/-- All verifier chains, leaf compression, public-slot write, and the actual saved return. -/
theorem upper_leaf_body (hash : Hash) (s : MachineState) (level tree : Nat) (side : Bool) (base : Nat)
    (message : Reference.Digest) (values : Reference.Chain → Reference.Digest)
    (pc : s.pc = 0x1490) (data : LeafData s level tree side base message values)
    (counter : s.getMem 0x80430 = 0) (sp : s.getReg .x2 = 0xffffe0)
    (aligned : base % 8 = 0) (bound : base+736 ≤ 0x80000) :
    ∃ final steps cycles calls, Trace hash verify s steps cycles (calls+1) (calls+12) final ∧
      steps ≤ 33781 ∧ cycles ≤ 36130 ∧ calls ≤ 322 ∧
      final.pc = s.getMem 0xffffe0 &&& ~~~1#64 ∧ final.getReg .x2 = 0xfffff0 ∧
      (∀ i : Fin 2, final.getMem (KeygenSavePublic.wordAddress side i.val) =
        (Reference.compressLeaf hash level tree side (recoveredEndpoint hash level tree side message values)).extractLsb' (64*i.val) 64) ∧
      (∀ a, OutsideUpperLeaf side a → final.getMem a = s.getMem a) := by
  obtain ⟨ready, steps, cycles, calls, loop, hsteps, hcycles, hcalls, readyPC, _,
    readyData, endpoints, _, readySP, loopFrame⟩ := recover_all_chains hash s level tree side base message values
      pc data counter aligned bound
  have words : ∀ i : Fin 92, ready.getMem (wordAddress 0x80800 i.val) =
      KeygenLeafHeader.endpointWord (recoveredEndpoint hash level tree side message values) i := by
    intro i
    have addr : KeygenEndpoint.endpointAddress (i.val/2) (i.val%2) = wordAddress 0x80800 i.val := by
      unfold KeygenEndpoint.endpointAddress wordAddress
      apply congrArg (BitVec.ofNat 64)
      omega
    rw [← addr]
    exact endpoints ⟨i.val/2, by have := i.isLt; omega⟩ ⟨i.val%2, by omega⟩
  have stack : ready.getReg .x2 = 0xffffe0 := readySP.trans sp
  obtain ⟨final, suffix, finalPC, finalSP, output, suffixFrame⟩ := KeygenLeaf.compute_return verify hash 0x1690
    verify_leaf_hash_code leaf_return_code ready readyPC level tree side
    (recoveredEndpoint hash level tree side message values) readyData.levelEq readyData.leafEq readyData.indexEq words
    (by rw [stack]; decide) (by rw [stack]; decide) (by rw [stack]; decide)
    (by rw [stack]; cases side <;> decide)
  refine ⟨final, steps+615, cycles+710, calls, loop.trans suffix, by omega, by omega, hcalls, ?_, ?_, output, ?_⟩
  · rw [finalPC, stack, loopFrame _ (by unfold OutsideLeafWork; decide)]
  · rw [finalSP, stack]; rfl
  · intro a outside
    exact (suffixFrame a outside.1.1 outside.1.2.1 outside.2).trans (loopFrame a outside.1)

/-- info: 'SigGolfCandidate.Hypertree.Verifying.upper_leaf_body' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms upper_leaf_body

end SigGolfCandidate.Hypertree.Verifying
