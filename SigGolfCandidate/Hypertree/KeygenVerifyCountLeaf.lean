import SigGolfCandidate.Hypertree.KeygenVerifyCountLoop
import SigGolfCandidate.Hypertree.VerifyLeafCall

namespace SigGolfCandidate.Hypertree.KeygenVerifyCount
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 Keygen Signing Verifying
set_option maxRecDepth 4096

theorem upper_leaf_body_exact (hash : Hash) (s : MachineState) (level tree : Nat) (side : Bool) (base : Nat)
    (message : Reference.Digest) (values : Reference.Chain → Reference.Digest)
    (pc : s.pc = 0x1490) (data : LeafData s level tree side base message values)
    (counter : s.getMem 0x80430 = 0) (sp : s.getReg .x2 = 0xffffe0)
    (aligned : base % 8 = 0) (bound : base+736 ≤ 0x80000) :
    ∃ final steps cycles calls, Trace hash verify s steps cycles (calls+1) (calls+12) final ∧
      steps ≤ 33781 ∧ cycles ≤ 36130 ∧ calls ≤ 322 ∧
      final.pc = s.getMem 0xffffe0 &&& ~~~1#64 ∧ final.getReg .x2 = 0xfffff0 ∧
      (∀ i : Fin 2, final.getMem (KeygenSavePublic.wordAddress side i.val) =
        (Reference.compressLeaf hash level tree side (recoveredEndpoint hash level tree side message values)).extractLsb' (64*i.val) 64) ∧
      (∀ a, OutsideUpperLeaf side a → final.getMem a = s.getMem a) ∧ calls = chainCalls message := by
  obtain ⟨ready, steps, cycles, calls, loop, hsteps, hcycles, hcalls, readyPC, _,
    readyData, endpoints, _, readySP, loopFrame, exactCalls⟩ := recover_all_chains_exact hash s level tree side base message values
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
  refine ⟨final, steps+615, cycles+710, calls, loop.trans suffix, by omega, by omega, hcalls, ?_, ?_, output, ?_, exactCalls⟩
  · rw [finalPC, stack, loopFrame _ (by unfold OutsideLeafWork; decide)]
  · rw [finalSP, stack]; rfl
  · intro a outside
    exact (suffixFrame a outside.1.1 outside.1.2.1 outside.2).trans (loopFrame a outside.1)

theorem upper_leaf_call_exact (hash : Hash) (s : MachineState) (level tree : Nat) (side : Bool) (base : Nat)
    (message : Reference.Digest) (signature : Reference.LayerSignature)
    (pc : s.pc = 0x1458) (sp : s.getReg .x2 = 0xfffff0)
    (data : LeafData s level tree side base message signature.values)
    (nonzero : BitVec.ofNat 64 level ≠ 0) (aligned : base % 8 = 0) (bound : base+736 ≤ 0x80000) :
    ∃ final steps cycles calls, Trace hash verify s steps cycles (calls+1) (calls+12) final ∧
      steps ≤ 33795 ∧ cycles ≤ 36144 ∧ calls ≤ 322 ∧
      final.pc = s.getReg .x1 &&& ~~~1#64 ∧ final.getReg .x2 = s.getReg .x2 ∧
      (∀ i : Fin 2, final.getMem (KeygenSavePublic.wordAddress side i.val) =
        (Reference.recoverLeaf hash level tree side message signature).extractLsb' (64*i.val) 64) ∧
      (∀ a, a ≠ 0xffffe0 → OutsideUpperLeaf side a → final.getMem a = s.getMem a) ∧ calls = chainCalls message := by
  obtain ⟨ready, pre, rpc, rdata, counter, rsp, saved, entryFrame⟩ :=
    prepare_upper_leaf hash s level tree side base message signature pc sp data nonzero aligned bound
  obtain ⟨final, steps, cycles, calls, body, hsteps, hcycles, hcalls, finalPC, finalSP, output, frame, exactCalls⟩ :=
    upper_leaf_body_exact hash ready level tree side base message signature.values rpc rdata counter rsp aligned bound
  refine ⟨final, 14+steps, 14+cycles, calls, ?_, by omega, by omega, hcalls, ?_, ?_, ?_, ?_, exactCalls⟩
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

/-- info: 'SigGolfCandidate.Hypertree.KeygenVerifyCount.upper_leaf_call_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms upper_leaf_call_exact

end SigGolfCandidate.Hypertree.KeygenVerifyCount
