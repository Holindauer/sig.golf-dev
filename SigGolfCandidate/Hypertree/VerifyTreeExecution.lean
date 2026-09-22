import SigGolfCandidate.Hypertree.VerifyTreeFrame

namespace SigGolfCandidate.Hypertree.Verifying
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 Keygen Signing
set_option maxRecDepth 4096

/-- Complete actual tree verification for arbitrary witness contents and either layer format. -/
theorem recover_tree_call (hash : Hash) (s : MachineState) (level tree base : Nat) (side : Bool)
    (message : Reference.Digest) (signature : Reference.LayerSignature)
    (pc : s.pc = 0x12f0) (sp : s.getReg .x2 = 0x1000000)
    (data : LayerData s level tree base side message signature)
    (small : level < 160) (aligned : base % 8 = 0) (bound : base+752 ≤ 0x80000) :
    ∃ final steps cycles calls blocks, Trace hash verify s steps cycles calls blocks final ∧
      steps ≤ 33908 ∧ cycles ≤ 36264 ∧ calls ≤ 324 ∧ blocks ≤ 335 ∧
      final.pc = s.getReg .x1 &&& ~~~1#64 ∧ final.getReg .x2 = s.getReg .x2 ∧
      (∀ i : Fin 2, final.getMem (wordAddress 0x80500 i.val) =
        (Reference.recoverLayer hash level tree side message signature).extractLsb' (64*i.val) 64) ∧
      (∀ a, OutsideTreeWork a → final.getMem a = s.getMem a) := by
  have pre := VerifyTreeEntry.block s pc sp
  have entryData := tree_entry_context s level tree base side message signature sp data bound
  have entryLeaf : (VerifyTreeEntry.ready s).getMem 0x80428 = BitVec.ofNat 64 (Reference.sideNumber side) := by
    rw [VerifyTreeEntry.leaf s sp]
    exact data.selectorEq
  obtain ⟨recovered, leafSteps, leafCycles, leafCalls, leafBlocks, leafRun, hsteps, hcycles, hcalls, hblocks,
    leafPC, leafSP, output, leafFrame⟩ := recover_leaf_call hash (VerifyTreeEntry.ready s) level tree base side
      message signature (VerifyTreeEntry.pc s pc) (VerifyTreeEntry.stack s sp) entryData entryLeaf small aligned bound
  have recoveredPC : recovered.pc = 0x1314 := by rw [leafPC, VerifyTreeEntry.ra s pc]; rfl
  have recoveredSP : recovered.getReg .x2 = 0xfffff0 := leafSP.trans (VerifyTreeEntry.stack s sp)
  have recoveredData : LayerData recovered level tree base side message signature := by
    apply entryData.transfer _ _ level tree base side message signature bound
    intro a outside
    exact leafFrame a outside.2.2.2.2.1 ⟨outside.1, outside.2.1 side⟩
  obtain ⟨final, postSteps, postCycles, post, psteps, pcycles, finalPC, finalSP, current, postFrame⟩ :=
    finish_tree hash recovered level tree base side message signature recoveredPC recoveredSP small aligned bound
      recoveredData.levelEq recoveredData.indexEq recoveredData.pointerEq recoveredData.selectorEq output recoveredData.siblingEq
  refine ⟨final, 9+leafSteps+postSteps, 9+leafCycles+postCycles, leafCalls+1, leafBlocks+1,
    ?_, by omega, by omega, by omega, by omega, ?_, ?_, current, ?_⟩
  · simpa only [Nat.zero_add] using (pre.trace.trans leafRun).trans post
  · rw [finalPC, leafFrame _ (by decide) (by unfold OutsideUpperLeaf OutsideLeafWork; cases side <;> decide),
      VerifyTreeEntry.saved s sp]
  · rw [finalSP, sp]
  · intro a outside
    have parent : OutsideParentWork side a :=
      ⟨fun i => outside.1.1 ⟨i.val, by have := i.isLt; omega⟩, outside.1.2.1, outside.2.2.1, outside.2.1 (!side)⟩
    rw [postFrame a parent, leafFrame a outside.2.2.2.2.1 ⟨outside.1, outside.2.1 side⟩,
      VerifyTreeEntry.frame s sp a outside.2.2.2.1 outside.2.2.2.2.2]

/-- info: 'SigGolfCandidate.Hypertree.Verifying.recover_tree_call' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms recover_tree_call

end SigGolfCandidate.Hypertree.Verifying
