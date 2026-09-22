import SigGolfCandidate.Hypertree.VerifyLayerDispatch

namespace SigGolfCandidate.Hypertree.Verifying
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 Keygen Signing
set_option maxRecDepth 4096

/-- Encoding and complete tree recovery preserve the loop's witness and metadata. -/
theorem verify_layer_tree (hash : Hash) (s : MachineState) (level index : Nat) (side : Bool)
    (current : Reference.Digest) (witness : Bytes signatureBytes)
    (pc : s.pc = 0x11bc) (small : level < 160)
    (data : LoopData s level index current witness)
    (selector : s.getMem 0x80420 = BitVec.ofNat 64 (Reference.sideNumber side)) :
    ∃ final steps cycles calls blocks, Trace hash verify s steps cycles calls blocks final ∧
      steps ≤ 34368 ∧ cycles ≤ 36724 ∧ calls ≤ 324 ∧ blocks ≤ 335 ∧
      final.pc = 0x11d4 ∧
      LoopData final level index (Reference.recoverLayer hash level index side current (wireLayer witness level)) witness ∧
      LowFrame s final := by
  obtain ⟨ready, preSteps, pre, preBound, rpc, rra, rsp, readyData, preFrame⟩ :=
    prepare_tree s level index side current witness pc small data selector
  have bound := layer_pointer_bound 0x3d3b0 level (by decide) small
  obtain ⟨final, steps, cycles, calls, blocks, run, hsteps, hcycles, hcalls, hblocks, fpc, fsp, output, frame⟩ :=
    recover_tree_call hash ready level index (0x3d3b0+layerOffset level) side current (wireLayer witness level)
      rpc rsp readyData small (layer_pointer_aligned _ _ (by decide)) bound
  have finalData := readyData.transfer ready final level index (0x3d3b0+layerOffset level) side current
    (wireLayer witness level) bound frame
  have treeFrame : LowFrame ready final := by
    intro address _ low
    exact frame _ (outside_tree_low _ (by change address % 2^64 < 0x80000; omega))
  have totalFrame := preFrame.trans s ready final treeFrame
  refine ⟨final, preSteps+steps, preSteps+cycles, calls, blocks, ?_, by omega, by omega, hcalls, hblocks, ?_, ?_, totalFrame⟩
  · simpa only [Nat.zero_add] using pre.trace.trans run
  · rw [fpc, rra]; rfl
  · exact ⟨fsp.trans rsp, finalData.levelEq, finalData.indexEq, finalData.pointerEq,
      output, data.witnessEq.transfer_words s final witness totalFrame⟩

end SigGolfCandidate.Hypertree.Verifying
