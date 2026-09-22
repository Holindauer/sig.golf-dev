import SigGolfCandidate.Hypertree.KeygenVerifyCountTree
import SigGolfCandidate.Hypertree.VerifyLayerStep

namespace SigGolfCandidate.Hypertree.KeygenVerifyCount
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 Keygen Signing Verifying
set_option maxRecDepth 4096

theorem verify_layer_tree_exact (hash : Hash) (s : MachineState) (level index : Nat) (side : Bool)
    (current : Reference.Digest) (witness : Bytes signatureBytes)
    (pc : s.pc = 0x11bc) (small : level < 160)
    (data : LoopData s level index current witness)
    (selector : s.getMem 0x80420 = BitVec.ofNat 64 (Reference.sideNumber side)) :
    ∃ final steps cycles calls blocks, Trace hash verify s steps cycles calls blocks final ∧
      steps ≤ 34368 ∧ cycles ≤ 36724 ∧ calls ≤ 324 ∧ blocks ≤ 335 ∧
      final.pc = 0x11d4 ∧
      LoopData final level index (Reference.recoverLayer hash level index side current (wireLayer witness level)) witness ∧
      LowFrame s final ∧ calls = SecurityVerifyCost.leafCalls level current+1 := by
  obtain ⟨ready, preSteps, pre, preBound, rpc, rra, rsp, readyData, preFrame⟩ :=
    prepare_tree s level index side current witness pc small data selector
  have bound := layer_pointer_bound 0x3d3b0 level (by decide) small
  obtain ⟨final, steps, cycles, calls, blocks, run, hsteps, hcycles, hcalls, hblocks, fpc, fsp, output, frame, countEq⟩ :=
    recover_tree_call_exact hash ready level index (0x3d3b0+layerOffset level) side current (wireLayer witness level)
      rpc rsp readyData small (layer_pointer_aligned _ _ (by decide)) bound
  have finalData := readyData.transfer ready final level index (0x3d3b0+layerOffset level) side current
    (wireLayer witness level) bound frame
  have treeFrame : LowFrame ready final := by
    intro address _ low
    exact frame _ (outside_tree_low _ (by change address % 2^64 < 0x80000; omega))
  have totalFrame := preFrame.trans s ready final treeFrame
  refine ⟨final, preSteps+steps, preSteps+cycles, calls, blocks, ?_, by omega, by omega, hcalls, hblocks, ?_, ?_, totalFrame, countEq⟩
  · simpa only [Nat.zero_add] using pre.trace.trans run
  · rw [fpc, rra]; rfl
  · exact ⟨fsp.trans rsp, finalData.levelEq, finalData.indexEq, finalData.pointerEq,
      output, data.witnessEq.transfer_words s final witness totalFrame⟩

theorem verify_layer_exact (hash : Hash) (s : MachineState) (level index : Nat)
    (current : Reference.Digest) (witness : Bytes signatureBytes)
    (pc : s.pc = 0x1148) (small : level < 160) (indexSmall : index < 2^192)
    (data : LoopData s level index current witness) :
    ∃ final steps cycles calls blocks, Trace hash verify s steps cycles calls blocks final ∧
      steps ≤ 34415 ∧ cycles ≤ 36771 ∧ calls ≤ 324 ∧ blocks ≤ 335 ∧
      final.pc = (if level+1 = 160 then 0x1220 else 0x1148) ∧
      LoopData final (level+1) (index/2)
        (Reference.recoverLayer hash level (index/2) (index%2 == 1) current (wireLayer witness level)) witness ∧
      LowFrame s final ∧ calls = SecurityVerifyCost.leafCalls level current+1 := by
  have pre := Verifying.shiftIndexState_block s pc
  have shiftedPC : (shiftIndexState s).pc = 0x11bc := by rw [shiftIndexState_pc, pc]; rfl
  have shiftedData := data.shift s level index current witness indexSmall
  have selected := (shift_index_nat s index indexSmall data.indexEq).2
  obtain ⟨recovered, steps, cycles, calls, blocks, run, hsteps, hcycles, hcalls, hblocks, recoveredPC, recoveredData, frame, countEq⟩ :=
    verify_layer_tree_exact hash (shiftIndexState s) level (index/2) (index%2 == 1) current witness shiftedPC small shiftedData selected
  have post := advance_block verify 0x11d4 verify_advance_code recovered recoveredPC
  have finalData := recoveredData.advance recovered level (index/2) _ witness small
  have finalPC := advanceState_layer_pc recovered 0x11d4 level recoveredPC small recoveredData.levelEq
  let n := if recovered.getMem 0x80400 = 0 then 17 else 18
  have hn : n ≤ 18 := by dsimp [n]; split <;> decide
  refine ⟨advanceState recovered, 29+steps+n, 29+cycles+n, calls, blocks, ?_, by omega, by omega, hcalls, hblocks,
    ?_, finalData, ?_, countEq⟩
  · simpa only [Nat.zero_add, Nat.add_zero] using (pre.trace.trans run).trans post.trace
  · simpa using finalPC
  · exact ((shift_low_frame s).trans s _ recovered frame).trans s recovered _ (advance_low_frame recovered)

end SigGolfCandidate.Hypertree.KeygenVerifyCount
