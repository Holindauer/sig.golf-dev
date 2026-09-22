import SigGolfCandidate.Hypertree.VerifyLayerTree
import SigGolfCandidate.Hypertree.VerifyLayerAdvance

namespace SigGolfCandidate.Hypertree.Verifying
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 Keygen Signing
set_option maxRecDepth 4096

/-- One complete protected verifier iteration, including index shift, encoding, tree, and advancement. -/
theorem verify_layer (hash : Hash) (s : MachineState) (level index : Nat)
    (current : Reference.Digest) (witness : Bytes signatureBytes)
    (pc : s.pc = 0x1148) (small : level < 160) (indexSmall : index < 2^192)
    (data : LoopData s level index current witness) :
    ∃ final steps cycles calls blocks, Trace hash verify s steps cycles calls blocks final ∧
      steps ≤ 34415 ∧ cycles ≤ 36771 ∧ calls ≤ 324 ∧ blocks ≤ 335 ∧
      final.pc = (if level+1 = 160 then 0x1220 else 0x1148) ∧
      LoopData final (level+1) (index/2)
        (Reference.recoverLayer hash level (index/2) (index%2 == 1) current (wireLayer witness level)) witness ∧
      LowFrame s final := by
  have pre := Verifying.shiftIndexState_block s pc
  have shiftedPC : (shiftIndexState s).pc = 0x11bc := by rw [shiftIndexState_pc, pc]; rfl
  have shiftedData := data.shift s level index current witness indexSmall
  have selected := (shift_index_nat s index indexSmall data.indexEq).2
  obtain ⟨recovered, steps, cycles, calls, blocks, run, hsteps, hcycles, hcalls, hblocks, recoveredPC, recoveredData, frame⟩ :=
    verify_layer_tree hash (shiftIndexState s) level (index/2) (index%2 == 1) current witness shiftedPC small shiftedData selected
  have post := advance_block verify 0x11d4 verify_advance_code recovered recoveredPC
  have finalData := recoveredData.advance recovered level (index/2) _ witness small
  have finalPC := advanceState_layer_pc recovered 0x11d4 level recoveredPC small recoveredData.levelEq
  let n := if recovered.getMem 0x80400 = 0 then 17 else 18
  have hn : n ≤ 18 := by dsimp [n]; split <;> decide
  refine ⟨advanceState recovered, 29+steps+n, 29+cycles+n, calls, blocks, ?_, by omega, by omega, hcalls, hblocks,
    ?_, finalData, ?_⟩
  · simpa only [Nat.zero_add, Nat.add_zero] using (pre.trace.trans run).trans post.trace
  · simpa using finalPC
  · exact ((shift_low_frame s).trans s _ recovered frame).trans s recovered _ (advance_low_frame recovered)

/-- info: 'SigGolfCandidate.Hypertree.Verifying.verify_layer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms verify_layer

end SigGolfCandidate.Hypertree.Verifying
