import SigGolfCandidate.Hypertree.SignPreludeFetch
import SigGolfCandidate.Hypertree.KeygenTreeControl
namespace SigGolfCandidate.Hypertree.KeygenTreeControl
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 Keygen
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
/-- Actual left-leaf control block with regional evidence for every fetch. -/
theorem left_region (hash : Hash) (s : MachineState) (pc : s.pc = 0x13d0) :
    RegionTrace (fun st => 0x1004 ≤ st.pc.toNat ∧ st.pc.toNat < 0x1c70)
      hash sign s 5 5 0 0 (state s 0 364) := by
  let p : Word := 0x13d0
  let side : BitVec 12 := 0
  let jump : BitVec 21 := 364
  have code : Code sign p side jump := by decide
  let s1 := execInstrBr s (.ADDI .x6 .x0 side)
  let s2 := execInstrBr s1 (.LUI .x28 128)
  let s3 := execInstrBr s2 (.ADDI .x28 .x28 0x428)
  let s4 := execInstrBr s3 (.SD .x28 .x6 0)
  apply RegionTrace.step s s1 _ (.base (.ADDI .x6 .x0 side)) 4
  · change 0x1004 ≤ s.pc.toNat ∧ s.pc.toNat < 0x1c70
    simp [execInstrBr, pc, p, side, jump, BitVec.add_assoc]
  · simpa only [fetch_at,pc] using code.1
  · rfl
  apply RegionTrace.step s1 s2 _ (.base (.LUI .x28 128)) 3
  · change 0x1004 ≤ s1.pc.toNat ∧ s1.pc.toNat < 0x1c70
    simp [s1, execInstrBr, pc, p, side, jump, BitVec.add_assoc]
  · simpa only [fetch_at,s1,execInstrBr,MachineState.setPC,pc] using code.2.1
  · rfl
  apply RegionTrace.step s2 s3 _ (.base (.ADDI .x28 .x28 0x428)) 2
  · change 0x1004 ≤ s2.pc.toNat ∧ s2.pc.toNat < 0x1c70
    simp [s1, s2, execInstrBr, pc, p, side, jump, BitVec.add_assoc]
  · have hp : s2.pc=p+8 := by simp [s1,s2,execInstrBr,pc,p,BitVec.add_assoc]
    simpa only [fetch_at,hp] using code.2.2.1
  · rfl
  apply RegionTrace.step s3 s4 _ (.base (.SD .x28 .x6 0)) 1
  · change 0x1004 ≤ s3.pc.toNat ∧ s3.pc.toNat < 0x1c70
    simp [s1, s2, s3, execInstrBr, pc, p, side, jump, BitVec.add_assoc]
  · have hp : s3.pc=p+12 := by simp [s1,s2,s3,execInstrBr,pc,p,BitVec.add_assoc]
    simpa only [fetch_at,hp] using code.2.2.2.1
  · simp [s1,s2,s3,s4,ordinaryStep,memoryArgumentsValid,execInstrBr,signExtend12,
      accessValid,rangeValid,MEMORY_BYTES,MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  apply RegionTrace.step s4 (state s side jump) _ (.base (.JAL .x1 jump)) 0
  · change 0x1004 ≤ s4.pc.toNat ∧ s4.pc.toNat < 0x1c70
    simp [s1, s2, s3, s4, execInstrBr, pc, p, side, jump, BitVec.add_assoc]
  · have hp : s4.pc=p+16 := by simp [s1,s2,s3,s4,execInstrBr,pc,p,BitVec.add_assoc]
    simpa only [fetch_at,hp] using code.2.2.2.2
  · rfl
  exact RegionTrace.refl _
/-- info: 'SigGolfCandidate.Hypertree.KeygenTreeControl.left_region' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms left_region
end SigGolfCandidate.Hypertree.KeygenTreeControl
