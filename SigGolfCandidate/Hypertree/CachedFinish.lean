import SigGolfCandidate.Hypertree.ReuseChainBaseChunks
import SigGolfCandidate.Hypertree.CachedFusedFinish
namespace SigGolfCandidate.Hypertree.CachedFinish
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 Keygen
set_option maxRecDepth 50000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
def finish (s : MachineState) : MachineState :=
  let s := execInstrBr s (.LD .x11 .x28 744)
  let s := execInstrBr s (.SD .x28 .x11 1272)
  let s := execInstrBr s (.LD .x11 .x28 752)
  let s := execInstrBr s (.SD .x28 .x11 1280)
  let s := execInstrBr s (.ADDI .x28 .x28 1056)
  let s := execInstrBr s (.LD .x6 .x28 0)
  let s := execInstrBr s (.ADDI .x6 .x6 1)
  let s := execInstrBr s (.SD .x28 .x6 0)
  execInstrBr s (.JAL .x0 (-152))

theorem finish_equiv (s : MachineState) (base : s.getReg .x28 = 0x80018) :
    finish s = CachedFusedFinish.state s := by
  cases s with
  | mk regs mem code pc committed publicValues privateInput inputBufBase =>
    simp [MachineState.getReg] at base
    simp [finish, CachedFusedFinish.state, execInstrBr, MachineState.getReg, MachineState.setReg,
      MachineState.getMem, MachineState.setMem, MachineState.setPC, signExtend12, signExtend21,
      base, BitVec.add_assoc]
    funext r
    cases r <;> simp_all

/-- info: 'SigGolfCandidate.Hypertree.CachedFinish.finish_equiv' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms finish_equiv


def Code (image : Image) (p : Word) : Prop :=
  instructionAt image (p + 0) = some (.base (.LD .x11 .x28 744)) ∧
  instructionAt image (p + 4) = some (.base (.SD .x28 .x11 1272)) ∧
  instructionAt image (p + 8) = some (.base (.LD .x11 .x28 752)) ∧
  instructionAt image (p + 12) = some (.base (.SD .x28 .x11 1280)) ∧
  instructionAt image (p + 16) = some (.base (.ADDI .x28 .x28 1056)) ∧
  instructionAt image (p + 20) = some (.base (.LD .x6 .x28 0)) ∧
  instructionAt image (p + 24) = some (.base (.ADDI .x6 .x6 1)) ∧
  instructionAt image (p + 28) = some (.base (.SD .x28 .x6 0)) ∧
  instructionAt image (p + 32) = some (.base (.JAL .x0 (-152)))

theorem block (image : Image) (p : Word) (code : Code image p)
    (s : MachineState) (pc : s.pc = p) (base : s.getReg .x28 = 0x80018) :
    OrdinarySteps image s 9 (ChainLoopControl.increment (Copy6.optimized s 0x300 0x510) (-192)) := by
  rw [← CachedFusedFinish.state_equiv, ← finish_equiv s base]
  obtain ⟨c0,c1,c2,c3,c4,c5,c6,c7,c8⟩ := code
  let s1 := execInstrBr s (.LD .x11 .x28 744)
  let s2 := execInstrBr s1 (.SD .x28 .x11 1272)
  let s3 := execInstrBr s2 (.LD .x11 .x28 752)
  let s4 := execInstrBr s3 (.SD .x28 .x11 1280)
  let s5 := execInstrBr s4 (.ADDI .x28 .x28 1056)
  let s6 := execInstrBr s5 (.LD .x6 .x28 0)
  let s7 := execInstrBr s6 (.ADDI .x6 .x6 1)
  let s8 := execInstrBr s7 (.SD .x28 .x6 0)
  let s9 := execInstrBr s8 (.JAL .x0 (-152))
  change OrdinarySteps image s 9 s9
  apply OrdinarySteps.step s s1 _ (.base (.LD .x11 .x28 744)) 8
  · have hp : s.pc = p + 0 := by simp [execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c0
  · have hb : s.getReg .x28 = 0x80018 := by
      simpa [execInstrBr, signExtend12, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne, base] using base
    simp [s1, ordinaryStep, memoryArgumentsValid, hb, signExtend12, accessValid, rangeValid, MEMORY_BYTES]
  apply OrdinarySteps.step s1 s2 _ (.base (.SD .x28 .x11 1272)) 7
  · have hp : s1.pc = p + 4 := by simp [s1, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c1
  · have hb : s1.getReg .x28 = 0x80018 := by
      simpa [s1, execInstrBr, signExtend12, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne, base] using base
    simp [s2, ordinaryStep, memoryArgumentsValid, hb, signExtend12, accessValid, rangeValid, MEMORY_BYTES]
  apply OrdinarySteps.step s2 s3 _ (.base (.LD .x11 .x28 752)) 6
  · have hp : s2.pc = p + 8 := by simp [s1, s2, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c2
  · have hb : s2.getReg .x28 = 0x80018 := by
      simpa [s1, s2, execInstrBr, signExtend12, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne, base] using base
    simp [s3, ordinaryStep, memoryArgumentsValid, hb, signExtend12, accessValid, rangeValid, MEMORY_BYTES]
  apply OrdinarySteps.step s3 s4 _ (.base (.SD .x28 .x11 1280)) 5
  · have hp : s3.pc = p + 12 := by simp [s1, s2, s3, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c3
  · have hb : s3.getReg .x28 = 0x80018 := by
      simpa [s1, s2, s3, execInstrBr, signExtend12, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne, base] using base
    simp [s4, ordinaryStep, memoryArgumentsValid, hb, signExtend12, accessValid, rangeValid, MEMORY_BYTES]
  apply OrdinarySteps.step s4 s5 _ (.base (.ADDI .x28 .x28 1056)) 4
  · have hp : s4.pc = p + 16 := by simp [s1, s2, s3, s4, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c4
  · rfl
  apply OrdinarySteps.step s5 s6 _ (.base (.LD .x6 .x28 0)) 3
  · have hp : s5.pc = p + 20 := by simp [s1, s2, s3, s4, s5, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c5
  · have hb : s5.getReg .x28 = 0x80438 := by
      simpa [s1, s2, s3, s4, s5, execInstrBr, signExtend12, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne, base] using base
    simp [s6, ordinaryStep, memoryArgumentsValid, hb, signExtend12, accessValid, rangeValid, MEMORY_BYTES]
  apply OrdinarySteps.step s6 s7 _ (.base (.ADDI .x6 .x6 1)) 2
  · have hp : s6.pc = p + 24 := by simp [s1, s2, s3, s4, s5, s6, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c6
  · rfl
  apply OrdinarySteps.step s7 s8 _ (.base (.SD .x28 .x6 0)) 1
  · have hp : s7.pc = p + 28 := by simp [s1, s2, s3, s4, s5, s6, s7, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c7
  · have hb : s7.getReg .x28 = 0x80438 := by
      simpa [s1, s2, s3, s4, s5, s6, s7, execInstrBr, signExtend12, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne, base] using base
    simp [s8, ordinaryStep, memoryArgumentsValid, hb, signExtend12, accessValid, rangeValid, MEMORY_BYTES]
  apply OrdinarySteps.step s8 s9 _ (.base (.JAL .x0 (-152))) 0
  · have hp : s8.pc = p + 32 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using c8
  · rfl
  exact OrdinarySteps.refl _
/-- info: 'SigGolfCandidate.Hypertree.CachedFinish.block' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms block
end SigGolfCandidate.Hypertree.CachedFinish
