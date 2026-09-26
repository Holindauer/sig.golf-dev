import SigGolfCandidate.Hypertree.RegisterHeader
import SigGolfCandidate.Hypertree.StepBaseBlocks
namespace SigGolfCandidate.Hypertree.RegisterHeader
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 Keygen
set_option maxRecDepth 8192

def PrepareCode (image : Image) (p : Word) : Prop :=
  instructionAt image p = some (.base (.ADD .x14 .x14 .x13)) ∧
  instructionAt image (p+4) = some (.base (.SD .x28 .x14 (-1080))) ∧
  instructionAt image (p+8) = some (.base (.ADDI .x10 .x28 (-1080))) ∧
  instructionAt image (p+12) = some (.base (.JAL .x0 92))

theorem prepare_block (image : Image) (p : Word) (code : PrepareCode image p)
    (s : MachineState) (pc : s.pc = p) (base : s.getReg .x28 = 0x80438) :
    OrdinarySteps image s 4 (prepare s) := by
  obtain ⟨c0,c1,c2,c3⟩ := code
  let s1 := execInstrBr s (.ADD .x14 .x14 .x13)
  let s2 := execInstrBr s1 (.SD .x28 .x14 (-1080))
  let s3 := execInstrBr s2 (.ADDI .x10 .x28 (-1080))
  let s4 := execInstrBr s3 (.JAL .x0 92)
  change OrdinarySteps image s 4 s4
  apply OrdinarySteps.step s s1 _ (.base (.ADD .x14 .x14 .x13)) 3
  · simpa only [fetch_at,pc] using c0
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.SD .x28 .x14 (-1080))) 2
  · have hp : s1.pc = p+4 := by simp [s1,execInstrBr,pc]
    simpa only [fetch_at,hp] using c1
  · have hb : s1.getReg .x28 = 0x80438 := by simp [s1,execInstrBr,MachineState.getReg_setReg_ne,base]
    simp [s2,ordinaryStep,memoryArgumentsValid,hb,signExtend12,accessValid,rangeValid,MEMORY_BYTES]
  apply OrdinarySteps.step s2 s3 _ (.base (.ADDI .x10 .x28 (-1080))) 1
  · have hp : s2.pc = p+8 := by simp [s1,s2,execInstrBr,pc,BitVec.add_assoc]
    simpa only [fetch_at,hp] using c2
  · rfl
  apply OrdinarySteps.step s3 s4 _ (.base (.JAL .x0 92)) 0
  · have hp : s3.pc = p+12 := by simp [s1,s2,s3,execInstrBr,pc,BitVec.add_assoc]
    simpa only [fetch_at,hp] using c3
  · rfl
  exact OrdinarySteps.refl _

/-- info: 'SigGolfCandidate.Hypertree.RegisterHeader.prepare_block' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms prepare_block
end SigGolfCandidate.Hypertree.RegisterHeader
