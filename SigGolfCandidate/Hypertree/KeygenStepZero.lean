import SigGolfCandidate.Hypertree.KeygenBlocks

namespace SigGolfCandidate.Hypertree.KeygenStepZero
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 OracleComp Keygen

def Code (image : Image) (p : Word) : Prop :=
  instructionAt image p = some (.base (.ADDI .x6 .x0 0)) ∧
  instructionAt image (p+4) = some (.base (.LUI .x28 128)) ∧
  instructionAt image (p+8) = some (.base (.ADDI .x28 .x28 0x438)) ∧
  instructionAt image (p+12) = some (.base (.SD .x28 .x6 0))

instance (image : Image) (p : Word) : Decidable (Code image p) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

def state (s : MachineState) : MachineState :=
  let s := execInstrBr s (.ADDI .x6 .x0 0)
  let s := execInstrBr s (.LUI .x28 128)
  let s := execInstrBr s (.ADDI .x28 .x28 0x438)
  execInstrBr s (.SD .x28 .x6 0)

theorem block (image : Image) (p : Word) (code : Code image p)
    (s : MachineState) (pc : s.pc=p) : OrdinarySteps image s 4 (state s) := by
  let s1 := execInstrBr s (.ADDI .x6 .x0 0)
  let s2 := execInstrBr s1 (.LUI .x28 128)
  let s3 := execInstrBr s2 (.ADDI .x28 .x28 0x438)
  apply OrdinarySteps.step s s1 _ (.base (.ADDI .x6 .x0 0)) 3
  · simpa only [fetch_at,pc] using code.1
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.LUI .x28 128)) 2
  · simpa only [fetch_at,s1,execInstrBr,MachineState.setPC,pc] using code.2.1
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.ADDI .x28 .x28 0x438)) 1
  · have hp : s2.pc=p+8 := by simp [s1,s2,execInstrBr,pc,BitVec.add_assoc]
    simpa only [fetch_at,hp] using code.2.2.1
  · rfl
  apply OrdinarySteps.step s3 (state s) _ (.base (.SD .x28 .x6 0)) 0
  · have hp : s3.pc=p+12 := by simp [s1,s2,s3,execInstrBr,pc,BitVec.add_assoc]
    simpa only [fetch_at,hp] using code.2.2.2
  · simp [s1,s2,s3,state,ordinaryStep,memoryArgumentsValid,execInstrBr,signExtend12,
      accessValid,rangeValid,MEMORY_BYTES,MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  exact OrdinarySteps.refl _

theorem pc (s : MachineState) : (state s).pc=s.pc+16 := by simp [state,execInstrBr,BitVec.add_assoc]

theorem mem (s : MachineState) (a : Word) :
    (state s).getMem a = if a=0x80438 then 0 else s.getMem a := by
  simp [state,execInstrBr,signExtend12,MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]

theorem stack (s : MachineState) :
    (state s).getReg .x1=s.getReg .x1 ∧ (state s).getReg .x2=s.getReg .x2 := by
  simp [state,execInstrBr,MachineState.getReg_setReg_ne]

theorem keygen_code : Code keygen 0x1308 := by decide

theorem sign_code : Code sign 0x1688 := by decide

end SigGolfCandidate.Hypertree.KeygenStepZero
