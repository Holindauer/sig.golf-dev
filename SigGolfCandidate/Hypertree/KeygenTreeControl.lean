import SigGolfCandidate.Hypertree.KeygenBlocks

namespace SigGolfCandidate.Hypertree.KeygenTreeControl
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 OracleComp Keygen

def Code (image : Image) (p : Word) (side : BitVec 12) (jump : BitVec 21) : Prop :=
  instructionAt image p=some (.base (.ADDI .x6 .x0 side)) ∧
  instructionAt image (p+4)=some (.base (.LUI .x28 128)) ∧
  instructionAt image (p+8)=some (.base (.ADDI .x28 .x28 0x428)) ∧
  instructionAt image (p+12)=some (.base (.SD .x28 .x6 0)) ∧
  instructionAt image (p+16)=some (.base (.JAL .x1 jump))

instance (image : Image) (p : Word) (side : BitVec 12) (jump : BitVec 21) :
    Decidable (Code image p side jump) := inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _))

def state (s : MachineState) (side : BitVec 12) (jump : BitVec 21) : MachineState :=
  let s := execInstrBr s (.ADDI .x6 .x0 side)
  let s := execInstrBr s (.LUI .x28 128)
  let s := execInstrBr s (.ADDI .x28 .x28 0x428)
  let s := execInstrBr s (.SD .x28 .x6 0)
  execInstrBr s (.JAL .x1 jump)

theorem block (image : Image) (p : Word) (side : BitVec 12) (jump : BitVec 21)
    (code : Code image p side jump) (s : MachineState) (pc : s.pc=p) :
    OrdinarySteps image s 5 (state s side jump) := by
  let s1 := execInstrBr s (.ADDI .x6 .x0 side)
  let s2 := execInstrBr s1 (.LUI .x28 128)
  let s3 := execInstrBr s2 (.ADDI .x28 .x28 0x428)
  let s4 := execInstrBr s3 (.SD .x28 .x6 0)
  apply OrdinarySteps.step s s1 _ (.base (.ADDI .x6 .x0 side)) 4
  · simpa only [fetch_at,pc] using code.1
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.LUI .x28 128)) 3
  · simpa only [fetch_at,s1,execInstrBr,MachineState.setPC,pc] using code.2.1
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.ADDI .x28 .x28 0x428)) 2
  · have hp : s2.pc=p+8 := by simp [s1,s2,execInstrBr,pc,BitVec.add_assoc]
    simpa only [fetch_at,hp] using code.2.2.1
  · rfl
  apply OrdinarySteps.step s3 s4 _ (.base (.SD .x28 .x6 0)) 1
  · have hp : s3.pc=p+12 := by simp [s1,s2,s3,execInstrBr,pc,BitVec.add_assoc]
    simpa only [fetch_at,hp] using code.2.2.2.1
  · simp [s1,s2,s3,s4,ordinaryStep,memoryArgumentsValid,execInstrBr,signExtend12,
      accessValid,rangeValid,MEMORY_BYTES,MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s4 (state s side jump) _ (.base (.JAL .x1 jump)) 0
  · have hp : s4.pc=p+16 := by simp [s1,s2,s3,s4,execInstrBr,pc,BitVec.add_assoc]
    simpa only [fetch_at,hp] using code.2.2.2.2
  · rfl
  exact OrdinarySteps.refl _

theorem pc (s : MachineState) (side : BitVec 12) (jump : BitVec 21) :
    (state s side jump).pc=s.pc+16+signExtend21 jump := by simp [state,execInstrBr,BitVec.add_assoc]

theorem ra (s : MachineState) (side : BitVec 12) (jump : BitVec 21) :
    (state s side jump).getReg .x1=s.pc+20 := by
  simp [state,execInstrBr,MachineState.getReg_setReg_eq,BitVec.add_assoc]

theorem sp (s : MachineState) (side : BitVec 12) (jump : BitVec 21) :
    (state s side jump).getReg .x2=s.getReg .x2 := by
  simp [state,execInstrBr,MachineState.getReg_setReg_ne]

theorem mem (s : MachineState) (side : BitVec 12) (jump : BitVec 21) (a : Word) :
    (state s side jump).getMem a=if a=0x80428 then signExtend12 side else s.getMem a := by
  simp [state,execInstrBr,signExtend12,MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]

theorem left_code : Code keygen 0x1050 0 364 := by decide

theorem right_code : Code keygen 0x1064 1 344 := by decide

end SigGolfCandidate.Hypertree.KeygenTreeControl
