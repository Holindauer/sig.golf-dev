import SigGolfCandidate.Hypertree.FusedFinish

namespace SigGolfCandidate.Hypertree.CheckReuse
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 Keygen ChainLoopControl
set_option maxRecDepth 8192

def shortCheck (s : MachineState) : MachineState :=
  let s := execInstrBr s (.LD .x6 .x28 0)
  let s := execInstrBr s (.ADDI .x7 .x0 7)
  execInstrBr s (.BEQ .x6 .x7 320)

theorem shortCheck_equiv (s : MachineState) (base : s.getReg .x28 = 0x80438) :
    shortCheck (s.setPC (s.pc + 8)) = check s := by
  cases s with
  | mk regs mem code pc committed publicValues privateInput inputBufBase =>
    simp [MachineState.getReg] at base
    simp [shortCheck, check, execInstrBr, MachineState.getReg, MachineState.setReg,
      MachineState.getMem, MachineState.setPC, signExtend12, signExtend13, base, BitVec.add_assoc]
    split_ifs <;> congr 1 <;> funext r <;> cases r <;> simp_all

def Code (image : Image) (p : Word) : Prop :=
  instructionAt image (p + 0) = some (.base (.LD .x6 .x28 0)) ∧
  instructionAt image (p + 4) = some (.base (.ADDI .x7 .x0 7)) ∧
  instructionAt image (p + 8) = some (.base (.BEQ .x6 .x7 320))

theorem block (image : Image) (p : Word) (code : Code image p)
    (s : MachineState) (pc : s.pc = p) (base : s.getReg .x28 = 0x80438) :
    OrdinarySteps image s 3 (shortCheck s) := by
  let s1 := execInstrBr s (.LD .x6 .x28 0)
  let s2 := execInstrBr s1 (.ADDI .x7 .x0 7)
  let s3 := execInstrBr s2 (.BEQ .x6 .x7 320)
  apply OrdinarySteps.step s s1 _ (.base (.LD .x6 .x28 0)) 2
  · simpa [fetch_at, pc] using code.1
  · simp [s1, ordinaryStep, memoryArgumentsValid, base, signExtend12, accessValid, rangeValid, MEMORY_BYTES]
  apply OrdinarySteps.step s1 s2 _ (.base (.ADDI .x7 .x0 7)) 1
  · have hp : s1.pc = p + 4 := by simp [s1, execInstrBr, pc]
    simpa only [fetch_at, hp] using code.2.1
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.BEQ .x6 .x7 320)) 0
  · have hp : s2.pc = p + 8 := by simp [s1, s2, execInstrBr, pc, BitVec.add_assoc]
    simpa only [fetch_at, hp] using code.2.2
  · rfl
  exact OrdinarySteps.refl _

theorem short_mem (s : MachineState) (a : Word) : (shortCheck s).getMem a = s.getMem a := by
  simp [shortCheck, execInstrBr, MachineState.setReg, MachineState.setPC, MachineState.getMem]
  split_ifs <;> rfl

theorem short_pc (s : MachineState) (base : s.getReg .x28 = 0x80438) :
    (shortCheck s).pc = if s.getMem 0x80438 = 7 then s.pc + 328 else s.pc + 12 := by
  change s.regs .x28 = _ at base
  simp [shortCheck, execInstrBr, MachineState.getReg, MachineState.setReg, MachineState.setPC,
    signExtend12, signExtend13, base, BitVec.add_assoc]

theorem short_base (s : MachineState) : (shortCheck s).getReg .x28 = s.getReg .x28 := by
  simp [shortCheck, execInstrBr, MachineState.getReg, MachineState.setReg, MachineState.setPC]
  split_ifs <;> simp

theorem short_stack (s : MachineState) :
    (shortCheck s).getReg .x1 = s.getReg .x1 ∧ (shortCheck s).getReg .x2 = s.getReg .x2 := by
  simp [shortCheck, execInstrBr, MachineState.getReg, MachineState.setReg, MachineState.setPC]
  split_ifs <;> simp

theorem finish_step_address (s : MachineState) :
    (FusedFinish.state s).getReg .x28 = 0x80438 := by
  simp [FusedFinish.state, execInstrBr, MachineState.getReg, MachineState.setReg,
    MachineState.setMem, MachineState.setPC, signExtend12, signExtend21]

/-- info: 'SigGolfCandidate.Hypertree.CheckReuse.shortCheck_equiv' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms shortCheck_equiv

def setup (s : MachineState) : MachineState :=
  execInstrBr (execInstrBr s (.LUI .x28 128)) (.ADDI .x28 .x28 1080)

theorem setup_block (image : Image) (p : Word) (code : CheckCode image p)
    (s : MachineState) (pc : s.pc = p) : OrdinarySteps image s 2 (setup s) := by
  let s1 := execInstrBr s (.LUI .x28 128)
  apply OrdinarySteps.step s s1 _ (.base (.LUI .x28 128)) 1
  · simpa [fetch_at, pc] using code.1
  · rfl
  apply OrdinarySteps.step s1 (setup s) _ (.base (.ADDI .x28 .x28 1080)) 0
  · have hp : s1.pc = p + 4 := by simp [s1, execInstrBr, pc]
    simpa only [fetch_at, hp] using code.2.1
  · rfl
  exact OrdinarySteps.refl _

theorem setup_pc (s : MachineState) : (setup s).pc = s.pc + 8 := by
  simp [setup, execInstrBr, BitVec.add_assoc]
theorem setup_base (s : MachineState) : (setup s).getReg .x28 = 0x80438 := by
  simp [setup, execInstrBr, MachineState.getReg, MachineState.setReg, MachineState.setPC, signExtend12]
theorem setup_mem (s : MachineState) (a : Word) : (setup s).getMem a = s.getMem a := by rfl
theorem setup_stack (s : MachineState) :
    (setup s).getReg .x1 = s.getReg .x1 ∧ (setup s).getReg .x2 = s.getReg .x2 := by
  simp [setup, execInstrBr, MachineState.getReg, MachineState.setReg, MachineState.setPC]
theorem increment_base (s : MachineState) (jump : BitVec 21) :
    (increment s jump).getReg .x28 = 0x80438 := by
  simp [increment, execInstrBr, MachineState.getReg, MachineState.setReg, MachineState.setPC,
    MachineState.setMem, signExtend12]

/-- info: 'SigGolfCandidate.Hypertree.CheckReuse.block' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms block

end SigGolfCandidate.Hypertree.CheckReuse
