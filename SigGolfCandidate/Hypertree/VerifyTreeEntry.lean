import SigGolfCandidate.Hypertree.VerifyNode

namespace SigGolfCandidate.Hypertree.VerifyTreeEntry
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 Keygen Verifying
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false

def selected (s : MachineState) : MachineState :=
  let s := execInstrBr s (.LUI .x28 128)
  let s := execInstrBr s (.ADDI .x28 .x28 0x420)
  let s := execInstrBr s (.LD .x6 .x28 0)
  let s := execInstrBr s (.LUI .x28 128)
  let s := execInstrBr s (.ADDI .x28 .x28 0x428)
  let s := execInstrBr s (.SD .x28 .x6 0)
  execInstrBr s (.JAL .x1 328)

theorem selected_block (s : MachineState) (pc : s.pc = 0x12f8) :
    OrdinarySteps verify s 7 (selected s) := by
  let s1 := execInstrBr s (.LUI .x28 128)
  let s2 := execInstrBr s1 (.ADDI .x28 .x28 0x420)
  let s3 := execInstrBr s2 (.LD .x6 .x28 0)
  let s4 := execInstrBr s3 (.LUI .x28 128)
  let s5 := execInstrBr s4 (.ADDI .x28 .x28 0x428)
  let s6 := execInstrBr s5 (.SD .x28 .x6 0)
  let s7 := execInstrBr s6 (.JAL .x1 328)
  apply OrdinarySteps.step s s1 _ (.base (.LUI .x28 128)) 6
  · have hp : s.pc = 0x12f8 := by simp [execInstrBr, pc, BitVec.add_assoc]
    rw [fetch_at, hp]
    decide
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.ADDI .x28 .x28 0x420)) 5
  · have hp : s1.pc = 0x12fc := by simp [s1, execInstrBr, pc, BitVec.add_assoc]
    rw [fetch_at, hp]
    decide
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.LD .x6 .x28 0)) 4
  · have hp : s2.pc = 0x1300 := by simp [s1, s2, execInstrBr, pc, BitVec.add_assoc]
    rw [fetch_at, hp]
    decide
  · simp [s1, s2, s3, ordinaryStep, memoryArgumentsValid, execInstrBr, signExtend12, accessValid, rangeValid, MEMORY_BYTES, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s3 s4 _ (.base (.LUI .x28 128)) 3
  · have hp : s3.pc = 0x1304 := by simp [s1, s2, s3, execInstrBr, pc, BitVec.add_assoc]
    rw [fetch_at, hp]
    decide
  · rfl
  apply OrdinarySteps.step s4 s5 _ (.base (.ADDI .x28 .x28 0x428)) 2
  · have hp : s4.pc = 0x1308 := by simp [s1, s2, s3, s4, execInstrBr, pc, BitVec.add_assoc]
    rw [fetch_at, hp]
    decide
  · rfl
  apply OrdinarySteps.step s5 s6 _ (.base (.SD .x28 .x6 0)) 1
  · have hp : s5.pc = 0x130c := by simp [s1, s2, s3, s4, s5, execInstrBr, pc, BitVec.add_assoc]
    rw [fetch_at, hp]
    decide
  · simp [s1, s2, s3, s4, s5, s6, ordinaryStep, memoryArgumentsValid, execInstrBr, signExtend12, accessValid, rangeValid, MEMORY_BYTES, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s6 s7 _ (.base (.JAL .x1 328)) 0
  · have hp : s6.pc = 0x1310 := by simp [s1, s2, s3, s4, s5, s6, execInstrBr, pc, BitVec.add_assoc]
    rw [fetch_at, hp]
    decide
  · rfl
  exact OrdinarySteps.refl _

theorem selected_pc (s : MachineState) : (selected s).pc = s.pc+352 := by
  simp [selected, execInstrBr, signExtend21, BitVec.add_assoc]

theorem selected_ra (s : MachineState) : (selected s).getReg .x1 = s.pc+28 := by
  simp [selected, execInstrBr, MachineState.getReg_setReg_eq, BitVec.add_assoc]

theorem selected_sp (s : MachineState) : (selected s).getReg .x2 = s.getReg .x2 := by
  simp [selected, execInstrBr, MachineState.getReg_setReg_ne]

theorem selected_mem (s : MachineState) (a : Word) :
    (selected s).getMem a = if a = 0x80428 then s.getMem 0x80420 else s.getMem a := by
  simp [selected, execInstrBr, signExtend12, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]

def ready (s : MachineState) : MachineState := selected (enterState s)

theorem block (s : MachineState) (pc : s.pc = 0x12f0) (sp : s.getReg .x2 = 0x1000000) :
    OrdinarySteps verify s 9 (ready s) := by
  have entered := enter_block verify 0x12f0 tree_enter_code s pc (by rw [sp]; decide)
  have epc : (enterState s).pc = 0x12f8 := by rw [enter_pc, pc]; rfl
  exact ordinary_trans verify _ _ _ 2 7 entered (selected_block _ epc)

theorem pc (s : MachineState) (pc : s.pc = 0x12f0) : (ready s).pc = 0x1458 := by
  rw [ready, selected_pc, enter_pc, pc]; rfl

theorem stack (s : MachineState) (sp : s.getReg .x2 = 0x1000000) :
    (ready s).getReg .x2 = 0xfffff0 := by
  rw [ready, selected_sp, enter_sp, sp]; rfl

theorem ra (s : MachineState) (pc : s.pc = 0x12f0) : (ready s).getReg .x1 = 0x1314 := by
  rw [ready, selected_ra, enter_pc, pc]; rfl

theorem frame (s : MachineState) (sp : s.getReg .x2 = 0x1000000)
    (a : Word) (hs : a ≠ 0xfffff0) (hl : a ≠ 0x80428) : (ready s).getMem a = s.getMem a := by
  rw [ready, selected_mem, if_neg hl, enter_mem, sp]
  exact if_neg hs

theorem saved (s : MachineState) (sp : s.getReg .x2 = 0x1000000) :
    (ready s).getMem 0xfffff0 = s.getReg .x1 := by
  rw [ready, selected_mem, if_neg (by decide), enter_mem, sp, if_pos (by decide)]

theorem leaf (s : MachineState) (sp : s.getReg .x2 = 0x1000000) :
    (ready s).getMem 0x80428 = s.getMem 0x80420 := by
  rw [ready, selected_mem, if_pos rfl, enter_mem, sp, if_neg (by decide)]

/-- info: 'SigGolfCandidate.Hypertree.VerifyTreeEntry.block' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms block

end SigGolfCandidate.Hypertree.VerifyTreeEntry
