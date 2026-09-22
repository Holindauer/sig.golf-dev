import SigGolfCandidate.Hypertree.KeygenBlocks

namespace SigGolfCandidate.Hypertree.Keygen
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 OracleComp

set_option maxRecDepth 4096

/-- The generated subroutine prologue allocates a 16-byte frame and saves `ra`. -/
def enterState (s : MachineState) : MachineState :=
  execInstrBr (execInstrBr s (.ADDI .x2 .x2 (-16))) (.SD .x2 .x1 0)

def EnterCode (image : Image) (p : Word) : Prop :=
  instructionAt image p = some (.base (.ADDI .x2 .x2 (-16))) ∧
  instructionAt image (p + 4) = some (.base (.SD .x2 .x1 0))

instance (image : Image) (p : Word) : Decidable (EnterCode image p) :=
  inferInstanceAs (Decidable (_ ∧ _))

theorem enter_block (image : Image) (p : Word) (code : EnterCode image p)
    (s : MachineState) (pc : s.pc = p)
    (stack : accessValid (s.getReg .x2 - 16) 8 = true) :
    OrdinarySteps image s 2 (enterState s) := by
  apply OrdinarySteps.step s (execInstrBr s (.ADDI .x2 .x2 (-16))) _
    (.base (.ADDI .x2 .x2 (-16))) 1
  · simpa only [fetch_at, pc] using code.1
  · rfl
  apply OrdinarySteps.step _ (enterState s) _ (.base (.SD .x2 .x1 0)) 0
  · simpa only [fetch_at, execInstrBr, MachineState.setPC, pc] using code.2
  · simpa [enterState, ordinaryStep, memoryArgumentsValid, execInstrBr,
      signExtend12, MachineState.getReg_setReg_eq, BitVec.sub_eq_add_neg] using stack
  exact OrdinarySteps.refl _

theorem enter_pc (s : MachineState) : (enterState s).pc = s.pc + 8 := by
  simp [enterState, execInstrBr, BitVec.add_assoc]

theorem enter_sp (s : MachineState) : (enterState s).getReg .x2 = s.getReg .x2 - 16 := by
  simp [enterState, execInstrBr, signExtend12, BitVec.sub_eq_add_neg, MachineState.getReg_setReg_eq]

theorem enter_mem (s : MachineState) (a : Word) :
    (enterState s).getMem a =
      if a = s.getReg .x2 - 16 then s.getReg .x1 else s.getMem a := by
  simp [enterState, execInstrBr, signExtend12, BitVec.sub_eq_add_neg,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]

/-- The generated epilogue restores `ra` and the stack pointer, then uses protected JALR. -/
def returnState (s : MachineState) : MachineState :=
  execInstrBr (execInstrBr (execInstrBr s (.LD .x1 .x2 0))
    (.ADDI .x2 .x2 16)) (.JALR .x0 .x1 0)

def ReturnCode (image : Image) (p : Word) : Prop :=
  instructionAt image p = some (.base (.LD .x1 .x2 0)) ∧
  instructionAt image (p + 4) = some (.base (.ADDI .x2 .x2 16)) ∧
  instructionAt image (p + 8) = some (.base (.JALR .x0 .x1 0))

instance (image : Image) (p : Word) : Decidable (ReturnCode image p) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

theorem return_block (image : Image) (p : Word) (code : ReturnCode image p)
    (s : MachineState) (pc : s.pc = p)
    (stack : accessValid (s.getReg .x2) 8 = true) :
    OrdinarySteps image s 3 (returnState s) := by
  let s1 := execInstrBr s (.LD .x1 .x2 0)
  let s2 := execInstrBr s1 (.ADDI .x2 .x2 16)
  apply OrdinarySteps.step s s1 _ (.base (.LD .x1 .x2 0)) 2
  · simpa only [fetch_at, pc] using code.1
  · simp [s1, ordinaryStep, memoryArgumentsValid, signExtend12, stack]
  apply OrdinarySteps.step s1 s2 _ (.base (.ADDI .x2 .x2 16)) 1
  · simpa only [fetch_at, s1, execInstrBr, MachineState.setPC, pc] using code.2.1
  · rfl
  apply OrdinarySteps.step s2 (returnState s) _ (.base (.JALR .x0 .x1 0)) 0
  · simpa [fetch_at, s1, s2, execInstrBr, MachineState.setPC, pc, BitVec.add_assoc] using code.2.2
  · rfl
  exact OrdinarySteps.refl _

theorem return_pc (s : MachineState) :
    (returnState s).pc = s.getMem (s.getReg .x2) &&& ~~~1#64 := by
  simp [returnState, execInstrBr, signExtend12, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]

theorem return_sp (s : MachineState) :
    (returnState s).getReg .x2 = s.getReg .x2 + 16 := by
  simp [returnState, execInstrBr, signExtend12, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]

theorem return_mem (s : MachineState) (a : Word) :
    (returnState s).getMem a = s.getMem a := by simp [returnState, execInstrBr]

theorem keygen_tree_enter : EnterCode keygen 0x1048 := by decide
 theorem keygen_leaf_enter : EnterCode keygen 0x11cc := by decide
 theorem keygen_tree_return : ReturnCode keygen 0x11c0 := by decide
 theorem keygen_leaf_return : ReturnCode keygen 0x1650 := by decide
 theorem keygen_bottom_return : ReturnCode keygen 0x18e4 := by decide

/-- The real keygen entry initializes LEVEL=159 and calls the tree subroutine. -/
def prefixState (s : MachineState) : MachineState :=
  let s := execInstrBr s (.ADDI .x6 .x0 159)
  let s := execInstrBr s (.LUI .x28 0x80)
  let s := execInstrBr s (.ADDI .x28 .x28 0x400)
  let s := execInstrBr s (.SD .x28 .x6 0)
  execInstrBr s (.JAL .x1 56)

theorem prefix_block (s : MachineState) (pc : s.pc = 0x1000) :
    OrdinarySteps keygen s 5 (prefixState s) := by
  let s1 := execInstrBr s (.ADDI .x6 .x0 159)
  let s2 := execInstrBr s1 (.LUI .x28 0x80)
  let s3 := execInstrBr s2 (.ADDI .x28 .x28 0x400)
  let s4 := execInstrBr s3 (.SD .x28 .x6 0)
  apply OrdinarySteps.step s s1 _ (.base (.ADDI .x6 .x0 159)) 4
  · simp only [fetch, pc, keygen]; decide
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.LUI .x28 0x80)) 3
  · simp only [fetch, s1, execInstrBr, MachineState.setPC, pc, keygen]; decide
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.ADDI .x28 .x28 0x400)) 2
  · simp only [fetch, s1, s2, execInstrBr, MachineState.setPC, pc, keygen]; decide
  · rfl
  apply OrdinarySteps.step s3 s4 _ (.base (.SD .x28 .x6 0)) 1
  · simp only [fetch, s1, s2, s3, execInstrBr, MachineState.setPC, pc, keygen]; decide
  · simp [s1, s2, s3, s4, ordinaryStep, memoryArgumentsValid, execInstrBr,
      MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne, signExtend12,
      accessValid, rangeValid, MEMORY_BYTES]
  apply OrdinarySteps.step s4 (prefixState s) _ (.base (.JAL .x1 56)) 0
  · simp only [fetch, s1, s2, s3, s4, execInstrBr, MachineState.setPC, pc, keygen]; decide
  · rfl
  exact OrdinarySteps.refl _

theorem prefix_pc (s : MachineState) (pc : s.pc = 0x1000) :
    (prefixState s).pc = 0x1048 := by simp [prefixState, execInstrBr, pc, signExtend21]

theorem prefix_ra (s : MachineState) (pc : s.pc = 0x1000) :
    (prefixState s).getReg .x1 = 0x1014 := by
  simp [prefixState, execInstrBr, pc, MachineState.getReg_setReg_eq]

theorem prefix_sp (s : MachineState) : (prefixState s).getReg .x2 = s.getReg .x2 := by
  simp [prefixState, execInstrBr, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]

theorem prefix_mem (s : MachineState) (a : Word) :
    (prefixState s).getMem a = if a = 0x80400 then 159 else s.getMem a := by
  simp [prefixState, execInstrBr, signExtend12, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]

end SigGolfCandidate.Hypertree.Keygen
