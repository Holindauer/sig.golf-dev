import SigGolfCandidate.Hypertree.KeygenCopySetup
import SigGolfCandidate.Hypertree.KeygenChainHeader

namespace SigGolfCandidate.Hypertree.FastCopy16
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 Keygen
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

/-- Original two-iteration copy, including its five-instruction setup. -/
def original (s : MachineState) (src dst : BitVec 12) : MachineState :=
  Expansion.loopNext (Expansion.loopNext (copySetup s src dst 2))

/-- Experimental ten-instruction copy; the final jump skips one padding word. -/
def optimized (s : MachineState) (src dst : BitVec 12) : MachineState :=
  let s := copySetup s (src+16) (dst+16) 0
  let s := execInstrBr s (.LD .x11 .x6 (-16))
  let s := execInstrBr s (.SD .x7 .x11 (-16))
  let s := execInstrBr s (.LD .x11 .x6 (-8))
  let s := execInstrBr s (.SD .x7 .x11 (-8))
  execInstrBr s (.JAL .x0 8)

/-- Full state equivalence for the chain-input copy, for arbitrary memory and registers. -/
theorem chain_input_equiv (s : MachineState) :
    optimized s 0x510 0x20 = original s 0x510 0x20 := by
  cases s
  simp [optimized, original, copySetup, Expansion.loopNext, Expansion.loopBody,
    execInstrBr, MachineState.getReg, MachineState.setReg, MachineState.getMem,
    MachineState.setMem, MachineState.setPC, signExtend12, signExtend13,
    signExtend21, BitVec.add_assoc]
  funext r
  cases r <;> rfl

theorem chain_output_equiv (s : MachineState) :
    optimized s 0x300 0x510 = original s 0x300 0x510 := by
  cases s
  simp [optimized, original, copySetup, Expansion.loopNext, Expansion.loopBody,
    execInstrBr, MachineState.getReg, MachineState.setReg, MachineState.getMem,
    MachineState.setMem, MachineState.setPC, signExtend12, signExtend13,
    signExtend21, BitVec.add_assoc]
  funext r
  cases r <;> rfl

/-- info: 'SigGolfCandidate.Hypertree.FastCopy16.chain_input_equiv' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms chain_input_equiv

/-- Actual ten executed instructions of the replacement at the chain-input site. -/
def InputCode (image : Image) (p : Word) : Prop :=
  instructionAt image (p + 0) = some (.base (.LUI .x6 128)) ∧
  instructionAt image (p + 4) = some (.base (.ADDI .x6 .x6 0x520)) ∧
  instructionAt image (p + 8) = some (.base (.LUI .x7 128)) ∧
  instructionAt image (p + 12) = some (.base (.ADDI .x7 .x7 0x30)) ∧
  instructionAt image (p + 16) = some (.base (.ADDI .x10 .x0 0)) ∧
  instructionAt image (p + 20) = some (.base (.LD .x11 .x6 (-16))) ∧
  instructionAt image (p + 24) = some (.base (.SD .x7 .x11 (-16))) ∧
  instructionAt image (p + 28) = some (.base (.LD .x11 .x6 (-8))) ∧
  instructionAt image (p + 32) = some (.base (.SD .x7 .x11 (-8))) ∧
  instructionAt image (p + 36) = some (.base (.JAL .x0 8))

theorem chain_input_executes (image : Image) (p : Word) (code : InputCode image p)
    (s : MachineState) (pc : s.pc = p) :
    OrdinarySteps image s 10 (optimized s 0x510 0x20) := by
  obtain ⟨c0,c1,c2,c3,c4,c5,c6,c7,c8,c9⟩ := code
  let s1 := execInstrBr s (.LUI .x6 128)
  let s2 := execInstrBr s1 (.ADDI .x6 .x6 0x520)
  let s3 := execInstrBr s2 (.LUI .x7 128)
  let s4 := execInstrBr s3 (.ADDI .x7 .x7 0x30)
  let s5 := execInstrBr s4 (.ADDI .x10 .x0 0)
  let s6 := execInstrBr s5 (.LD .x11 .x6 (-16))
  let s7 := execInstrBr s6 (.SD .x7 .x11 (-16))
  let s8 := execInstrBr s7 (.LD .x11 .x6 (-8))
  let s9 := execInstrBr s8 (.SD .x7 .x11 (-8))
  let s10 := execInstrBr s9 (.JAL .x0 8)
  change OrdinarySteps image s 10 s10
  apply OrdinarySteps.step s s1 _ (.base (.LUI .x6 128)) 9
  · simpa [fetch_at, execInstrBr, MachineState.setPC, pc, BitVec.add_assoc] using c0
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.ADDI .x6 .x6 0x520)) 8
  · simpa [fetch_at, s1, execInstrBr, MachineState.setPC, pc, BitVec.add_assoc] using c1
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.LUI .x7 128)) 7
  · simpa [fetch_at, s1, s2, execInstrBr, MachineState.setPC, pc, BitVec.add_assoc] using c2
  · rfl
  apply OrdinarySteps.step s3 s4 _ (.base (.ADDI .x7 .x7 0x30)) 6
  · simpa [fetch_at, s1, s2, s3, execInstrBr, MachineState.setPC, pc, BitVec.add_assoc] using c3
  · rfl
  apply OrdinarySteps.step s4 s5 _ (.base (.ADDI .x10 .x0 0)) 5
  · simpa [fetch_at, s1, s2, s3, s4, execInstrBr, MachineState.setPC, pc, BitVec.add_assoc] using c4
  · rfl
  apply OrdinarySteps.step s5 s6 _ (.base (.LD .x11 .x6 (-16))) 4
  · simpa [fetch_at, s1, s2, s3, s4, s5, execInstrBr, MachineState.setPC, pc, BitVec.add_assoc] using c5
  · simp [s1, s2, s3, s4, s5, s6, ordinaryStep, memoryArgumentsValid, execInstrBr, signExtend12,
      accessValid, rangeValid, MEMORY_BYTES, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s6 s7 _ (.base (.SD .x7 .x11 (-16))) 3
  · simpa [fetch_at, s1, s2, s3, s4, s5, s6, execInstrBr, MachineState.setPC, pc, BitVec.add_assoc] using c6
  · simp [s1, s2, s3, s4, s5, s6, s7, ordinaryStep, memoryArgumentsValid, execInstrBr, signExtend12,
      accessValid, rangeValid, MEMORY_BYTES, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s7 s8 _ (.base (.LD .x11 .x6 (-8))) 2
  · simpa [fetch_at, s1, s2, s3, s4, s5, s6, s7, execInstrBr, MachineState.setPC, pc, BitVec.add_assoc] using c7
  · simp [s1, s2, s3, s4, s5, s6, s7, s8, ordinaryStep, memoryArgumentsValid, execInstrBr, signExtend12,
      accessValid, rangeValid, MEMORY_BYTES, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s8 s9 _ (.base (.SD .x7 .x11 (-8))) 1
  · simpa [fetch_at, s1, s2, s3, s4, s5, s6, s7, s8, execInstrBr, MachineState.setPC, pc, BitVec.add_assoc] using c8
  · simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, ordinaryStep, memoryArgumentsValid, execInstrBr, signExtend12,
      accessValid, rangeValid, MEMORY_BYTES, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s9 s10 _ (.base (.JAL .x0 8)) 0
  · simpa [fetch_at, s1, s2, s3, s4, s5, s6, s7, s8, s9, execInstrBr, MachineState.setPC, pc, BitVec.add_assoc] using c9
  · rfl
  exact OrdinarySteps.refl _

/-- info: 'SigGolfCandidate.Hypertree.FastCopy16.chain_input_executes' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms chain_input_executes

/-- Actual ten executed instructions of the replacement at the chain-output site. -/
def OutputCode (image : Image) (p : Word) : Prop :=
  instructionAt image (p + 0) = some (.base (.LUI .x6 128)) ∧
  instructionAt image (p + 4) = some (.base (.ADDI .x6 .x6 0x310)) ∧
  instructionAt image (p + 8) = some (.base (.LUI .x7 128)) ∧
  instructionAt image (p + 12) = some (.base (.ADDI .x7 .x7 0x520)) ∧
  instructionAt image (p + 16) = some (.base (.ADDI .x10 .x0 0)) ∧
  instructionAt image (p + 20) = some (.base (.LD .x11 .x6 (-16))) ∧
  instructionAt image (p + 24) = some (.base (.SD .x7 .x11 (-16))) ∧
  instructionAt image (p + 28) = some (.base (.LD .x11 .x6 (-8))) ∧
  instructionAt image (p + 32) = some (.base (.SD .x7 .x11 (-8))) ∧
  instructionAt image (p + 36) = some (.base (.JAL .x0 8))

theorem chain_output_executes (image : Image) (p : Word) (code : OutputCode image p)
    (s : MachineState) (pc : s.pc = p) :
    OrdinarySteps image s 10 (optimized s 0x300 0x510) := by
  obtain ⟨c0,c1,c2,c3,c4,c5,c6,c7,c8,c9⟩ := code
  let s1 := execInstrBr s (.LUI .x6 128)
  let s2 := execInstrBr s1 (.ADDI .x6 .x6 0x310)
  let s3 := execInstrBr s2 (.LUI .x7 128)
  let s4 := execInstrBr s3 (.ADDI .x7 .x7 0x520)
  let s5 := execInstrBr s4 (.ADDI .x10 .x0 0)
  let s6 := execInstrBr s5 (.LD .x11 .x6 (-16))
  let s7 := execInstrBr s6 (.SD .x7 .x11 (-16))
  let s8 := execInstrBr s7 (.LD .x11 .x6 (-8))
  let s9 := execInstrBr s8 (.SD .x7 .x11 (-8))
  let s10 := execInstrBr s9 (.JAL .x0 8)
  change OrdinarySteps image s 10 s10
  apply OrdinarySteps.step s s1 _ (.base (.LUI .x6 128)) 9
  · simpa [fetch_at, execInstrBr, MachineState.setPC, pc, BitVec.add_assoc] using c0
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.ADDI .x6 .x6 0x310)) 8
  · simpa [fetch_at, s1, execInstrBr, MachineState.setPC, pc, BitVec.add_assoc] using c1
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.LUI .x7 128)) 7
  · simpa [fetch_at, s1, s2, execInstrBr, MachineState.setPC, pc, BitVec.add_assoc] using c2
  · rfl
  apply OrdinarySteps.step s3 s4 _ (.base (.ADDI .x7 .x7 0x520)) 6
  · simpa [fetch_at, s1, s2, s3, execInstrBr, MachineState.setPC, pc, BitVec.add_assoc] using c3
  · rfl
  apply OrdinarySteps.step s4 s5 _ (.base (.ADDI .x10 .x0 0)) 5
  · simpa [fetch_at, s1, s2, s3, s4, execInstrBr, MachineState.setPC, pc, BitVec.add_assoc] using c4
  · rfl
  apply OrdinarySteps.step s5 s6 _ (.base (.LD .x11 .x6 (-16))) 4
  · simpa [fetch_at, s1, s2, s3, s4, s5, execInstrBr, MachineState.setPC, pc, BitVec.add_assoc] using c5
  · simp [s1, s2, s3, s4, s5, s6, ordinaryStep, memoryArgumentsValid, execInstrBr, signExtend12,
      accessValid, rangeValid, MEMORY_BYTES, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s6 s7 _ (.base (.SD .x7 .x11 (-16))) 3
  · simpa [fetch_at, s1, s2, s3, s4, s5, s6, execInstrBr, MachineState.setPC, pc, BitVec.add_assoc] using c6
  · simp [s1, s2, s3, s4, s5, s6, s7, ordinaryStep, memoryArgumentsValid, execInstrBr, signExtend12,
      accessValid, rangeValid, MEMORY_BYTES, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s7 s8 _ (.base (.LD .x11 .x6 (-8))) 2
  · simpa [fetch_at, s1, s2, s3, s4, s5, s6, s7, execInstrBr, MachineState.setPC, pc, BitVec.add_assoc] using c7
  · simp [s1, s2, s3, s4, s5, s6, s7, s8, ordinaryStep, memoryArgumentsValid, execInstrBr, signExtend12,
      accessValid, rangeValid, MEMORY_BYTES, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s8 s9 _ (.base (.SD .x7 .x11 (-8))) 1
  · simpa [fetch_at, s1, s2, s3, s4, s5, s6, s7, s8, execInstrBr, MachineState.setPC, pc, BitVec.add_assoc] using c8
  · simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, ordinaryStep, memoryArgumentsValid, execInstrBr, signExtend12,
      accessValid, rangeValid, MEMORY_BYTES, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s9 s10 _ (.base (.JAL .x0 8)) 0
  · simpa [fetch_at, s1, s2, s3, s4, s5, s6, s7, s8, s9, execInstrBr, MachineState.setPC, pc, BitVec.add_assoc] using c9
  · rfl
  exact OrdinarySteps.refl _

/-- info: 'SigGolfCandidate.Hypertree.FastCopy16.chain_output_executes' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms chain_output_executes


/-- Experimental image emitted by the local generator; not yet fully certified. -/
def experimentalVerify : Image where
  code := [
    0x00000313, 0x00080e37, 0x440e0e13, 0x006e3023, 0x0003d337, 0x3d030313, 0x00080e37, 0x448e0e13,
    0x006e3023, 0x04000313, 0x000803b7, 0x02038393, 0x00200513, 0x00033583, 0x00b3b023, 0x00830313,
    0x00838393, 0xfff50513, 0xfe0516e3, 0x00000313, 0x000803b7, 0x03038393, 0x00400513, 0x00033583,
    0x00b3b023, 0x00830313, 0x00838393, 0xfff50513, 0xfe0516e3, 0x0003d337, 0x3b030313, 0x000803b7,
    0x05038393, 0x00400513, 0x00033583, 0x00b3b023, 0x00830313, 0x00838393, 0xfff50513, 0xfe0516e3,
    0x00500513, 0x00080e37, 0x000e0e13, 0x00ae3023, 0x00000593, 0x00080e37, 0x008e0e13, 0x00be3023,
    0x00000593, 0x00080e37, 0x010e0e13, 0x00be3023, 0x00000593, 0x00080e37, 0x018e0e13, 0x00be3023,
    0x00080537, 0x00050513, 0x07000593, 0x00080637, 0x30060613, 0x00100293, 0x00000073, 0x00080337,
    0x30030313, 0x000803b7, 0x40838393, 0x00200513, 0x00033583, 0x00b3b023, 0x00830313, 0x00838393,
    0xfff50513, 0xfe0516e3, 0x00080e37, 0x310e0e13, 0x000e3303, 0x02031313, 0x02035313, 0x00080e37,
    0x418e0e13, 0x006e3023, 0x00080e37, 0x408e0e13, 0x000e3303, 0x00080e37, 0x410e0e13, 0x000e3383,
    0x00080e37, 0x418e0e13, 0x000e3503, 0x00137593, 0x00080e37, 0x420e0e13, 0x00be3023, 0x00135313,
    0x03f39593, 0x00b30333, 0x00080e37, 0x408e0e13, 0x006e3023, 0x0013d393, 0x03f51593, 0x00b383b3,
    0x00080e37, 0x410e0e13, 0x007e3023, 0x00155513, 0x00080e37, 0x418e0e13, 0x00ae3023, 0x00080e37,
    0x400e0e13, 0x000e3303, 0x00030463, 0x09c000ef, 0x120000ef, 0x00080e37, 0x400e0e13, 0x000e3303,
    0x00080e37, 0x448e0e13, 0x000e3383, 0x00030663, 0x2f038393, 0x0080006f, 0x02038393, 0x00080e37,
    0x448e0e13, 0x007e3023, 0x00130313, 0x00080e37, 0x400e0e13, 0x006e3023, 0x0a000393, 0xf27316e3,
    0x00080e37, 0x500e0e13, 0x000e3303, 0x04000e13, 0x000e3383, 0x02731463, 0x00080e37, 0x508e0e13,
    0x000e3303, 0x04800e13, 0x000e3383, 0x00731863, 0x00000293, 0x00100513, 0x00000073, 0x00000293,
    0x00000513, 0x00000073, 0xff010113, 0x00113023, 0x00080e37, 0x500e0e13, 0x000e3303, 0x00080e37,
    0x508e0e13, 0x000e3383, 0x00080537, 0x60050513, 0x02b00593, 0x12d00613, 0x00737693, 0x00d50023,
    0x40d60633, 0x00335313, 0x03d39693, 0x00d30333, 0x0033d393, 0x00150513, 0xfff58593, 0xfc059ee3,
    0x00767693, 0x00d50023, 0x00365613, 0x00767693, 0x00d500a3, 0x00365613, 0x00767693, 0x00d50123,
    0x00365613, 0x00013083, 0x01010113, 0x00008067, 0xff010113, 0x00113023, 0x00080e37, 0x420e0e13,
    0x000e3303, 0x00080e37, 0x428e0e13, 0x006e3023, 0x148000ef, 0x00080e37, 0x420e0e13, 0x000e3303,
    0x00134313, 0x00431313, 0x000803b7, 0x52038393, 0x006383b3, 0x00080e37, 0x448e0e13, 0x000e3503,
    0x00080e37, 0x400e0e13, 0x000e3583, 0x00058663, 0x2e050513, 0x0080006f, 0x01050513, 0x00053583,
    0x00853603, 0x00b3b023, 0x00c3b423, 0x00080337, 0x52030313, 0x000803b7, 0x02038393, 0x00400513,
    0x00033583, 0x00b3b023, 0x00830313, 0x00838393, 0xfff50513, 0xfe0516e3, 0x00400513, 0x00080e37,
    0x400e0e13, 0x000e3583, 0x00859593, 0x00b50533, 0x00080e37, 0x000e0e13, 0x00ae3023, 0x00080e37,
    0x408e0e13, 0x000e3583, 0x00080e37, 0x008e0e13, 0x00be3023, 0x00080e37, 0x410e0e13, 0x000e3583,
    0x00080e37, 0x010e0e13, 0x00be3023, 0x00080e37, 0x418e0e13, 0x000e3583, 0x00080e37, 0x018e0e13,
    0x00be3023, 0x00080537, 0x00050513, 0x04000593, 0x00080637, 0x30060613, 0x00100293, 0x00000073,
    0x00080337, 0x30030313, 0x000803b7, 0x50038393, 0x00200513, 0x00033583, 0x00b3b023, 0x00830313,
    0x00838393, 0xfff50513, 0xfe0516e3, 0x00013083, 0x01010113, 0x00008067, 0xff010113, 0x00113023,
    0x00000313, 0x00080e37, 0x430e0e13, 0x006e3023, 0x00000313, 0x00080e37, 0x438e0e13, 0x006e3023,
    0x00080e37, 0x400e0e13, 0x000e3303, 0x30030c63, 0x00080e37, 0x430e0e13, 0x000e3303, 0x00080e37,
    0x448e0e13, 0x000e3383, 0x00431513, 0x00a383b3, 0x0003b503, 0x0083b583, 0x00080e37, 0x510e0e13,
    0x00ae3023, 0x00080e37, 0x518e0e13, 0x00be3023, 0x000803b7, 0x60038393, 0x006383b3, 0x0003c503,
    0x00080e37, 0x438e0e13, 0x00ae3023, 0x00080e37, 0x438e0e13, 0x000e3303, 0x00700393, 0x14730063,
    0x00080337, 0x52030313, 0x000803b7, 0x03038393, 0x00000513, 0xff033583, 0xfeb3b823, 0xff833583,
    0xfeb3bc23, 0x0080006f, 0x00000013, 0x00200513, 0x00080e37, 0x400e0e13, 0x000e3583, 0x00859593,
    0x00b50533, 0x00080e37, 0x428e0e13, 0x000e3583, 0x01059593, 0x00b50533, 0x00080e37, 0x430e0e13,
    0x000e3583, 0x01859593, 0x00b50533, 0x00080e37, 0x438e0e13, 0x000e3583, 0x02059593, 0x00b50533,
    0x00080e37, 0x000e0e13, 0x00ae3023, 0x00080e37, 0x408e0e13, 0x000e3583, 0x00080e37, 0x008e0e13,
    0x00be3023, 0x00080e37, 0x410e0e13, 0x000e3583, 0x00080e37, 0x010e0e13, 0x00be3023, 0x00080e37,
    0x418e0e13, 0x000e3583, 0x00080e37, 0x018e0e13, 0x00be3023, 0x00080537, 0x00050513, 0x03000593,
    0x00080637, 0x30060613, 0x00100293, 0x00000073, 0x00080337, 0x31030313, 0x000803b7, 0x52038393,
    0x00000513, 0xff033583, 0xfeb3b823, 0xff833583, 0xfeb3bc23, 0x0080006f, 0x00000013, 0x00080e37,
    0x438e0e13, 0x000e3303, 0x00130313, 0x00080e37, 0x438e0e13, 0x006e3023, 0xeb5ff06f, 0x00080e37,
    0x430e0e13, 0x000e3303, 0x00431393, 0x00081537, 0x80050513, 0x00a383b3, 0x00080e37, 0x510e0e13,
    0x000e3503, 0x00080e37, 0x518e0e13, 0x000e3583, 0x00a3b023, 0x00b3b423, 0x00130313, 0x00080e37,
    0x430e0e13, 0x006e3023, 0x02e00393, 0xe07312e3, 0x00081337, 0x80030313, 0x000803b7, 0x02038393,
    0x05c00513, 0x00033583, 0x00b3b023, 0x00830313, 0x00838393, 0xfff50513, 0xfe0516e3, 0x00300513,
    0x00080e37, 0x400e0e13, 0x000e3583, 0x00859593, 0x00b50533, 0x00080e37, 0x428e0e13, 0x000e3583,
    0x01059593, 0x00b50533, 0x00080e37, 0x000e0e13, 0x00ae3023, 0x00080e37, 0x408e0e13, 0x000e3583,
    0x00080e37, 0x008e0e13, 0x00be3023, 0x00080e37, 0x410e0e13, 0x000e3583, 0x00080e37, 0x010e0e13,
    0x00be3023, 0x00080e37, 0x418e0e13, 0x000e3583, 0x00080e37, 0x018e0e13, 0x00be3023, 0x00080537,
    0x00050513, 0x000005b7, 0x30058593, 0x00080637, 0x30060613, 0x00100293, 0x00000073, 0x00080e37,
    0x428e0e13, 0x000e3303, 0x00431313, 0x000803b7, 0x52038393, 0x006383b3, 0x00080e37, 0x300e0e13,
    0x000e3503, 0x00080e37, 0x308e0e13, 0x000e3583, 0x00a3b023, 0x00b3b423, 0x00013083, 0x01010113,
    0x00008067, 0x00080e37, 0x448e0e13, 0x000e3383, 0x0003b503, 0x0083b583, 0x00080e37, 0x510e0e13,
    0x00ae3023, 0x00080e37, 0x518e0e13, 0x00be3023, 0x00080337, 0x51030313, 0x000803b7, 0x02038393,
    0x00200513, 0x00033583, 0x00b3b023, 0x00830313, 0x00838393, 0xfff50513, 0xfe0516e3, 0x00200513,
    0x00080e37, 0x400e0e13, 0x000e3583, 0x00859593, 0x00b50533, 0x00080e37, 0x428e0e13, 0x000e3583,
    0x01059593, 0x00b50533, 0x00080e37, 0x430e0e13, 0x000e3583, 0x01859593, 0x00b50533, 0x00080e37,
    0x438e0e13, 0x000e3583, 0x02059593, 0x00b50533, 0x00080e37, 0x000e0e13, 0x00ae3023, 0x00080e37,
    0x408e0e13, 0x000e3583, 0x00080e37, 0x008e0e13, 0x00be3023, 0x00080e37, 0x410e0e13, 0x000e3583,
    0x00080e37, 0x010e0e13, 0x00be3023, 0x00080e37, 0x418e0e13, 0x000e3583, 0x00080e37, 0x018e0e13,
    0x00be3023, 0x00080537, 0x00050513, 0x03000593, 0x00080637, 0x30060613, 0x00100293, 0x00000073,
    0x00080e37, 0x428e0e13, 0x000e3303, 0x00431313, 0x000803b7, 0x52038393, 0x006383b3, 0x00080e37,
    0x300e0e13, 0x000e3503, 0x00080e37, 0x308e0e13, 0x000e3583, 0x00a3b023, 0x00b3b423, 0x00013083,
    0x01010113, 0x00008067]
  data := []

theorem experimental_input_code : InputCode experimentalVerify 0x1500 := by unfold InputCode; decide
theorem experimental_output_code : OutputCode experimentalVerify 0x15f0 := by unfold OutputCode; decide

theorem experimental_input_replaces (s : MachineState) (pc : s.pc = 0x1500) :
    OrdinarySteps experimentalVerify s 10 (original s 0x510 0x20) := by
  rw [← chain_input_equiv]
  exact chain_input_executes experimentalVerify 0x1500 experimental_input_code s pc

theorem experimental_output_replaces (s : MachineState) (pc : s.pc = 0x15f0) :
    OrdinarySteps experimentalVerify s 10 (original s 0x300 0x510) := by
  rw [← chain_output_equiv]
  exact chain_output_executes experimentalVerify 0x15f0 experimental_output_code s pc

/-- info: 'SigGolfCandidate.Hypertree.FastCopy16.experimental_input_replaces' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms experimental_input_replaces

/-- info: 'SigGolfCandidate.Hypertree.FastCopy16.experimental_output_replaces' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms experimental_output_replaces

theorem input_spec (s : MachineState) :
    (optimized s 0x510 0x20).pc = s.pc + 44 ∧
    (optimized s 0x510 0x20).getReg .x1 = s.getReg .x1 ∧
    (optimized s 0x510 0x20).getReg .x2 = s.getReg .x2 ∧
    (∀ i : Fin 2, (optimized s 0x510 0x20).getMem (Signing.wordAddress 0x80020 i.val) =
      s.getMem (Signing.wordAddress 0x80510 i.val)) ∧
    (∀ a, a ≠ 0x80020#64 → a ≠ 0x80028#64 → (optimized s 0x510 0x20).getMem a = s.getMem a) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [optimized, copySetup, execInstrBr, MachineState.getReg, MachineState.setReg, MachineState.setPC, MachineState.getMem, MachineState.setMem, signExtend12, signExtend21, BitVec.add_assoc]
  · simp [optimized, copySetup, execInstrBr, MachineState.getReg, MachineState.setReg, MachineState.setPC, MachineState.getMem, MachineState.setMem, signExtend12, signExtend21, BitVec.add_assoc]
  · simp [optimized, copySetup, execInstrBr, MachineState.getReg, MachineState.setReg, MachineState.setPC, MachineState.getMem, MachineState.setMem, signExtend12, signExtend21, BitVec.add_assoc]
  · intro i
    fin_cases i <;> simp [optimized, copySetup, execInstrBr, MachineState.getReg, MachineState.setReg, MachineState.setPC, MachineState.getMem, MachineState.setMem, signExtend12, signExtend21, BitVec.add_assoc, Signing.wordAddress]
  · intro a h0 h1
    simp [optimized, copySetup, execInstrBr, MachineState.getReg, MachineState.setReg, MachineState.setPC, MachineState.getMem, MachineState.setMem, signExtend12, signExtend21, BitVec.add_assoc, h0, h1]

theorem output_spec (s : MachineState) :
    (optimized s 0x300 0x510).pc = s.pc + 44 ∧
    (optimized s 0x300 0x510).getReg .x1 = s.getReg .x1 ∧
    (optimized s 0x300 0x510).getReg .x2 = s.getReg .x2 ∧
    (∀ i : Fin 2, (optimized s 0x300 0x510).getMem (Signing.wordAddress 0x80510 i.val) =
      s.getMem (Signing.wordAddress 0x80300 i.val)) ∧
    (∀ a, a ≠ 0x80510#64 → a ≠ 0x80518#64 → (optimized s 0x300 0x510).getMem a = s.getMem a) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [optimized, copySetup, execInstrBr, MachineState.getReg, MachineState.setReg, MachineState.setPC, MachineState.getMem, MachineState.setMem, signExtend12, signExtend21, BitVec.add_assoc]
  · simp [optimized, copySetup, execInstrBr, MachineState.getReg, MachineState.setReg, MachineState.setPC, MachineState.getMem, MachineState.setMem, signExtend12, signExtend21, BitVec.add_assoc]
  · simp [optimized, copySetup, execInstrBr, MachineState.getReg, MachineState.setReg, MachineState.setPC, MachineState.getMem, MachineState.setMem, signExtend12, signExtend21, BitVec.add_assoc]
  · intro i
    fin_cases i <;> simp [optimized, copySetup, execInstrBr, MachineState.getReg, MachineState.setReg, MachineState.setPC, MachineState.getMem, MachineState.setMem, signExtend12, signExtend21, BitVec.add_assoc, Signing.wordAddress]
  · intro a h0 h1
    simp [optimized, copySetup, execInstrBr, MachineState.getReg, MachineState.setReg, MachineState.setPC, MachineState.getMem, MachineState.setMem, signExtend12, signExtend21, BitVec.add_assoc, h0, h1]

theorem copy_input (image : Image) (p : Word) (code : InputCode image p)
    (s : MachineState) (pc : s.pc = p) :
    ∃ final, OrdinarySteps image s 10 final ∧ final.pc = p+44 ∧
      (∀ i : Fin 2, final.getMem (Signing.wordAddress 0x80020 i.val) = s.getMem (Signing.wordAddress 0x80510 i.val)) ∧
      final.getReg .x1 = s.getReg .x1 ∧ final.getReg .x2 = s.getReg .x2 ∧
      (∀ a, (∀ i : Fin 2, a ≠ Signing.wordAddress 0x80020 i.val) → final.getMem a = s.getMem a) := by
  obtain ⟨hp, ra, sp, values, frame⟩ := input_spec s
  refine ⟨optimized s 0x510 0x20, chain_input_executes image p code s pc, by simpa [pc] using hp, values, ra, sp, ?_⟩
  intro a h
  apply frame a
  · simpa [Signing.wordAddress] using h 0
  · simpa [Signing.wordAddress] using h 1

theorem copy_output (image : Image) (p : Word) (code : OutputCode image p)
    (s : MachineState) (pc : s.pc = p) :
    ∃ final, OrdinarySteps image s 10 final ∧ final.pc = p+44 ∧
      (∀ i : Fin 2, final.getMem (Signing.wordAddress 0x80510 i.val) = s.getMem (Signing.wordAddress 0x80300 i.val)) ∧
      final.getReg .x1 = s.getReg .x1 ∧ final.getReg .x2 = s.getReg .x2 ∧
      (∀ a, (∀ i : Fin 2, a ≠ Signing.wordAddress 0x80510 i.val) → final.getMem a = s.getMem a) := by
  obtain ⟨hp, ra, sp, values, frame⟩ := output_spec s
  refine ⟨optimized s 0x300 0x510, chain_output_executes image p code s pc, by simpa [pc] using hp, values, ra, sp, ?_⟩
  intro a h
  apply frame a
  · simpa [Signing.wordAddress] using h 0
  · simpa [Signing.wordAddress] using h 1

def ChainCode (image : Image) (p : Word) : Prop :=
  InputCode image p ∧ KeygenChainHeader.Code image (p+44) ∧
  instructionAt image (p+236) = some (.base .ECALL) ∧ OutputCode image (p+240)

theorem chain_compute (image : Image) (hash : Hash) (p : Word) (code : ChainCode image p)
    (s : MachineState) (pc : s.pc = p) (level tree step : Nat)
    (side : Bool) (chain : Reference.Chain) (value : Reference.Digest)
    (hlevel : s.getMem 0x80400 = BitVec.ofNat 64 level)
    (hleaf : s.getMem 0x80428 = BitVec.ofNat 64 (Reference.sideNumber side))
    (hchain : s.getMem 0x80430 = BitVec.ofNat 64 chain.val)
    (hstep : s.getMem 0x80438 = BitVec.ofNat 64 step)
    (hindex : ∀ i : Fin 3, s.getMem (Signing.wordAddress 0x80408 i.val) =
      (BitVec.ofNat 192 tree).extractLsb' (64*i.val) 64)
    (hvalue : ∀ i : Fin 2, s.getMem (Signing.wordAddress 0x80510 i.val) =
      value.extractLsb' (64*i.val) 64) :
    ∃ final, Trace hash image s 69 76 1 1 final ∧ final.pc = p+284 ∧
      (∀ i : Fin 2, final.getMem (Signing.wordAddress 0x80510 i.val) =
        (Reference.chainHash hash level tree side chain step value).extractLsb' (64*i.val) 64) ∧
      final.getReg .x1 = s.getReg .x1 ∧ final.getReg .x2 = s.getReg .x2 ∧
      (∀ a, (∀ i : Fin 6, a ≠ Signing.wordAddress 0x80000 i.val) →
        (∀ i : Fin 4, a ≠ Signing.wordAddress 0x80300 i.val) →
        (∀ i : Fin 2, a ≠ Signing.wordAddress 0x80510 i.val) →
        final.getMem a = s.getMem a) := by
  obtain ⟨copied,pre,cpc,content,cra,csp,cframe⟩ :=
    copy_input image p code.1 s pc
  have levelEq : copied.getMem 0x80400 = BitVec.ofNat 64 level := by
    rw [cframe _ (by intro i; fin_cases i <;> decide)]; exact hlevel
  have leafEq : copied.getMem 0x80428 = BitVec.ofNat 64 (Reference.sideNumber side) := by
    rw [cframe _ (by intro i; fin_cases i <;> decide)]; exact hleaf
  have chainEq : copied.getMem 0x80430 = BitVec.ofNat 64 chain.val := by
    rw [cframe _ (by intro i; fin_cases i <;> decide)]; exact hchain
  have stepEq : copied.getMem 0x80438 = BitVec.ofNat 64 step := by
    rw [cframe _ (by intro i; fin_cases i <;> decide)]; exact hstep
  have indexEq : ∀ i : Fin 3, copied.getMem (Signing.wordAddress 0x80408 i.val) =
      (BitVec.ofNat 192 tree).extractLsb' (64*i.val) 64 := by
    intro i
    rw [cframe _ (by intro j; fin_cases i <;> fin_cases j <;> decide)]
    exact hindex i
  have valueEq : ∀ i : Fin 2, copied.getMem (Signing.wordAddress 0x80020 i.val) =
      value.extractLsb' (64*i.val) 64 := by intro i; rw [content i]; exact hvalue i
  let prepared := KeygenChainHeader.state copied
  have headTrace := KeygenChainHeader.block image (p+44) code.2.1 copied cpc
  have hpc : prepared.pc = p+236 := by
    simp only [prepared,KeygenChainHeader.pc,cpc]; simp [BitVec.add_assoc]
  obtain ⟨service,source,bits,destination⟩ := KeygenChainHeader.regs copied
  have words := KeygenChainHeader.words copied level tree (Reference.sideNumber side) chain.val step value
    levelEq leafEq chainEq stepEq indexEq valueEq
  have hf : fetch image prepared = some (.base .ECALL) := by
    simpa only [fetch_at,hpc] using code.2.2.1
  let hashed := writeHash prepared (hash (hashInput prepared))
  have hashTrace := KeygenDomain.hash_trace image hash prepared hf service source bits destination
  have hashPC : hashed.pc = p+240 := by simp only [hashed,hash_pc,hpc]; simp [BitVec.add_assoc]
  obtain ⟨final,post,fpc,result,fra,fsp,fframe⟩ :=
    copy_output image (p+240) code.2.2.2 hashed hashPC
  refine ⟨final,pre.trace.trans (headTrace.trace.trans (hashTrace.trans post.trace)),?_,?_,?_,?_,?_⟩
  · simpa [BitVec.add_assoc] using fpc
  · intro i
    rw [result i]
    exact KeygenDomain.answer_words hash prepared 2 level tree (Reference.sideNumber side) chain.val step value
      source bits destination words i
  · exact fra.trans ((hash_registers _ _ _).trans ((KeygenChainHeader.stack copied).1.trans cra))
  · exact fsp.trans ((hash_registers _ _ _).trans ((KeygenChainHeader.stack copied).2.trans csp))
  · intro a inputOutside answerOutside valueOutside
    rw [fframe a valueOutside,Signing.hash_answer_frame prepared _ destination a answerOutside]
    rw [KeygenChainHeader.frame copied a (fun i => inputOutside ⟨i.val,by have := i.isLt; omega⟩)]
    apply cframe
    intro i
    have h := inputOutside ⟨i.val+4,by have := i.isLt; omega⟩
    simpa [Signing.wordAddress,Nat.mul_add,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h

theorem experimental_chain_code : ChainCode experimentalVerify 0x1500 := by
  unfold ChainCode InputCode OutputCode
  decide

/-- info: 'SigGolfCandidate.Hypertree.FastCopy16.chain_compute' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms chain_compute

end SigGolfCandidate.Hypertree.FastCopy16
