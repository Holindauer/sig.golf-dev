import SigGolfCandidate.Hypertree.CounterArgs
import SigGolfCandidate.Hypertree.RegisterCounter
namespace SigGolfCandidate.Hypertree.PersistentStepBase
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 Keygen
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false

def finish (s : MachineState) : MachineState :=
  let s := execInstrBr s (.ADDI .x6 .x6 1)
  let s := execInstrBr s (.SD .x28 .x6 0)
  execInstrBr s (.JAL .x0 (-120))

theorem finish_equiv (s : MachineState) (base : s.getReg .x28 = 0x80438) :
    finish s = RegisterCounter.finish (s.setReg .x28 0x80018) := by
  cases s with
  | mk regs mem code pc committed publicValues privateInput inputBufBase =>
    simp [MachineState.getReg] at base
    simp [finish,RegisterCounter.finish,execInstrBr,MachineState.getReg,MachineState.setReg,
      MachineState.getMem,MachineState.setMem,MachineState.setPC,signExtend12,signExtend21,base,BitVec.add_assoc]
    all_goals first | rfl | (funext r; cases r <;> simp_all)

def prepare (s : MachineState) : MachineState :=
  let s := execInstrBr s (.LD .x10 .x28 (-1080))
  let s := execInstrBr s (.ADD .x10 .x10 .x13)
  let s := execInstrBr s (.SD .x28 .x10 (-1080))
  let s := execInstrBr s (.ADDI .x10 .x28 (-1080))
  execInstrBr s (.JAL .x0 88)

theorem prepare_equiv (s : MachineState) (base : s.getReg .x28 = 0x80438) :
    prepare s = ((CounterArgs.state s).setReg .x28 0x80438).setPC (s.pc+104) := by
  cases s with
  | mk regs mem code pc committed publicValues privateInput inputBufBase =>
    simp [MachineState.getReg] at base
    simp [prepare,CounterArgs.state,execInstrBr,MachineState.getReg,MachineState.setReg,
      MachineState.getMem,MachineState.setMem,MachineState.setPC,signExtend12,signExtend21,base,BitVec.add_assoc]
    all_goals first | rfl | (funext r; cases r <;> simp_all)

def initialPrefix (s : MachineState) : MachineState :=
  let s := execInstrBr s (.LD .x11 .x28 (216))
  let s := execInstrBr s (.SD .x28 .x11 (-1048))
  let s := execInstrBr s (.LD .x11 .x28 (224))
  let s := execInstrBr s (.SD .x28 .x11 (-1040))
  let s := execInstrBr s (.ADDI .x10 .x0 2)
  let s := execInstrBr s (.LD .x11 .x28 (-56))
  let s := execInstrBr s (.SLLI .x11 .x11 8)
  let s := execInstrBr s (.ADD .x10 .x10 .x11)
  let s := execInstrBr s (.LD .x11 .x28 (-16))
  let s := execInstrBr s (.SLLI .x11 .x11 16)
  let s := execInstrBr s (.ADD .x10 .x10 .x11)
  let s := execInstrBr s (.LD .x11 .x28 (-8))
  let s := execInstrBr s (.SLLI .x11 .x11 24)
  let s := execInstrBr s (.ADD .x10 .x10 .x11)
  let s := execInstrBr s (.LD .x11 .x28 (0))
  let s := execInstrBr s (.SLLI .x11 .x11 32)
  let s := execInstrBr s (.ADD .x10 .x10 .x11)
  let s := execInstrBr s (.SD .x28 .x10 (-1080))
  let s := execInstrBr s (.LD .x11 .x28 (-48))
  let s := execInstrBr s (.SD .x28 .x11 (-1072))
  let s := execInstrBr s (.LD .x11 .x28 (-40))
  let s := execInstrBr s (.SD .x28 .x11 (-1064))
  let s := execInstrBr s (.LD .x11 .x28 (-32))
  execInstrBr s (.SD .x28 .x11 (-1056))

def oldTail (s : MachineState) : MachineState :=
  let s := execInstrBr s (.ADDI .x28 .x28 (-1056))
  let s := execInstrBr s (.ADDI .x10 .x28 (-24))
  let s := execInstrBr s (.ADDI .x11 .x0 48)
  let s := execInstrBr s (.ADDI .x12 .x28 8)
  let s := execInstrBr s (.ADDI .x5 .x0 1)
  let s := execInstrBr s (.ADDI .x13 .x0 1)
  let s := execInstrBr s (.SLLI .x13 .x13 32)
  execInstrBr s (.JAL .x0 112)

def newTail (s : MachineState) : MachineState :=
  let s := execInstrBr s (.ADDI .x10 .x28 (-1080))
  let s := execInstrBr s (.ADDI .x11 .x0 48)
  let s := execInstrBr s (.ADDI .x12 .x28 (-1048))
  let s := execInstrBr s (.ADDI .x5 .x0 1)
  let s := execInstrBr s (.ADDI .x13 .x0 1)
  let s := execInstrBr s (.SLLI .x13 .x13 32)
  execInstrBr s (.JAL .x0 116)

theorem prefix_base (s : MachineState) : (initialPrefix s).getReg .x28 = s.getReg .x28 := by
  simp [initialPrefix,execInstrBr,MachineState.getReg_setReg_ne]

theorem tail_equiv (s : MachineState) (base : s.getReg .x28 = 0x80438) :
    newTail s = (oldTail s).setReg .x28 0x80438 := by
  cases s with
  | mk regs mem code pc committed publicValues privateInput inputBufBase =>
    simp [MachineState.getReg] at base
    simp [newTail,oldTail,execInstrBr,MachineState.getReg,MachineState.setReg,
      MachineState.getMem,MachineState.setMem,MachineState.setPC,signExtend12,signExtend21,base,BitVec.add_assoc]
    all_goals first | rfl | (funext r; cases r <;> simp_all)

def initial (s : MachineState) : MachineState := newTail (initialPrefix s)

theorem initial_equiv (s : MachineState) (base : s.getReg .x28 = 0x80438) :
    initial s = (InplaceInitialPrepare.state s).setReg .x28 0x80438 := by
  change newTail (initialPrefix s) = (oldTail (initialPrefix s)).setReg .x28 0x80438
  exact tail_equiv _ ((prefix_base s).trans base)

/-- info: 'SigGolfCandidate.Hypertree.PersistentStepBase.initial_equiv' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms initial_equiv
/-- info: 'SigGolfCandidate.Hypertree.PersistentStepBase.finish_equiv' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms finish_equiv
/-- info: 'SigGolfCandidate.Hypertree.PersistentStepBase.prepare_equiv' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms prepare_equiv
end SigGolfCandidate.Hypertree.PersistentStepBase
