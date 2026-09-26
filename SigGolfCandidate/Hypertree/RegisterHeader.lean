import SigGolfCandidate.Hypertree.PersistentStepBase
import SigGolfCandidate.Hypertree.CounterCheck
import SigGolfCandidate.Hypertree.InplaceHash
namespace SigGolfCandidate.Hypertree.RegisterHeader
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 Keygen
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false

/-- x14 retains the first hash header word between chain calls. -/
def Ready (s : MachineState) : Prop := s.getReg .x14 = s.getMem 0x80000

def prepare (s : MachineState) : MachineState :=
  let s := execInstrBr s (.ADD .x14 .x14 .x13)
  let s := execInstrBr s (.SD .x28 .x14 (-1080))
  let s := execInstrBr s (.ADDI .x10 .x28 (-1080))
  execInstrBr s (.JAL .x0 92)

theorem prepare_equiv (s : MachineState) (base : s.getReg .x28 = 0x80438) (ready : Ready s) :
    prepare s = (PersistentStepBase.prepare s).setReg .x14 (s.getReg .x14+s.getReg .x13) := by
  cases s with
  | mk regs mem code pc committed publicValues privateInput inputBufBase =>
    simp [MachineState.getReg] at base
    simp [Ready,MachineState.getReg,MachineState.getMem] at ready
    simp [prepare,PersistentStepBase.prepare,execInstrBr,MachineState.getReg,MachineState.setReg,
      MachineState.getMem,MachineState.setMem,MachineState.setPC,signExtend12,signExtend21,base,ready,BitVec.add_assoc]
    all_goals first | rfl | (funext r; cases r <;> simp_all)

theorem prepare_ready (s : MachineState) (base : s.getReg .x28 = 0x80438) : Ready (prepare s) := by
  simp [Ready,prepare,execInstrBr,MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,
    MachineState.getMem_setReg,MachineState.getMem_setMem_eq,
    MachineState.getReg_setPC,MachineState.getMem_setPC,base,signExtend12]

theorem finish_ready (s : MachineState) (base : s.getReg .x28 = 0x80438) (ready : Ready s) :
    Ready (PersistentStepBase.finish s) := by
  simpa [Ready,PersistentStepBase.finish,execInstrBr,MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,
    MachineState.getMem_setReg,MachineState.getMem_setMem_ne,
    MachineState.getReg_setPC,MachineState.getMem_setPC,base,signExtend12] using ready

theorem check_ready (s : MachineState) (ready : Ready s) : Ready (CounterCheck.shortCheck s) := by
  simpa [Ready,CounterCheck.shortCheck,CounterCheck.state,PersistentLimit.check,execInstrBr] using ready

theorem hash_ready (s : MachineState) (digest : BitVec 256)
    (destination : s.getReg .x12 = 0x80020) (ready : Ready s) : Ready (writeHash s digest) := by
  unfold Ready at *
  rw [hash_registers,InplaceHash.frame s digest destination _ (by intro i; fin_cases i <;> decide)]
  exact ready

def initialPrefix (s : MachineState) : MachineState :=
  let s := execInstrBr s (.LD .x11 .x28 (216))
  let s := execInstrBr s (.SD .x28 .x11 (-1048))
  let s := execInstrBr s (.LD .x11 .x28 (224))
  let s := execInstrBr s (.SD .x28 .x11 (-1040))
  let s := execInstrBr s (.ADDI .x14 .x0 2)
  let s := execInstrBr s (.LD .x11 .x28 (-56))
  let s := execInstrBr s (.SLLI .x11 .x11 8)
  let s := execInstrBr s (.ADD .x14 .x14 .x11)
  let s := execInstrBr s (.LD .x11 .x28 (-16))
  let s := execInstrBr s (.SLLI .x11 .x11 16)
  let s := execInstrBr s (.ADD .x14 .x14 .x11)
  let s := execInstrBr s (.LD .x11 .x28 (-8))
  let s := execInstrBr s (.SLLI .x11 .x11 24)
  let s := execInstrBr s (.ADD .x14 .x14 .x11)
  let s := execInstrBr s (.LD .x11 .x28 (0))
  let s := execInstrBr s (.SLLI .x11 .x11 32)
  let s := execInstrBr s (.ADD .x14 .x14 .x11)
  let s := execInstrBr s (.SD .x28 .x14 (-1080))
  let s := execInstrBr s (.LD .x11 .x28 (-48))
  let s := execInstrBr s (.SD .x28 .x11 (-1072))
  let s := execInstrBr s (.LD .x11 .x28 (-40))
  let s := execInstrBr s (.SD .x28 .x11 (-1064))
  let s := execInstrBr s (.LD .x11 .x28 (-32))
  execInstrBr s (.SD .x28 .x11 (-1056))

def initial (s : MachineState) : MachineState := PersistentStepBase.newTail (initialPrefix s)

/-- info: 'SigGolfCandidate.Hypertree.RegisterHeader.prepare_equiv' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms prepare_equiv
end SigGolfCandidate.Hypertree.RegisterHeader
