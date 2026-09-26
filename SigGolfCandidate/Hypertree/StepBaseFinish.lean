import SigGolfCandidate.Hypertree.StepBaseBlocks
namespace SigGolfCandidate.Hypertree.StepBaseFinish
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 Keygen
set_option maxRecDepth 8192
abbrev state := PersistentStepBase.finish

theorem mem (s : MachineState) (base : s.getReg .x28 = 0x80438)
    (counter : s.getReg .x6 = s.getMem 0x80438) (a : Word) :
    (state s).getMem a = if a=0x80438 then s.getMem 0x80438+1 else s.getMem a := by
  simp [state,PersistentStepBase.finish,execInstrBr,MachineState.getReg_setReg_ne,
    MachineState.getReg_setReg_eq,base,counter,signExtend12]

theorem reg (s : MachineState) (r : Reg) (ne : r ≠ .x6) : (state s).getReg r = s.getReg r := by
  simp [state,PersistentStepBase.finish,execInstrBr,MachineState.getReg,MachineState.setReg,
    MachineState.setMem,MachineState.setPC,ne]

theorem pc (s : MachineState) : (state s).pc = s.pc-112 := by
  simp [state,PersistentStepBase.finish,execInstrBr,signExtend21,BitVec.add_assoc,BitVec.sub_eq_add_neg]

theorem counter (s : MachineState) (base : s.getReg .x28 = 0x80438) :
    (state s).getReg .x6 = (state s).getMem 0x80438 := by
  simp [state,PersistentStepBase.finish,execInstrBr,MachineState.getReg_setReg_ne,
    MachineState.getReg_setReg_eq,base,signExtend12]

theorem ready (s : MachineState) (base : s.getReg .x28 = 0x80438)
    (counter : s.getReg .x6 = s.getMem 0x80438)
    (current : InplaceInvariant.Current s) : CachedPrepare.Ready (state s) := by
  obtain ⟨h0,h1,h2,h3⟩ := current
  unfold CachedPrepare.Ready
  simp only [mem s base counter]
  simp
  refine ⟨?_,h1,h2,h3⟩
  simpa [BitVec.add_assoc] using congrArg (fun x : Word => x+4294967296) h0

/-- info: 'SigGolfCandidate.Hypertree.StepBaseFinish.ready' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ready
/-- info: 'SigGolfCandidate.Hypertree.StepBaseFinish.counter' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms counter
/-- info: 'SigGolfCandidate.Hypertree.StepBaseFinish.reg' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms reg
end SigGolfCandidate.Hypertree.StepBaseFinish
