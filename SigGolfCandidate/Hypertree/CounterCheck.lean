import SigGolfCandidate.Hypertree.RegisterCounter
namespace SigGolfCandidate.Hypertree.CounterCheck
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 Keygen
abbrev state := RegisterCounter.check
abbrev Code := RegisterCounter.CheckCode
abbrev block := RegisterCounter.check_block

theorem mem (s : MachineState) (a : Word) : (state s).getMem a = s.getMem a := by
  simp [state,RegisterCounter.check,execInstrBr,MachineState.setReg,MachineState.setPC,MachineState.getMem]
  split_ifs <;> rfl

theorem reg (s : MachineState) (r : Reg) (ne : r ≠ .x7) : (state s).getReg r = s.getReg r := by
  simp [state,RegisterCounter.check,execInstrBr,MachineState.setReg,MachineState.setPC,MachineState.getReg]
  split_ifs <;> simp_all

theorem pc (s : MachineState) (counter : s.getReg .x6 = s.getMem 0x80438) :
    (state s).pc = if s.getMem 0x80438 = 7 then s.pc+132 else s.pc+8 := by
  simp [state,RegisterCounter.check,execInstrBr,MachineState.getReg_setReg_ne,
    MachineState.getReg_setReg_eq,signExtend12,signExtend13,counter,BitVec.add_assoc]

theorem counter (s : MachineState) (h : s.getReg .x6 = s.getMem 0x80438) :
    (state s).getReg .x6 = (state s).getMem 0x80438 := by
  rw [reg s .x6 (by decide),mem]; exact h

theorem ready (s : MachineState) (h : CachedPrepare.Ready s) : CachedPrepare.Ready (state s) := by
  simpa only [CachedPrepare.Ready,mem] using h

abbrev shortCheck := state
abbrev short_mem := mem

theorem short_base (s : MachineState) : (state s).getReg .x28 = s.getReg .x28 := reg s .x28 (by decide)
theorem short_stack (s : MachineState) : (state s).getReg .x1 = s.getReg .x1 ∧ (state s).getReg .x2 = s.getReg .x2 :=
  ⟨reg s .x1 (by decide),reg s .x2 (by decide)⟩

/-- info: 'SigGolfCandidate.Hypertree.CounterCheck.pc' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms pc
/-- info: 'SigGolfCandidate.Hypertree.CounterCheck.ready' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ready
end SigGolfCandidate.Hypertree.CounterCheck
