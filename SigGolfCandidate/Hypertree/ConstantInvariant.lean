import SigGolfCandidate.Hypertree.ConstantPrepare
import SigGolfCandidate.Hypertree.ConstantFinish
import SigGolfCandidate.Hypertree.ConstantCheck
namespace SigGolfCandidate.Hypertree.ConstantInvariant
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 Keygen
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

/-- The input buffer contains the domain metadata for the current step. -/
def Current (s : MachineState) : Prop :=
  s.getMem 0x80000 =
    2 + (s.getMem 0x80400 <<< 8) + (s.getMem 0x80428 <<< 16) +
      (s.getMem 0x80430 <<< 24) + (s.getMem 0x80438 <<< 32) ∧
  s.getMem 0x80008 = s.getMem 0x80408 ∧
  s.getMem 0x80010 = s.getMem 0x80410 ∧
  s.getMem 0x80018 = s.getMem 0x80418

theorem prepare_current (s : MachineState) (base : s.getReg .x28 = 0x80438) (constant : s.getReg .x13 = 4294967296)
    (ready : CachedPrepare.Ready s) : Current (ConstantPrepare.state s) := by
  obtain ⟨h0,h1,h2,h3⟩ := ready
  unfold Current
  simp only [ConstantPrepare.mem s base constant]
  simpa using And.intro h0 (And.intro h1 (And.intro h2 h3))

theorem finish_mem (s : MachineState) (base : s.getReg .x28 = 0x80018) (a : Word) :
    (ConstantFinish.finish s).getMem a =
      if a = 0x80438 then s.getMem 0x80438 + 1 else
      if a = 0x80518 then s.getMem 0x80308 else
      if a = 0x80510 then s.getMem 0x80300 else s.getMem a := by
  simp [ConstantFinish.finish, execInstrBr, signExtend12, signExtend21, base,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]

theorem finish_ready (s : MachineState) (base : s.getReg .x28 = 0x80018)
    (current : Current s) : CachedPrepare.Ready (ConstantFinish.finish s) := by
  obtain ⟨h0,h1,h2,h3⟩ := current
  unfold CachedPrepare.Ready
  simp only [finish_mem s base]
  simp
  refine ⟨?_,h1,h2,h3⟩
  simpa [BitVec.add_assoc] using congrArg (fun x : Word => x + 4294967296) h0

theorem check_ready (s : MachineState) (ready : CachedPrepare.Ready s) :
    CachedPrepare.Ready (ConstantCheck.shortCheck s) := by
  simpa only [CachedPrepare.Ready, ConstantCheck.short_mem] using ready

theorem full_prepare_current (s : MachineState) : Current (KeygenChainHeader.state s) := by
  simp [Current, KeygenChainHeader.mem]

theorem hash_current (s : MachineState) (answer : BitVec 256)
    (dst : s.getReg .x12 = 0x80300) (current : Current s) :
    Current (writeHash s answer) := by
  have frame (a : Word) (outside : ∀ i : Fin 4, a ≠ Signing.wordAddress 0x80300 i.val) :=
    Signing.hash_answer_frame s answer dst a outside
  unfold Current at *
  have h0 := frame 0x80000 (by intro i; fin_cases i <;> decide)
  have h1 := frame 0x80008 (by intro i; fin_cases i <;> decide)
  have h2 := frame 0x80010 (by intro i; fin_cases i <;> decide)
  have h3 := frame 0x80018 (by intro i; fin_cases i <;> decide)
  have h4 := frame 0x80400 (by intro i; fin_cases i <;> decide)
  have h5 := frame 0x80428 (by intro i; fin_cases i <;> decide)
  have h6 := frame 0x80430 (by intro i; fin_cases i <;> decide)
  have h7 := frame 0x80438 (by intro i; fin_cases i <;> decide)
  have h8 := frame 0x80408 (by intro i; fin_cases i <;> decide)
  have h9 := frame 0x80410 (by intro i; fin_cases i <;> decide)
  have h10 := frame 0x80418 (by intro i; fin_cases i <;> decide)
  rw [h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10]
  exact current

/-- info: 'SigGolfCandidate.Hypertree.ConstantInvariant.prepare_current' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms prepare_current
/-- info: 'SigGolfCandidate.Hypertree.ConstantInvariant.finish_mem' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms finish_mem
/-- info: 'SigGolfCandidate.Hypertree.ConstantInvariant.finish_ready' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms finish_ready
/-- info: 'SigGolfCandidate.Hypertree.ConstantInvariant.check_ready' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms check_ready
/-- info: 'SigGolfCandidate.Hypertree.ConstantInvariant.full_prepare_current' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms full_prepare_current
/-- info: 'SigGolfCandidate.Hypertree.ConstantInvariant.hash_current' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms hash_current
end SigGolfCandidate.Hypertree.ConstantInvariant
