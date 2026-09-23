import SigGolfCandidate.Hypertree.InplacePrepare
import SigGolfCandidate.Hypertree.InplaceFinish
import SigGolfCandidate.Hypertree.InplaceRestore
import SigGolfCandidate.Hypertree.InplaceCheck
import SigGolfCandidate.Hypertree.InplaceHash
namespace SigGolfCandidate.Hypertree.InplaceInvariant
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
    (ready : CachedPrepare.Ready s) : Current (InplacePrepare.state s) := by
  obtain ⟨h0,h1,h2,h3⟩ := ready
  unfold Current
  simp only [InplacePrepare.mem s base, constant]
  simpa using And.intro h0 (And.intro h1 (And.intro h2 h3))

theorem finish_mem (s : MachineState) (base : s.getReg .x28 = 0x80018) (a : Word) :
    (InplaceFinish.state s).getMem a =
      if a = 0x80438 then s.getMem 0x80438 + 1 else s.getMem a := InplaceFinish.mem s base a

theorem finish_ready (s : MachineState) (base : s.getReg .x28 = 0x80018)
    (current : Current s) : CachedPrepare.Ready (InplaceFinish.state s) := by
  obtain ⟨h0,h1,h2,h3⟩ := current
  unfold CachedPrepare.Ready
  simp only [finish_mem s base]
  simp
  refine ⟨?_,h1,h2,h3⟩
  simpa [BitVec.add_assoc] using congrArg (fun x : Word => x + 4294967296) h0

theorem check_ready (s : MachineState) (ready : CachedPrepare.Ready s) :
    CachedPrepare.Ready (InplaceCheck.shortCheck s) := by
  simpa only [CachedPrepare.Ready, InplaceCheck.short_mem] using ready

theorem full_prepare_current (s : MachineState) : Current (KeygenChainHeader.state s) := by
  simp [Current, KeygenChainHeader.mem]

theorem hash_current (s : MachineState) (answer : BitVec 256)
    (dst : s.getReg .x12 = 0x80020) (current : Current s) :
    Current (writeHash s answer) := by
  have frame (a : Word) (outside : ∀ i : Fin 4, a ≠ Signing.wordAddress 0x80020 i.val) :=
    InplaceHash.frame s answer dst a outside
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

/-- info: 'SigGolfCandidate.Hypertree.InplaceInvariant.prepare_current' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms prepare_current
/-- info: 'SigGolfCandidate.Hypertree.InplaceInvariant.finish_mem' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms finish_mem
/-- info: 'SigGolfCandidate.Hypertree.InplaceInvariant.finish_ready' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms finish_ready
/-- info: 'SigGolfCandidate.Hypertree.InplaceInvariant.check_ready' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms check_ready
/-- info: 'SigGolfCandidate.Hypertree.InplaceInvariant.full_prepare_current' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms full_prepare_current
/-- info: 'SigGolfCandidate.Hypertree.InplaceInvariant.hash_current' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms hash_current
theorem restore_words (s : MachineState) (base : s.getReg .x28 = 0x80438) (i : Fin 2) :
    (InplaceRestore.state s).getMem (Signing.wordAddress 0x80510 i.val) =
      s.getMem (Signing.wordAddress 0x80020 i.val) := by
  fin_cases i <;> simp [Signing.wordAddress, InplaceRestore.mem s base]

/-- info: 'SigGolfCandidate.Hypertree.InplaceInvariant.restore_words' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms restore_words
end SigGolfCandidate.Hypertree.InplaceInvariant
