import SigGolfCandidate.Hypertree.PreludeDerivation
import SigGolfCandidate.Hypertree.KeygenCopyFrame
namespace SigGolfCandidate.Hypertree.Signing.Prelude
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 Keygen
set_option maxRecDepth 4096

def rootCopySetup (s : MachineState) : MachineState :=
  let s := execInstrBr s (.LUI .x6 0x80)
  let s := execInstrBr s (.ADDI .x6 .x6 0x500)
  let s := execInstrBr s (.ADDI .x7 .x0 0x40)
  execInstrBr s (.ADDI .x10 .x0 2)

theorem rootCopy_setup (s : MachineState) (pc : s.pc = 0x1cac) :
    OrdinarySteps signPrelude s 4 (rootCopySetup s) := by
  let s1 := execInstrBr s (.LUI .x6 0x80)
  let s2 := execInstrBr s1 (.ADDI .x6 .x6 0x500)
  let s3 := execInstrBr s2 (.ADDI .x7 .x0 0x40)
  apply OrdinarySteps.step s s1 _ (.base (.LUI .x6 0x80)) 3
  · rw [fetch_at, pc]; decide
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.ADDI .x6 .x6 0x500)) 2
  · have hp : s1.pc = 0x1cb0 := by simp [s1, execInstrBr, pc]
    rw [fetch_at, hp]; decide
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.ADDI .x7 .x0 0x40)) 1
  · have hp : s2.pc = 0x1cb4 := by simp [s1, s2, execInstrBr, pc]
    rw [fetch_at, hp]; decide
  · rfl
  apply OrdinarySteps.step s3 (rootCopySetup s) _ (.base (.ADDI .x10 .x0 2)) 0
  · have hp : s3.pc = 0x1cb8 := by simp [s1, s2, s3, execInstrBr, pc]
    rw [fetch_at, hp]; decide
  · rfl
  exact OrdinarySteps.refl _

theorem root_copy (s : MachineState) (pc : s.pc = 0x1cac) :
    ∃ final, OrdinarySteps signPrelude s 16 final ∧ final.pc = 0x1cd4 ∧
      (∀ i : Fin 2, final.getMem (wordAddress 0x40 i.val) = s.getMem (wordAddress 0x80500 i.val)) ∧
      final.getReg .x1 = s.getReg .x1 ∧ final.getReg .x2 = s.getReg .x2 ∧
      (∀ a, a ≠ 0x40 → a ≠ 0x48 → final.getMem a = s.getMem a) := by
  have inv : CopyInvariant 0x1cbc 0x80500 0x40 2 2 (rootCopySetup s) := by
    simp [CopyInvariant, rootCopySetup, execInstrBr, pc, signExtend12,
      MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  obtain ⟨final, steps, done, content, frame, ra, sp⟩ :=
    copy_all_frame signPrelude 0x1cbc (by decide) 0x80500 0x40 2 (rootCopySetup s) inv
      (by decide) (by decide) (by decide) (by decide) (by decide)
  refine ⟨final, ordinary_trans signPrelude s _ _ 4 12 (rootCopy_setup s pc) steps, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [CopyInvariant] using done.2.2.1
  · intro i
    rw [content i.val i.isLt]
    simp [rootCopySetup, execInstrBr]
  · simpa [rootCopySetup, execInstrBr, MachineState.getReg_setReg_ne] using ra
  · simpa [rootCopySetup, execInstrBr, MachineState.getReg_setReg_ne] using sp
  · intro a h0 h1
    rw [frame]
    · simp [rootCopySetup, execInstrBr]
    · intro i hi
      interval_cases i <;> simpa [wordAddress] using (by assumption : a ≠ _)

/-- info: 'SigGolfCandidate.Hypertree.Signing.Prelude.root_copy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms root_copy
end SigGolfCandidate.Hypertree.Signing.Prelude
