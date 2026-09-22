import SigGolfCandidate.Hypertree.SignCopy

namespace SigGolfCandidate.Hypertree.Keygen
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 OracleComp

/-- Fixed-length ordinary traces of the protected interpreter have a unique final state. -/
theorem ordinary_deterministic {image : Image} {s t u : MachineState} {n : Nat}
    (first : OrdinarySteps image s n t) (second : OrdinarySteps image s n u) : t = u := by
  induction first generalizing u with
  | refl state => cases second; rfl
  | step state next final instruction steps hf hs tail ih =>
    cases second with
    | step _ other _ otherInstruction _ hf' hs' tail' =>
      have instr_eq := Option.some.inj (hf.symm.trans hf')
      subst otherInstruction
      have next_eq := Option.some.inj (hs.symm.trans hs')
      subst other
      exact ih tail'

theorem copy_next_stack (s : MachineState) :
    (Expansion.loopNext s).getReg .x1 = s.getReg .x1 ∧
    (Expansion.loopNext s).getReg .x2 = s.getReg .x2 := by
  simp [Expansion.loopNext, Expansion.loopBody, execInstrBr, MachineState.getReg_setReg_ne]

theorem copy_loop_stack (image : Image) (p : Word) (code : CopyCode image p)
    (source destination total n : Nat) (s : MachineState)
    (inv : CopyInvariant p source destination total n s)
    (srcbound : source + 8 * total ≤ MEMORY_BYTES)
    (dstbound : destination + 8 * total ≤ MEMORY_BYTES)
    (srcalign : source % 8 = 0) (dstalign : destination % 8 = 0) :
    ∃ final, OrdinarySteps image s (6 * n) final ∧
      final.getReg .x1 = s.getReg .x1 ∧ final.getReg .x2 = s.getReg .x2 := by
  induction n generalizing s with
  | zero => exact ⟨s, OrdinarySteps.refl _, rfl, rfl⟩
  | succ n ih =>
    have access := copy_accesses p source destination total n s inv srcbound dstbound srcalign dstalign
    have block := copy_block image p code s (by simpa using inv.2.2.1) access.1 access.2
    obtain ⟨final, tail, ra, sp⟩ := ih (Expansion.loopNext s)
      (copy_invariant_next p source destination total n s inv)
    refine ⟨final, ?_, ra.trans (copy_next_stack s).1, sp.trans (copy_next_stack s).2⟩
    simpa only [Nat.mul_add, Nat.mul_one] using ordinary_trans image s _ final 6 (6 * n) block tail

/-- The content/frame copy theorem also preserves the call stack and return-address registers. -/
theorem copy_all_frame (image : Image) (p : Word) (code : CopyCode image p)
    (source destination total : Nat) (s : MachineState)
    (inv : CopyInvariant p source destination total total s)
    (srcbound : source + 8 * total ≤ MEMORY_BYTES)
    (dstbound : destination + 8 * total ≤ MEMORY_BYTES)
    (srcalign : source % 8 = 0) (dstalign : destination % 8 = 0)
    (separate : source + 8 * total ≤ destination ∨ destination + 8 * total ≤ source) :
    ∃ final, OrdinarySteps image s (6 * total) final ∧
      CopyInvariant p source destination total 0 final ∧
      (∀ i, i < total → final.getMem (Signing.wordAddress destination i) =
        s.getMem (Signing.wordAddress source i)) ∧
      (∀ a, (∀ i, i < total → a ≠ Signing.wordAddress destination i) → final.getMem a = s.getMem a) ∧
      final.getReg .x1 = s.getReg .x1 ∧ final.getReg .x2 = s.getReg .x2 := by
  obtain ⟨final, trace, done, content, frame⟩ := Signing.copy_all image p code source destination total s
    inv srcbound dstbound srcalign dstalign separate
  obtain ⟨other, trace', ra, sp⟩ := copy_loop_stack image p code source destination total total s inv
    srcbound dstbound srcalign dstalign
  have eq := ordinary_deterministic trace trace'
  subst other
  exact ⟨final, trace, done, content, frame, ra, sp⟩

end SigGolfCandidate.Hypertree.Keygen
