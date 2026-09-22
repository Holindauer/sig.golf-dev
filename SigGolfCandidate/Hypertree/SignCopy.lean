import SigGolfCandidate.Hypertree.KeygenBlocks

namespace SigGolfCandidate.Hypertree.Signing
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 Keygen

/-- Aligned word positions in a byte buffer. -/
def wordAddress (base i : Nat) : Word := BitVec.ofNat 64 (base + 8 * i)

/-- Copied prefix plus a complete frame condition for every other memory word. -/
def CopyContent (source destination total n : Nat) (original current : MachineState) : Prop :=
  (∀ a, (∀ j, j < total - n → a ≠ wordAddress destination j) →
    current.getMem a = original.getMem a) ∧
  (∀ i, i < total - n → current.getMem (wordAddress destination i) =
    original.getMem (wordAddress source i))

theorem wordAddress_injective (base total : Nat) (bound : base + 8 * total ≤ MEMORY_BYTES)
    (i j : Nat) (hi : i < total) (hj : j < total) (ne : i ≠ j) :
    wordAddress base i ≠ wordAddress base j := by
  intro eq
  have values := congrArg BitVec.toNat eq
  have hbi : base + 8 * i < 2 ^ 64 := by simp only [MEMORY_BYTES] at bound; omega
  have hbj : base + 8 * j < 2 ^ 64 := by simp only [MEMORY_BYTES] at bound; omega
  change (base + 8 * i) % 2 ^ 64 = (base + 8 * j) % 2 ^ 64 at values
  rw [Nat.mod_eq_of_lt hbi, Nat.mod_eq_of_lt hbj] at values
  omega

/-- Disjoint byte intervals give the nonaliasing condition used by the copy proof. -/
theorem wordAddress_disjoint (source destination total : Nat)
    (srcbound : source + 8 * total ≤ MEMORY_BYTES)
    (dstbound : destination + 8 * total ≤ MEMORY_BYTES)
    (separate : source + 8 * total ≤ destination ∨ destination + 8 * total ≤ source)
    (i j : Nat) (hi : i < total) (hj : j < total) :
    wordAddress source i ≠ wordAddress destination j := by
  intro eq
  have values := congrArg BitVec.toNat eq
  have hsi : source + 8 * i < 2 ^ 64 := by simp only [MEMORY_BYTES] at srcbound; omega
  have hdj : destination + 8 * j < 2 ^ 64 := by simp only [MEMORY_BYTES] at dstbound; omega
  change (source + 8 * i) % 2 ^ 64 = (destination + 8 * j) % 2 ^ 64 at values
  rw [Nat.mod_eq_of_lt hsi, Nat.mod_eq_of_lt hdj] at values
  omega

theorem copy_content_next (p : Word) (source destination total n : Nat)
    (original s : MachineState) (inv : CopyInvariant p source destination total (n + 1) s)
    (content : CopyContent source destination total (n + 1) original s)
    (dstbound : destination + 8 * total ≤ MEMORY_BYTES)
    (disjoint : ∀ i j, i < total → j < total →
      wordAddress source i ≠ wordAddress destination j) :
    CopyContent source destination total n original (Expansion.loopNext s) := by
  obtain ⟨hn, _, _, src, dst, _⟩ := inv
  have current : total - (n + 1) < total := by omega
  change s.getReg .x6 = wordAddress source (total - (n + 1)) at src
  change s.getReg .x7 = wordAddress destination (total - (n + 1)) at dst
  constructor
  · intro a outside
    rw [Expansion.loop_next_mem, dst, if_neg (outside _ (by omega))]
    exact content.1 a (fun j hj => outside j (by omega))
  · intro i hi
    have hib : i < total := by omega
    by_cases eq : i = total - (n + 1)
    · subst i
      rw [Expansion.loop_next_mem, dst, src, if_pos rfl]
      exact content.1 _ (fun j hj => disjoint _ j current (by omega))
    · rw [Expansion.loop_next_mem, dst,
        if_neg (wordAddress_injective destination total dstbound i _ hib current eq)]
      exact content.2 i (by omega)

/-- The generated copy loop has both its actual execution derivation and its precise
memory effect. It is independent of the particular image, buffer sizes, and contents. -/
theorem copy_loop_content (image : Image) (p : Word) (code : CopyCode image p)
    (source destination total n : Nat) (original s : MachineState)
    (inv : CopyInvariant p source destination total n s)
    (content : CopyContent source destination total n original s)
    (srcbound : source + 8 * total ≤ MEMORY_BYTES)
    (dstbound : destination + 8 * total ≤ MEMORY_BYTES)
    (srcalign : source % 8 = 0) (dstalign : destination % 8 = 0)
    (disjoint : ∀ i j, i < total → j < total →
      wordAddress source i ≠ wordAddress destination j) :
    ∃ final, OrdinarySteps image s (6 * n) final ∧
      CopyInvariant p source destination total 0 final ∧
      CopyContent source destination total 0 original final := by
  induction n generalizing s with
  | zero => exact ⟨s, OrdinarySteps.refl _, inv, content⟩
  | succ n ih =>
    have access := copy_accesses p source destination total n s inv srcbound dstbound srcalign dstalign
    have block := copy_block image p code s (by simpa using inv.2.2.1) access.1 access.2
    obtain ⟨final, tail, done, output⟩ := ih (Expansion.loopNext s)
      (copy_invariant_next p source destination total n s inv)
      (copy_content_next p source destination total n original s inv content dstbound disjoint)
    refine ⟨final, ?_, done, output⟩
    simpa only [Nat.mul_add, Nat.mul_one] using ordinary_trans image s _ final 6 (6 * n) block tail

/-- Entry-to-exit copy correctness for disjoint buffers, including the frame condition. -/
theorem copy_all (image : Image) (p : Word) (code : CopyCode image p)
    (source destination total : Nat) (s : MachineState)
    (inv : CopyInvariant p source destination total total s)
    (srcbound : source + 8 * total ≤ MEMORY_BYTES)
    (dstbound : destination + 8 * total ≤ MEMORY_BYTES)
    (srcalign : source % 8 = 0) (dstalign : destination % 8 = 0)
    (separate : source + 8 * total ≤ destination ∨ destination + 8 * total ≤ source) :
    ∃ final, OrdinarySteps image s (6 * total) final ∧
      CopyInvariant p source destination total 0 final ∧
      (∀ i, i < total → final.getMem (wordAddress destination i) = s.getMem (wordAddress source i)) ∧
      (∀ a, (∀ i, i < total → a ≠ wordAddress destination i) → final.getMem a = s.getMem a) := by
  have initial : CopyContent source destination total total s s := by
    constructor
    · intro _ _; rfl
    · intro i hi; omega
  obtain ⟨final, trace, done, output⟩ := copy_loop_content image p code source destination total total s s
    inv initial srcbound dstbound srcalign dstalign
    (wordAddress_disjoint source destination total srcbound dstbound separate)
  exact ⟨final, trace, done, by simpa using output.2, by simpa using output.1⟩

/-- info: 'SigGolfCandidate.Hypertree.Signing.copy_all' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms copy_all

end SigGolfCandidate.Hypertree.Signing
