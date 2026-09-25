import SigGolfCandidate.Hypertree.SecurityGraphCausality
import Mathlib.Data.List.Sort

namespace SigGolfCandidate.Hypertree.SecurityGraphOrder
open SigGolf Reference SecurityDerivation SecurityGraph SecurityGraphCausality

private def chainCoordinates (address : ChainAddress) : Fin 160 × BitVec 192 × Bool × Chain :=
  (address.level, address.tree, address.side, address.chain)

private theorem chainCoordinates_injective : Function.Injective chainCoordinates := by
  intro first second same
  cases first
  cases second
  simp only [chainCoordinates, Prod.mk.injEq] at same
  rcases same with ⟨rfl, rfl, rfl, rfl⟩
  rfl

instance : Finite ChainAddress := Finite.of_injective chainCoordinates chainCoordinates_injective

private def positionCoordinates : Position →
    (ChainAddress × Fin 7) ⊕ ((Fin 160 × BitVec 192 × Bool) ⊕ (Fin 160 × BitVec 192))
  | .chain address step => .inl (address, step)
  | .leaf level tree side => .inr (.inl (level, tree, side))
  | .node level tree => .inr (.inr (level, tree))

private theorem positionCoordinates_injective : Function.Injective positionCoordinates := by
  intro first second same
  cases first <;> cases second <;> simp_all [positionCoordinates]

instance : Finite Position := Finite.of_injective positionCoordinates positionCoordinates_injective
noncomputable instance : Fintype Position := Fintype.ofFinite Position

/-- A complete topological order, used symbolically. The enormous finite graph is
never enumerated or evaluated by the kernel. -/
noncomputable def positions : List Position :=
  (Finset.univ : Finset Position).toList.mergeSort (fun first second => decide (rank first ≤ rank second))

theorem positions_perm : positions.Perm (Finset.univ : Finset Position).toList :=
  List.mergeSort_perm _ _

theorem positions_nodup : positions.Nodup := positions_perm.nodup_iff.mpr (Finset.nodup_toList _)

theorem positions_complete (position : Position) : position ∈ positions := by
  rw [positions_perm.mem_iff]
  simp

theorem positions_ordered : positions.Pairwise (fun first second => rank first ≤ rank second) := by
  simpa only [positions, decide_eq_true_eq] using
    (List.pairwise_mergeSort (le := fun first second : Position => decide (rank first ≤ rank second))
      (fun a b c hab hbc => by simp only [decide_eq_true_eq] at *; omega)
      (fun a b => by simp only [Bool.or_eq_true, decide_eq_true_eq]; omega)
      (Finset.univ : Finset Position).toList)

/-- Complete reference graph evaluation satisfies every canonical vertex equation. -/
theorem read_complete_consistent (hash : Hash) (privateAnswers : Slot → BitVec 256) (labels : Labels)
    (position : Position) :
    hash (position.input privateAnswers (evalWithAnswerFn hash
      (readGraph privateAnswers positions labels))) =
      evalWithAnswerFn hash (readGraph privateAnswers positions labels) position :=
  readGraph_consistent hash privateAnswers positions positions_nodup positions_ordered labels position
    (positions_complete position)

end SigGolfCandidate.Hypertree.SecurityGraphOrder
