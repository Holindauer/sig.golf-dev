import LeanSphincs.Benchmark.Oracle
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! Experimental dependency graph and structural meter, not signature security.
One call returns two 128-bit vertices from the fixed 256-bit oracle. Using only
one output does not change the charge. Addresses occupy 16 input bytes.
No assertion here connects a graph schedule to a byte-level SigScheme yet. -/

namespace LeanSphincs.OTS

inductive Vertex where
  | source (index : Nat)
  | output (gate : Nat) (slot : Fin 2)
deriving DecidableEq, Repr

structure Gate where
  address : Fin (2^128)
  inputs : List Vertex

def Gate.cost (g : Gate) : Nat :=
  LeanSphincs.Benchmark.hashWeight (List.replicate (16 + 16 * g.inputs.length) 0)

structure Graph where
  sources : Nat
  gates : List Gate
  root : Vertex

def Graph.availableBefore (g : Graph) (index : Nat) : Vertex → Prop
  | .source i => i < g.sources
  | .output producer _ => producer < index

instance (g : Graph) (index : Nat) (v : Vertex) : Decidable (g.availableBefore index v) := by
  cases v <;> unfold Graph.availableBefore <;> infer_instance

def Graph.WellFormed (g : Graph) : Prop :=
  (∀ i : Fin g.gates.length, ∀ v ∈ (g.gates.get i).inputs, g.availableBefore i.val v) ∧
  (∀ i j : Fin g.gates.length,
    (g.gates.get i).address = (g.gates.get j).address → i = j) ∧
  g.availableBefore g.gates.length g.root

instance (g : Graph) : Decidable g.WellFormed := by
  unfold Graph.WellFormed
  infer_instance

/-- A structural reconstruction schedule: each gate's inputs must already be
known. Disclosure minimality, incomparability, serialization and security are
separate obligations, deliberately not inferred by this predicate. -/
def Graph.Reconstructs (g : Graph) : List Vertex → List (Fin g.gates.length) → Prop
  | known, [] => g.root ∈ known
  | known, i :: rest =>
      (∀ v ∈ (g.gates.get i).inputs, v ∈ known) ∧
      g.Reconstructs (.output i.val 0 :: .output i.val 1 :: known) rest

instance (g : Graph) (known : List Vertex) (schedule : List (Fin g.gates.length)) :
    Decidable (g.Reconstructs known schedule) := by
  induction schedule generalizing known with
  | nil => exact inferInstanceAs (Decidable (g.root ∈ known))
  | cons i rest ih =>
    haveI := ih (.output i.val 0 :: .output i.val 1 :: known)
    exact inferInstanceAs (Decidable (_ ∧ _))

def Graph.keygenCost (g : Graph) : Nat :=
  ∑ i : Fin g.gates.length, (g.gates.get i).cost

def Graph.reconstructionCost (g : Graph) (needed : Finset (Fin g.gates.length)) : Nat :=
  ∑ i ∈ needed, (g.gates.get i).cost

/-- A subset of gates, evaluated once each, costs no more than the whole graph.
This does not claim every subset is a valid reconstruction schedule. -/
theorem Graph.reconstructionCost_le (g : Graph) (needed : Finset (Fin g.gates.length)) :
    g.reconstructionCost needed ≤ g.keygenCost := by
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ needed)
  intros
  exact Nat.zero_le _

end LeanSphincs.OTS
