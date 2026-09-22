import SigGolfCandidate.Hypertree.SecurityGraph

namespace SigGolfCandidate.Hypertree.SecurityGraphCausality
open SigGolf OracleComp Reference SecurityDerivation SecurityGraph

/-- Public graph inputs depend only on strictly earlier ranks. -/
def rank : Position → Nat
  | .chain _ step => step.val
  | .leaf _ _ _ => 7
  | .node _ _ => 8

theorem payload_congr (privateAnswers : Slot → BitVec 256) (position : Position)
    (first second : Labels)
    (same : ∀ child, rank child < rank position → first child = second child) :
    position.payload privateAnswers first = position.payload privateAnswers second := by
  cases position with
  | chain address step =>
    simp only [Position.payload]
    split
    · rfl
    · rename_i positive
      rw [same (.chain address ⟨step.val - 1, by omega⟩) (by simp only [rank]; omega)]
  | leaf level tree side =>
    have points : (fun chain : Chain => truncate (first (.chain ⟨level, tree, side, chain⟩ 6))) =
        (fun chain : Chain => truncate (second (.chain ⟨level, tree, side, chain⟩ 6))) := by
      funext chain
      rw [same (.chain ⟨level, tree, side, chain⟩ 6) (by change (6 : Nat) < 7; decide)]
    exact congrArg (fun values : Chain → Digest => (List.ofFn values).flatMap bytes) points
  | node level tree =>
    have leaves (side : Bool) :
        (if level.val = 0 then truncate (first (.chain ⟨level, tree, side, 0⟩ 0))
          else truncate (first (.leaf level tree side))) =
        (if level.val = 0 then truncate (second (.chain ⟨level, tree, side, 0⟩ 0))
          else truncate (second (.leaf level tree side))) := by
      by_cases bottom : level.val = 0
      · simp only [if_pos bottom]
        rw [same (.chain ⟨level, tree, side, 0⟩ 0) (by change (0 : Nat) < 8; decide)]
      · simp only [if_neg bottom]
        rw [same (.leaf level tree side) (by change (7 : Nat) < 8; decide)]
    simp only [Position.payload, leaves]

theorem input_update_of_rank (privateAnswers : Slot → BitVec 256) (position later : Position)
    (ordered : rank position ≤ rank later) (labels : Labels) (answer : BitVec 256) :
    position.input privateAnswers (Function.update labels later answer) = position.input privateAnswers labels := by
  unfold Position.input
  congr 1
  apply payload_congr
  intro child earlier
  have different : child ≠ later := by
    intro equal
    subst child
    omega
  exact Function.update_of_ne different _ _

theorem eval_readGraph_cons (hash : Hash) (privateAnswers : Slot → BitVec 256)
    (position : Position) (rest : List Position) (labels : Labels) :
    evalWithAnswerFn hash (readGraph privateAnswers (position :: rest) labels) =
      evalWithAnswerFn hash (readGraph privateAnswers rest
        (Function.update labels position (hash (position.input privateAnswers labels)))) := rfl

/-- Later graph evaluation preserves every already-computed canonical input. -/
theorem readGraph_input_preserved (hash : Hash) (privateAnswers : Slot → BitVec 256)
    (position : Position) (positions : List Position)
    (later : ∀ next ∈ positions, rank position ≤ rank next) (labels : Labels) :
    position.input privateAnswers (evalWithAnswerFn hash (readGraph privateAnswers positions labels)) =
      position.input privateAnswers labels := by
  induction positions generalizing labels with
  | nil => rfl
  | cons next rest ih =>
    simp only [readGraph, evalWithAnswerFn_bind]
    rw [ih (fun item member => later item (List.mem_cons_of_mem _ member))]
    exact input_update_of_rank privateAnswers position next (later next (by simp)) labels _

/-- A vertex not evaluated by the suffix keeps its previously sampled label. -/
theorem readGraph_label_preserved (hash : Hash) (privateAnswers : Slot → BitVec 256)
    (position : Position) (positions : List Position) (absent : position ∉ positions) (labels : Labels) :
    evalWithAnswerFn hash (readGraph privateAnswers positions labels) position = labels position := by
  induction positions generalizing labels with
  | nil => rfl
  | cons next rest ih =>
    have notNext : position ≠ next := fun equal => absent (by simp [equal])
    have notRest : position ∉ rest := fun member => absent (List.mem_cons_of_mem _ member)
    simp only [readGraph, evalWithAnswerFn_bind]
    rw [ih notRest]
    exact Function.update_of_ne notNext _ _

/-- Evaluation in rank order solves every canonical graph equation for the actual
reference H function. This is the causal consistency needed for graph planting. -/
theorem readGraph_consistent (hash : Hash) (privateAnswers : Slot → BitVec 256)
    (positions : List Position) (distinct : positions.Nodup)
    (ordered : positions.Pairwise (fun first second => rank first ≤ rank second)) (labels : Labels) :
    ∀ position ∈ positions,
      hash (position.input privateAnswers (evalWithAnswerFn hash (readGraph privateAnswers positions labels))) =
        evalWithAnswerFn hash (readGraph privateAnswers positions labels) position := by
  induction positions generalizing labels with
  | nil => simp
  | cons first rest ih =>
    obtain ⟨notRest, restDistinct⟩ := List.nodup_cons.mp distinct
    obtain ⟨firstBefore, restOrdered⟩ := List.pairwise_cons.mp ordered
    intro position member
    simp only [List.mem_cons] at member
    rcases member with equal | member
    · subst position
      rw [eval_readGraph_cons]
      rw [readGraph_input_preserved hash privateAnswers first rest firstBefore,
        readGraph_label_preserved hash privateAnswers first rest notRest,
        input_update_of_rank privateAnswers first first le_rfl, Function.update_self]
    · simp only [readGraph, evalWithAnswerFn_bind]
      exact ih restDistinct restOrdered _ position member

end SigGolfCandidate.Hypertree.SecurityGraphCausality
