import SigGolfCandidate.Hypertree.SecurityGraphCausality

namespace SigGolfCandidate.Hypertree.SecurityGraphSampling
open SigGolf OracleComp OracleSpec Reference SecurityDerivation SecurityGraph SecurityGraphCausality

/-- Independent full outputs indexed by the canonical graph vertices. -/
noncomputable def sampleLabels : List Position → Labels → ProbComp Labels
  | [], labels => pure labels
  | position :: rest, labels => do
      let answer ← $ᵗ BitVec 256
      sampleLabels rest (Function.update labels position answer)

/-- Cache population using the completed canonical labels. -/
def graphCache (privateAnswers : Slot → BitVec 256) :
    List Position → Labels → QueryCache HashSpec → QueryCache HashSpec
  | [], _, cache => cache
  | position :: rest, labels, cache =>
      graphCache privateAnswers rest labels
        (cache.cacheQuery (position.input privateAnswers labels) (labels position))

theorem sampleLabels_unchanged (positions : List Position) (labels output : Labels)
    (member : output ∈ support (sampleLabels positions labels))
    (position : Position) (absent : position ∉ positions) : output position = labels position := by
  induction positions generalizing labels with
  | nil =>
    have equal : output = labels := by simpa [sampleLabels] using member
    exact congrArg (fun values : Labels => values position) equal
  | cons next rest ih =>
    rw [sampleLabels, mem_support_bind_iff] at member
    obtain ⟨answer, _, member⟩ := member
    have notNext : position ≠ next := fun same => absent (by simp [same])
    have notRest : position ∉ rest := fun h => absent (List.mem_cons_of_mem _ h)
    rw [ih _ member notRest, Function.update_of_ne notNext]

theorem sampleLabels_input_preserved (privateAnswers : Slot → BitVec 256) (position : Position)
    (positions : List Position) (later : ∀ next ∈ positions, rank position ≤ rank next)
    (labels output : Labels) (member : output ∈ support (sampleLabels positions labels)) :
    position.input privateAnswers output = position.input privateAnswers labels := by
  unfold Position.input
  congr 1
  apply payload_congr
  intro child earlier
  apply sampleLabels_unchanged positions labels output member child
  intro occurs
  have bound := later child occurs
  omega

/-- The sampled graph's public cache is exactly a deterministic function of the
independent final labels. Causality prevents later label draws from changing any
already-registered input. This is a joint distribution statement, retaining cache state. -/
theorem sampleGraph_eq_labels_cache (privateAnswers : Slot → BitVec 256)
    (positions : List Position) (distinct : positions.Nodup)
    (ordered : positions.Pairwise (fun first second => rank first ≤ rank second))
    (labels : Labels) (cache : QueryCache HashSpec) :
    𝒮[sampleGraph privateAnswers positions labels cache] =
      𝒮[do
        let final ← sampleLabels positions labels
        return (final, graphCache privateAnswers positions final cache)] := by
  induction positions generalizing labels cache with
  | nil => simp [sampleGraph, sampleLabels, graphCache]
  | cons first rest ih =>
    obtain ⟨notRest, restDistinct⟩ := List.nodup_cons.mp distinct
    obtain ⟨firstBefore, restOrdered⟩ := List.pairwise_cons.mp ordered
    calc
      _ = 𝒮[do
        let answer ← $ᵗ BitVec 256
        let final ← sampleLabels rest (Function.update labels first answer)
        return (final, graphCache privateAnswers rest final
          (cache.cacheQuery (first.input privateAnswers labels) answer))] := by
          simp only [sampleGraph]
          apply evalSPMF_bind_congr
          intro answer _
          exact ih restDistinct restOrdered _ _
      _ = _ := by
        simp only [sampleLabels, bind_assoc]
        apply evalSPMF_bind_congr
        intro answer _
        apply evalSPMF_bind_congr
        intro final member
        have sameInput : first.input privateAnswers final = first.input privateAnswers labels := by
          rw [sampleLabels_input_preserved privateAnswers first rest firstBefore _ final member,
            input_update_of_rank privateAnswers first first le_rfl]
        have sameLabel : final first = answer := by
          rw [sampleLabels_unchanged rest _ final member first notRest, Function.update_self]
        simp only [graphCache]
        rw [sameInput, sameLabel]

/-- Actual lazy graph evaluation is equivalent to sampling its independent labels
first and populating the exact reference cache from them. -/
theorem run_readGraph_eq_labels_cache (privateAnswers : Slot → BitVec 256)
    (positions : List Position) (distinct : positions.Nodup)
    (ordered : positions.Pairwise (fun first second => rank first ≤ rank second)) (labels : Labels) :
    𝒮[(simulateQ (randomOracle : QueryImpl HashSpec (StateT (QueryCache HashSpec) ProbComp))
      (readGraph privateAnswers positions labels)).run ∅] =
      𝒮[do
        let final ← sampleLabels positions labels
        return (final, graphCache privateAnswers positions final ∅)] := by
  rw [run_readGraph_empty privateAnswers positions distinct labels]
  exact sampleGraph_eq_labels_cache privateAnswers positions distinct ordered labels ∅

end SigGolfCandidate.Hypertree.SecurityGraphSampling
