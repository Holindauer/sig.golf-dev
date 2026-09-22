import SigGolfCandidate.Hypertree.SecurityGraphSampling
import SigGolfCandidate.Hypertree.SecurityGraphOrder

namespace SigGolfCandidate.Hypertree.SecurityGraphUniform
open SigGolf OracleComp OracleSpec Reference SecurityDerivation SecurityGraph
  SecurityGraphSampling SecurityGraphOrder

noncomputable instance : SampleableType Labels := SampleableType.ofFintype Labels

/-- Resampling every listed coordinate makes its initial value irrelevant. -/
theorem sampleLabels_congr_initial (positions : List Position) (first second : Labels)
    (outside : ∀ position ∉ positions, first position = second position) :
    sampleLabels positions first = sampleLabels positions second := by
  induction positions generalizing first second with
  | nil =>
    have same : first = second := funext fun position => outside position (by simp)
    rw [same]
  | cons position rest ih =>
    simp only [sampleLabels]
    congr 1
    funext answer
    apply ih
    intro other absent
    by_cases same : other = position
    · subst other
      simp
    · simp only [Function.update_of_ne same]
      exact outside other (by simp [same, absent])

/-- Resampling any finite list of coordinates preserves the uniform table law. -/
theorem uniform_resampling (positions : List Position) :
    𝒮[do let labels ← $ᵗ Labels; sampleLabels positions labels] = 𝒮[$ᵗ Labels] := by
  induction positions with
  | nil => simp [sampleLabels]
  | cons position rest ih =>
    calc
      _ = 𝒮[do
        let answer ← $ᵗ BitVec 256
        let labels ← $ᵗ Labels
        sampleLabels rest (Function.update labels position answer)] := by
          exact evalSPMF_bind_bind_swap _ _ _
      _ = 𝒮[do
        let updated ← (do
          let answer ← $ᵗ BitVec 256
          let labels ← $ᵗ Labels
          pure (Function.update labels position answer))
        sampleLabels rest updated] := by simp only [bind_assoc, pure_bind]
      _ = 𝒮[do let labels ← $ᵗ Labels; sampleLabels rest labels] := by
          rw [evalSPMF_bind, evalSPMF_uniformSample_bind_update, evalSPMF_bind]
      _ = _ := ih

/-- The complete graph has independent uniform full-width labels. -/
theorem sampleLabels_complete (initial : Labels) :
    𝒮[sampleLabels positions initial] = 𝒮[$ᵗ Labels] := by
  have independent (other : Labels) : sampleLabels positions other = sampleLabels positions initial :=
    sampleLabels_congr_initial positions other initial (fun position absent =>
      False.elim (absent (positions_complete position)))
  have equal : 𝒮[do let labels ← $ᵗ Labels; sampleLabels positions labels] =
      𝒮[sampleLabels positions initial] := by
    simp_rw [independent]
    apply evalSPMF_ext
    intro output
    rw [probOutput_bind_const]
    simp
  rw [← equal]
  exact uniform_resampling positions

/-- Exact joint law of all canonical labels and the oracle cache, with the actual
reference input at each vertex. This is a distribution identity, not a claim that
the candidate performs uncharged extra hash calls. -/
theorem run_complete_graph (privateAnswers : Slot → BitVec 256) (initial : Labels) :
    𝒮[(simulateQ (randomOracle : QueryImpl HashSpec (StateT (QueryCache HashSpec) ProbComp))
      (readGraph privateAnswers positions initial)).run ∅] =
      𝒮[do
        let labels ← $ᵗ Labels
        return (labels, graphCache privateAnswers positions labels ∅)] := by
  rw [run_readGraph_eq_labels_cache privateAnswers positions positions_nodup positions_ordered initial]
  simp only [evalSPMF_bind]
  rw [sampleLabels_complete]

end SigGolfCandidate.Hypertree.SecurityGraphUniform
