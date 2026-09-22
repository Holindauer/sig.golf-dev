import SigGolfCandidate.Hypertree.SecurityGraphHidden
import SigGolfCandidate.Hypertree.SecurityGraphReference

namespace SigGolfCandidate.Hypertree.SecurityGraphQuery
open SigGolf OracleComp OracleSpec Reference SecurityDerivation SecurityGraph
  SecurityGraphSampling SecurityGraphOrder SecurityGraphReference
open scoped Classical

/-- Parse only the public address. The selected vertex does not depend on any
private source or graph label, and arbitrary malformed hash inputs are allowed. -/
noncomputable def locate (query : Query) : Option Position :=
  if found : ∃ position : Position, ∃ payload : List Byte, position.address.input payload = query
  then some found.choose else none

theorem locate_address (position : Position) (payload : List Byte) :
    locate (position.address.input payload) = some position := by
  unfold locate
  split
  next found =>
    obtain ⟨otherPayload, equal⟩ := found.choose_spec
    have same : found.choose = position := Position.address_injective (Address.eq_of_input_eq equal)
    rw [same]
  next absent => exact False.elim (absent ⟨position, payload, rfl⟩)

theorem locate_input (privateAnswers : Slot → BitVec 256) (labels : Labels) (position : Position) :
    locate (position.input privateAnswers labels) = some position :=
  locate_address position (position.payload privateAnswers labels)

/-- At most one canonical graph output can be contacted by any arbitrary hash
query. Address selection is independent of the secret labels being guessed. -/
theorem locate_programmed (privateAnswers : Slot → BitVec 256) (labels : Labels)
    (residual : Hash) (query : Query) :
    programmed privateAnswers labels residual query =
      match locate query with
      | none => residual query
      | some position => if query = position.input privateAnswers labels
          then labels position else residual query := by
  unfold programmed
  split
  next found =>
    have located : locate query = some found.choose := by
      exact (congrArg locate found.choose_spec).symm.trans
        (locate_input privateAnswers labels found.choose)
    simp only [located, if_pos found.choose_spec.symm]
  next absent =>
    cases located : locate query with
    | none => rfl
    | some position =>
      have different : query ≠ position.input privateAnswers labels :=
        fun same => absent ⟨position, same.symm⟩
      simp only [if_neg different]

/-- Cache entries outside the finite canonical graph retain their original value. -/
theorem graphCache_outside (privateAnswers : Slot → BitVec 256) (positions : List Position)
    (labels : Labels) (cache : QueryCache HashSpec) (query : Query)
    (outside : ∀ position ∈ positions, query ≠ position.input privateAnswers labels) :
    graphCache privateAnswers positions labels cache query = cache query := by
  induction positions generalizing cache with
  | nil => rfl
  | cons position rest ih =>
    rw [graphCache, ih _ (fun other member => outside other (List.mem_cons_of_mem _ member))]
    exact QueryCache.cacheQuery_of_ne cache _ (outside position (by simp))

/-- A populated canonical graph cache retains the exact full label at every vertex. -/
theorem graphCache_inside (privateAnswers : Slot → BitVec 256) (positions : List Position)
    (labels : Labels) (cache : QueryCache HashSpec) (position : Position)
    (member : position ∈ positions) :
    graphCache privateAnswers positions labels cache (position.input privateAnswers labels) =
      some (labels position) := by
  induction positions generalizing cache with
  | nil => simp at member
  | cons first rest ih =>
    by_cases occurs : position ∈ rest
    · exact ih _ occurs
    · have same : position = first := (List.mem_cons.mp member).resolve_right occurs
      subst first
      rw [graphCache, graphCache_outside]
      · exact QueryCache.cacheQuery_self _ _ _
      · intro other otherMember equal
        have same : position = other := Position.address_injective (Address.eq_of_input_eq equal)
        exact occurs (same ▸ otherMember)

/-- The real post-sampling cache has precisely one possible canonical contact for
an arbitrary input. This exposes the exact cache lookup used by the lazy oracle. -/
theorem complete_cache_lookup (privateAnswers : Slot → BitVec 256) (labels : Labels) (query : Query) :
    graphCache privateAnswers positions labels ∅ query =
      match locate query with
      | none => none
      | some position => if query = position.input privateAnswers labels
          then some (labels position) else none := by
  cases located : locate query with
  | none =>
    apply graphCache_outside
    intro position _ same
    have wrong := locate_input privateAnswers labels position
    rw [← same, located] at wrong
    cases wrong
  | some position =>
    by_cases same : query = position.input privateAnswers labels
    · simp only [if_pos same]
      rw [same]
      exact graphCache_inside privateAnswers positions labels ∅ position (positions_complete position)
    · simp only [if_neg same]
      apply graphCache_outside
      intro other _ equal
      have otherLocated := locate_input privateAnswers labels other
      rw [← equal, located] at otherLocated
      have positionsEqual := Option.some.inj otherLocated
      exact same (positionsEqual ▸ equal)

end SigGolfCandidate.Hypertree.SecurityGraphQuery
