import LeanSphincs.OTS.Evaluate

/-! Reconstruction against an oracle-consistent reference assignment.
The evaluator is the actual OracleComp, interpreted under a total answer function.
Constructing this assignment from randomized key generation and transporting the
theorem through the shared lazy ROM remain explicit integration obligations. -/

open OracleComp OracleSpec

namespace LeanSphincs.OTS

open LeanSphincs.Benchmark

def AgreesOn (known : Values) (vertices : List Vertex) (reference : Vertex → Value) : Prop :=
  ∀ v ∈ vertices, known v = some (reference v)

def Graph.Consistent (g : Graph) (answers : QueryImpl HashSpec Id)
    (reference : Vertex → Value) : Prop :=
  ∀ (i : Fin g.gates.length) (slot : Fin 2), reference (.output i.val slot) =
    (answers ((g.gates.get i).queryInput (fun v => some (reference v)))).extractLsb' (128 * slot.val) 128

theorem Gate.queryInput_eq (g : Gate) (known expected : Values)
    (agree : ∀ v ∈ g.inputs, known v = expected v) :
    g.queryInput known = g.queryInput expected := by
  unfold Gate.queryInput inputValues
  congr 1
  apply List.flatMap_congr
  intro v hv
  rw [agree v hv]

theorem writeOutputs_agrees (g : Graph) (answers : QueryImpl HashSpec Id)
    (reference : Vertex → Value) (consistent : g.Consistent answers reference)
    (known : Values) (vertices : List Vertex) (agree : AgreesOn known vertices reference)
    (i : Fin g.gates.length) :
    AgreesOn (writeOutputs known i.val
      (answers ((g.gates.get i).queryInput (fun v => some (reference v)))))
      (.output i.val 0 :: .output i.val 1 :: vertices) reference := by
  intro v hv
  simp only [List.mem_cons] at hv
  rcases hv with rfl | rfl | hv
  · simp [writeOutputs, consistent i 0]
  · simp [writeOutputs, consistent i 1]
  · cases v with
    | source j => exact agree _ hv
    | output producer slot =>
      by_cases heq : producer = i.val
      · subst producer
        simp [writeOutputs, consistent i slot]
      · simpa [writeOutputs, heq] using agree (.output producer slot) hv

/-- A valid schedule reconstructs the reference root when disclosed values are
correct and every gate of the reference obeys the same oracle answer function.
Neither collision resistance nor unforgeability is assumed or concluded. -/
theorem Graph.reconstructs_reference (g : Graph) (answers : QueryImpl HashSpec Id)
    (reference : Vertex → Value) (consistent : g.Consistent answers reference)
    (known : Values) (vertices : List Vertex) (schedule : List (Fin g.gates.length))
    (agree : AgreesOn known vertices reference) (valid : g.Reconstructs vertices schedule) :
    evalWithAnswerFn answers (g.evaluate known schedule) = some (reference g.root) := by
  induction schedule generalizing known vertices with
  | nil => exact agree g.root valid
  | cons i rest ih =>
    obtain ⟨inputs, restValid⟩ := valid
    have inputsAgree : ∀ v ∈ (g.gates.get i).inputs, known v = some (reference v) :=
      fun v hv => agree v (inputs v hv)
    have present : ∀ v ∈ (g.gates.get i).inputs, (known v).isSome := by
      intro v hv
      rw [inputsAgree v hv]
      rfl
    have queryEq := Gate.queryInput_eq (g.gates.get i) known (fun v => some (reference v)) inputsAgree
    have gateResult : evalWithAnswerFn answers ((g.gates.get i).evaluate known) =
        some (answers ((g.gates.get i).queryInput (fun v => some (reference v)))) := by
      rw [Gate.evaluate, if_pos present, evalWithAnswerFn_bind]
      change some (answers ((g.gates.get i).queryInput known)) = _
      rw [queryEq]
    simp only [Graph.evaluate, evalWithAnswerFn_bind, gateResult]
    exact ih _ _ (writeOutputs_agrees g answers reference consistent known vertices agree i) restValid

end LeanSphincs.OTS
