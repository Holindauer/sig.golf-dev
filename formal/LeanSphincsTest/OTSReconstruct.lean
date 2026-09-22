import LeanSphincs.OTS.Reconstruct

open OracleComp OracleSpec LeanSphincs.OTS LeanSphincs.Benchmark

private def graph : Graph :=
  ⟨2, [⟨1, [.source 0]⟩, ⟨2, [.output 0 0, .output 0 1, .source 1]⟩], .output 1 0⟩
private def answers : QueryImpl HashSpec Id := QueryImpl.ofFn (fun _ => 0)
private def reference : Vertex → Value := fun _ => 0
private def known : Values
  | .source _ => some 0
  | .output _ _ => none
private def disclosed : List Vertex := [.source 0, .source 1]
private def schedule : List (Fin graph.gates.length) := [⟨0, by decide⟩, ⟨1, by decide⟩]

private theorem consistent : graph.Consistent answers reference := by
  unfold Graph.Consistent
  decide

example : graph.WellFormed := by decide
example : graph.Reconstructs disclosed schedule := by decide
example : ¬ graph.Reconstructs disclosed schedule.reverse := by decide

/-- The actual oracle computation, not a separate mock graph evaluator. -/
example : evalWithAnswerFn answers (graph.evaluate known schedule) = some 0 :=
  graph.reconstructs_reference answers reference consistent known disclosed schedule
    (by unfold AgreesOn; decide) (by decide)

/-- An inconsistent claimed reference does not meet the correctness premise. -/
example : ¬ graph.Consistent answers (fun _ => 1) := by
  unfold Graph.Consistent
  decide

example : ¬ AgreesOn (fun _ => some 1) disclosed reference := by
  unfold AgreesOn
  decide
