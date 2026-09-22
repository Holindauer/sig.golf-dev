import LeanSphincs.OTS.Graph

open LeanSphincs.OTS

private def gate : Gate := ⟨0, [.source 0]⟩
private def graph : Graph := ⟨1, [gate], .output 0 0⟩

example : graph.WellFormed := by decide
example : graph.Reconstructs [.source 0] [⟨0, by decide⟩] := by decide
example : ¬ graph.Reconstructs [] [⟨0, by decide⟩] := by decide
example : ¬ graph.Reconstructs [.source 0] [] := by decide
example : gate.cost = 1 := by decide
example : ({ gate with inputs := List.replicate 4 (.source 0) } : Gate).cost = 2 := by decide
example : graph.keygenCost = 1 := by decide

private def cyclic : Graph := ⟨0, [⟨0, [.output 0 0]⟩], .output 0 0⟩
example : ¬ cyclic.WellFormed := by decide
