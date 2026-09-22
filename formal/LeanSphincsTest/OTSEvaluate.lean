import LeanSphincs.OTS.Evaluate

open LeanSphincs.OTS LeanSphincs.Benchmark

private def unary : Gate := ⟨1, [.source 0]⟩
private def fourInputs : Gate := ⟨2, [.source 0, .source 1, .source 2, .source 3]⟩
private def graph : Graph := ⟨4, [unary, fourInputs], .output 1 0⟩
private def known : Values := fun _ => some 7

example : (unary.queryInput known).length = 32 := by decide
example : (fourInputs.queryInput known).length = 80 := by decide
example : hashWeight (fourInputs.queryInput known) = 2 := by decide
example : valueBytes 1 = [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide

example : unary.evaluate (fun _ => none) = pure none := by
  simp [Gate.evaluate, unary]

example : graph.scheduleCost [⟨0, by decide⟩, ⟨1, by decide⟩] = 3 := by decide
example : graph.scheduleCost [⟨1, by decide⟩, ⟨1, by decide⟩] = 4 := by decide

example : HasVerifyCost (graph.evaluate known [⟨0, by decide⟩, ⟨1, by decide⟩]) 3 :=
  graph.evaluate_cost known _

example : writeOutputs known 5 0 (.source 0) = some 7 := by decide
example : writeOutputs known 5 0 (.output 5 0) = some 0 := by decide
example : writeOutputs known 5 0 (.output 5 1) = some 0 := by decide
example : writeOutputs known 5 0 (.output 6 0) = some 7 := by decide

example : writeOutputs known 5 (BitVec.ofNat 256 (2^128)) (.output 5 0) = some 0 := by decide
example : writeOutputs known 5 (BitVec.ofNat 256 (2^128)) (.output 5 1) = some 1 := by decide

example : ∀ left right, unary.queryInput left ≠ fourInputs.queryInput right := by
  intro left right heq
  have impossible := Gate.queryInput_address unary fourInputs left right heq
  have : (1 : Nat) = 2 := congrArg Fin.val impossible
  omega

example : graph.scheduleCost [⟨0, by decide⟩, ⟨1, by decide⟩] ≤ graph.keygenCost :=
  graph.scheduleCost_le_keygen _ (by decide)

example : HasVerifyCost (unary.evaluate (fun _ => none)) 0 := by
  simpa [Gate.evaluate, unary] using (HasVerifyCost.pure (none : Option HashOutput) 0)
