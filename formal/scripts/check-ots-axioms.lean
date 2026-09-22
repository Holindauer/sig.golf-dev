import LeanSphincs.OTS.Score
import LeanSphincs.OTS.Graph
import LeanSphincs.OTS.Evaluate
import LeanSphincs.OTS.Reconstruct
import LeanSphincs.OTS.Failure
import Lean

open Lean Elab.Command in
run_cmd liftCoreM do
  let env ← getEnv
  let whitelist : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for (name, ci) in env.constants.toList do
    if (`LeanSphincs.OTS).isPrefixOf name then
      if ci.isAxiom then
        throwError "OTS axiom declaration: {name}"
      for ax in (← collectAxioms name) do
        unless whitelist.contains ax do
          throwError "{name} depends on forbidden axiom {ax}"
  IO.println "Experimental OTS declarations: standard axioms only; no security theorem claimed."
