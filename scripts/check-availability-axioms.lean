import LeanSphincsTest.AdaptiveAvailability
import Lean

open Lean Elab.Command in
run_cmd liftCoreM do
  let env ← getEnv
  for (name, ci) in env.constants.toList do
    if (`LeanSphincsTest.AdaptiveAvailability).isPrefixOf name then
      if ci.isAxiom then throwError "fixture axiom: {name}"
      for ax in ← collectAxioms name do
        unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
          throwError "{name} depends on forbidden axiom {ax}"
  IO.println "Adaptive positive and negative fixtures: standard axioms only."
