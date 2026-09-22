import LeanSphincs
import Lean

open Lean

/- The protected definitions and their entire axiom closures are audited,
including all computational definitions on which the claim depends. -/
open Elab.Command in
run_cmd liftCoreM do
  let env ← getEnv
  let whitelist : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for (name, ci) in env.constants.toList do
    if (`LeanSphincs.Benchmark).isPrefixOf name then
      if ci.isAxiom then
        throwError "protected axiom declaration: {name}"
      let axioms ← collectAxioms name
      for ax in axioms do
        unless whitelist.contains ax do
          throwError "{name} depends on forbidden axiom {ax}"
  IO.println "Protected declarations: standard axioms only."

set_option pp.universes false in
/-- info: 'LeanSphincs.Benchmark.MeetsFloor.sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanSphincs.Benchmark.MeetsFloor.sound
