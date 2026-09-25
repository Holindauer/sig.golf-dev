import SigGolfCandidate.Hypertree.SecurityGraphStateSign

namespace SigGolfCandidate.Hypertree.SecurityGraphState
open SigGolf OracleComp OracleSpec Reference SecurityDerivation SecurityGraph
  SecurityGraphIdeal SecurityGraphSigner SecurityGraphOracle SecurityGameHop
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

/-- The stateful split-oracle semantics is exactly the existing game routing:
fix private slots, then interpret public queries with the explicit graph oracle. -/
theorem execute_routing {α : Type} (privateAnswers : PrivateTable) (labels : Labels)
    (program : OracleComp SplitWorld α) :
    simulateQ (implementation privateAnswers labels)
      (fixPrivate privateAnswers (program.liftComp GameWorld)) = execute privateAnswers labels program := by
  unfold fixPrivate execute
  rw [← QueryImpl.simulateQ_compose, OracleComp.liftComp_def, ← QueryImpl.simulateQ_compose]
  congr 1
  funext query
  cases query with
  | inl slot =>
    change simulateQ (implementation privateAnswers labels)
      (privateImplementation privateAnswers (.inr (.inl slot))) = pure (privateAnswers slot)
    simp only [privateImplementation, simulateQ_pure]
  | inr input =>
    simp only [QueryImpl.compose]
    rw [QueryImpl.simulateQ_compose]
    change simulateQ (implementation privateAnswers labels)
      (simulateQ (privateImplementation privateAnswers)
        (liftM (GameWorld.query (.inr (.inr input))))) = _
    simp only [simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map]
    change simulateQ (implementation privateAnswers labels)
      (privateImplementation privateAnswers (.inr (.inr input))) = publicOracle privateAnswers labels input
    simp only [privateImplementation, simulateQ_query, OracleQuery.input_query,
      OracleQuery.cont_query, id_map, implementation, QueryImpl.add_apply_inr]

/-- Key generation through the original game interface preserves every residual cache. -/
theorem routed_keygen_run (privateAnswers : PrivateTable) (labels : Labels) (cache : QueryCache HashSpec) :
    (simulateQ (implementation privateAnswers labels)
      (fixPrivate privateAnswers (SecurityIdealKeygen.keygen.liftComp GameWorld))).run cache =
      pure (truncate (labels (.node 159 0)), cache) := by
  rw [execute_routing, keygen_run]

/-- Honest signing through the original game interface has exactly one residual operation. -/
theorem routed_signCompact_run (privateAnswers : PrivateTable) (labels : Labels)
    (pk : PublicKey) (message : Message) (cache : QueryCache HashSpec) :
    (simulateQ (implementation privateAnswers labels)
      (fixPrivate privateAnswers ((SecurityIdealSign.signCompact pk message).liftComp GameWorld))).run cache =
      (fun result => (signature privateAnswers labels (privateAnswers (.randomizer message))
        (result.1.extractLsb' 0 160), result.2)) <$>
      (randomOracle (spec := HashSpec)
        (SecurityRandomOracle.indexInput pk message (privateAnswers (.randomizer message)))).run cache := by
  rw [execute_routing, signCompact_run]

/-- The actual wire-returning signing interface preserves the same exact residual state. -/
theorem routed_signWire_run (privateAnswers : PrivateTable) (labels : Labels)
    (pk : PublicKey) (message : Message) (cache : QueryCache HashSpec) :
    (simulateQ (implementation privateAnswers labels)
      (fixPrivate privateAnswers ((SecurityExperiment.signWire pk message).liftComp GameWorld))).run cache =
      (fun result => (SecurityExperiment.serialize
        (signature privateAnswers labels (privateAnswers (.randomizer message))
          (result.1.extractLsb' 0 160)), result.2)) <$>
      (randomOracle (spec := HashSpec)
        (SecurityRandomOracle.indexInput pk message (privateAnswers (.randomizer message)))).run cache := by
  rw [execute_routing]
  simp only [SecurityExperiment.signWire, execute, simulateQ_map]
  change (SecurityExperiment.serialize <$>
    execute privateAnswers labels (SecurityIdealSign.signCompact pk message)).run cache = _
  simp only [StateT.run_map, signCompact_run, Functor.map_map]

end SigGolfCandidate.Hypertree.SecurityGraphState
