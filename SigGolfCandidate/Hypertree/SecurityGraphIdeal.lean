import SigGolfCandidate.Hypertree.SecurityGraphContact
import SigGolfCandidate.Hypertree.SecurityExperiment

namespace SigGolfCandidate.Hypertree.SecurityGraphIdeal
open SigGolf OracleComp OracleSpec SecurityDerivation SecuritySeparation SecurityGameHop
  SecurityGraph SecurityGraphHidden
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

private def slotCoordinates : Slot → ChainAddress ⊕ Message
  | .chain address => .inl address
  | .randomizer message => .inr message

private theorem slotCoordinates_injective : Function.Injective slotCoordinates := by
  intro first second same
  cases first <;> cases second <;> simp_all [slotCoordinates]

instance : Finite Slot := Finite.of_injective slotCoordinates slotCoordinates_injective
noncomputable instance : Fintype Slot := Fintype.ofFinite Slot
abbrev PrivateTable := Slot → BitVec 256
noncomputable instance : SampleableType PrivateTable := SampleableType.ofFintype PrivateTable

def extendPrivate (cache : QueryCache SecretSpec) (answers : PrivateTable) : PrivateTable :=
  fun slot => (cache slot).getD (answers slot)

theorem extendPrivate_update (cache : QueryCache SecretSpec) (answers : PrivateTable)
    (slot : Slot) (fresh : cache slot = none) (answer : BitVec 256) :
    extendPrivate (cache.cacheQuery slot answer) answers =
      extendPrivate cache (Function.update answers slot answer) := by
  funext other
  by_cases same : other = slot
  · subst other; simp [extendPrivate, fresh]
  · simp [extendPrivate, same]

/-- Keep adversary coins and public hash calls intact, while answering the actual
private chain-source and nonce slots from a fixed table. -/
def privateImplementation (answers : PrivateTable) : QueryImpl GameWorld (OracleComp World)
  | .inl coin => liftM (World.query (.inl coin))
  | .inr (.inl slot) => pure (answers slot)
  | .inr (.inr input) => liftM (World.query (.inr input))

def fixPrivate {α : Type} (answers : PrivateTable) (program : OracleComp GameWorld α) :
    OracleComp World α := simulateQ (privateImplementation answers) program

noncomputable def idealObserve {α : Type} (program : OracleComp GameWorld α)
    (secretCache : QueryCache SecretSpec) (publicCache : QueryCache HashSpec) : ProbComp α :=
  (simulateQ idealGameOracle program).run' (secretCache, publicCache)

theorem fixPrivate_query {α : Type} (answers : PrivateTable) (query : GameWorld.Domain)
    (next : GameWorld.Range query → OracleComp GameWorld α) :
    fixPrivate answers (liftM (GameWorld.query query) >>= next) =
      privateImplementation answers query >>= fun answer => fixPrivate answers (next answer) := by
  simp only [fixPrivate, simulateQ_bind, simulateQ_query, OracleQuery.input_query,
    OracleQuery.cont_query, id_map]

theorem idealObserve_query {α : Type} (query : GameWorld.Domain)
    (next : GameWorld.Range query → OracleComp GameWorld α)
    (secretCache : QueryCache SecretSpec) (publicCache : QueryCache HashSpec) :
    idealObserve (liftM (GameWorld.query query) >>= next) secretCache publicCache =
      (do
        let result ← (idealGameOracle query).run (secretCache, publicCache)
        idealObserve (next result.1) result.2.1 result.2.2) := by
  simp only [idealObserve, simulateQ_bind, simulateQ_query, OracleQuery.input_query,
    OracleQuery.cont_query, id_map, StateT.run'_eq, StateT.run_bind, map_bind]

/-- Uniform coordinate resampling remains valid after an arbitrary randomized
continuation, rather than only a deterministic map. -/
theorem uniform_update_bind {α : Type} (slot : Slot) (next : PrivateTable → ProbComp α) :
    𝒮[do
      let answer ← $ᵗ BitVec 256
      let table ← $ᵗ PrivateTable
      next (Function.update table slot answer)] =
      𝒮[do let table ← $ᵗ PrivateTable; next table] := by
  calc
    _ = 𝒮[do
      let updated ← (do
        let answer ← $ᵗ BitVec 256
        let table ← $ᵗ PrivateTable
        pure (Function.update table slot answer))
      next updated] := by simp only [bind_assoc, pure_bind]
    _ = _ := by rw [evalSPMF_bind, evalSPMF_uniformSample_bind_update, evalSPMF_bind]

/-- An exact eager-table description of the actual ideal experiment, while its
public random oracle and adversary coins remain lazy and adaptive. -/
theorem ideal_private_table {α : Type} (program : OracleComp GameWorld α)
    (secretCache : QueryCache SecretSpec) (publicCache : QueryCache HashSpec) :
    𝒮[idealObserve program secretCache publicCache] =
      𝒮[do
        let answers ← $ᵗ PrivateTable
        observe (fixPrivate (extendPrivate secretCache answers) program) publicCache] := by
  induction program using OracleComp.inductionOn generalizing secretCache publicCache with
  | pure value =>
    apply evalSPMF_ext
    intro output
    change Pr[= output | (pure value : ProbComp α)] =
      Pr[= output | (do let _ ← $ᵗ PrivateTable; pure value)]
    rw [probOutput_bind_const]
    simp
  | query_bind query next ih =>
    rw [idealObserve_query]
    simp_rw [fixPrivate_query]
    cases query with
    | inl coin =>
      change 𝒮[(fun answer => (answer, (secretCache, publicCache))) <$>
          (liftM (unifSpec.query coin) : ProbComp _) >>= _] = _
      simp only [map_eq_bind_pure_comp, Function.comp_apply, bind_assoc, pure_bind]
      calc
        _ = 𝒮[do
          let answer ← liftM (unifSpec.query coin)
          let table ← $ᵗ PrivateTable
          observe (fixPrivate (extendPrivate secretCache table) (next answer)) publicCache] := by
            apply evalSPMF_bind_congr
            intro answer _
            exact ih answer secretCache publicCache
        _ = _ := by
          rw [evalSPMF_bind_bind_swap]
          apply evalSPMF_bind_congr
          intro table _
          congr 1
    | inr query =>
      cases query with
      | inr input =>
        change 𝒮[((randomOracle (spec := HashSpec) input).run publicCache >>= fun result =>
          pure (result.1, (secretCache, result.2))) >>= _] = _
        simp only [bind_assoc, pure_bind]
        calc
          _ = 𝒮[do
            let result ← (randomOracle (spec := HashSpec) input).run publicCache
            let table ← $ᵗ PrivateTable
            observe (fixPrivate (extendPrivate secretCache table) (next result.1)) result.2] := by
              apply evalSPMF_bind_congr
              intro result _
              exact ih result.1 secretCache result.2
          _ = _ := by
            rw [evalSPMF_bind_bind_swap]
            apply evalSPMF_bind_congr
            intro table _
            congr 1
            simp [privateImplementation, observe, SecurityCache.implementation]
      | inl slot =>
        change 𝒮[((randomOracle (spec := SecretSpec) slot).run secretCache >>= fun result =>
          pure (result.1, (result.2, publicCache))) >>= _] = _
        simp only [bind_assoc, pure_bind, privateImplementation]
        cases present : secretCache slot with
        | some answer =>
          rw [randomOracle.run_eq, present]
          simp only [pure_bind]
          simpa only [extendPrivate, present, Option.getD_some] using
            ih answer secretCache publicCache
        | none =>
          rw [randomOracle.run_eq, present]
          simp only [bind_assoc, pure_bind]
          calc
            _ = 𝒮[do
              let answer ← $ᵗ BitVec 256
              let table ← $ᵗ PrivateTable
              observe (fixPrivate (extendPrivate (secretCache.cacheQuery slot answer) table)
                (next answer)) publicCache] := by
                  apply evalSPMF_bind_congr
                  intro answer _
                  exact ih answer (secretCache.cacheQuery slot answer) publicCache
            _ = 𝒮[do
              let answer ← $ᵗ BitVec 256
              let table ← $ᵗ PrivateTable
              let updated := Function.update table slot answer
              observe (fixPrivate (extendPrivate secretCache updated)
                (next (extendPrivate secretCache updated slot))) publicCache] := by
                  simp only [extendPrivate_update secretCache _ slot present,
                    extendPrivate, present, Option.getD_none, Function.update_self]
            _ = 𝒮[do
              let table ← $ᵗ PrivateTable
              observe (fixPrivate (extendPrivate secretCache table)
                (next (extendPrivate secretCache table slot))) publicCache] :=
                  uniform_update_bind slot (fun table => observe
                    (fixPrivate (extendPrivate secretCache table)
                      (next (extendPrivate secretCache table slot))) publicCache)
            _ = _ := by
              apply evalSPMF_bind_congr
              intro table _
              rfl


/-- Independent private sources and canonical graph outputs, followed by the
unchanged counted program and actual lazy public random oracle. -/
noncomputable def graphObserve {α : Type} (program : OracleComp GameWorld α) : ProbComp α := do
  let answers ← $ᵗ PrivateTable
  let labels ← $ᵗ Labels
  observe (fixPrivate answers program)
    (SecurityGraphSampling.graphCache answers SecurityGraphOrder.positions labels ∅)

/-- Exact distributional reduction for every program in the actual game interface.
In particular, the result may retain all original hash-call counts. -/
theorem ideal_graph {α : Type} (program : OracleComp GameWorld α) :
    𝒮[idealObserve program ∅ ∅] = 𝒮[graphObserve program] := by
  rw [ideal_private_table]
  have empty (answers : PrivateTable) : extendPrivate ∅ answers = answers := by
    funext slot
    simp [extendPrivate]
  simp_rw [empty]
  unfold graphObserve
  apply evalSPMF_bind_congr
  intro answers _
  exact graph_presampling answers (fixPrivate answers program) (fun _ => 0)

/-- The concrete reference experiment in independent graph coordinates. Keygen,
signing, final verification, and all adversary H calls retain their original counts. -/
noncomputable def graphExperiment (publicCache : Cache) (adversary : Adversary submission.sizes)
    (rounds : Nat) : ProbComp AttackResult :=
  (fun result => ⟨result.1.won, result.2⟩) <$>
    graphObserve (SecurityBudget.counted (SecurityExperiment.program publicCache adversary rounds))

/-- The actual ideal reference experiment equals the independent graph experiment;
this is an unconditional identity, not a security assumption. -/
theorem idealExperiment_graph (publicCache : Cache) (adversary : Adversary submission.sizes)
    (rounds : Nat) :
    𝒮[SecurityExperiment.idealExperiment publicCache adversary rounds] =
      𝒮[graphExperiment publicCache adversary rounds] := by
  change 𝒮[(fun result => (⟨result.1.won, result.2⟩ : AttackResult)) <$>
    idealObserve (SecurityBudget.counted (SecurityExperiment.program publicCache adversary rounds)) ∅ ∅] = _
  simp only [graphExperiment, evalSPMF_map]
  rw [ideal_graph]


end SigGolfCandidate.Hypertree.SecurityGraphIdeal
