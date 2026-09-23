import SigGolfCandidate.Hypertree.SecurityGraphMonitorOracle
import SigGolfCandidate.Hypertree.SecurityGraphStateRoute

namespace SigGolfCandidate.Hypertree.SecurityGraphMonitorSign
open SigGolf OracleComp OracleSpec Reference SecurityDerivation SecurityGraph SecurityGraphFrontier
  SecurityGraphPassive SecurityGraphDisclosure SecurityGraphFactor SecurityGraphPublicMonitor
  SecurityGraphMonitorProgram SecurityGraphSigner
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
open scoped Classical

/-- Public preimage targets and chain endpoints are disclosed at setup. -/
def PublicReady (table : PointTable) (cache : QueryCache PointSpec) : Prop :=
  ∀ address : ChainAddress, ∀ step : Fin 7, address.level.val = 0 ∨ step.val = 6 →
    cache (address,step.succ) = some (table (address,step.succ))

theorem revealCache_preserves (table : PointTable) (points : List Point) (cache : QueryCache PointSpec)
    (point : Point) (known : cache point = some (table point)) :
    revealCache table points cache point = some (table point) := by
  induction points generalizing cache with
  | nil => exact known
  | cons other rest ih =>
    apply ih
    by_cases same : point = other
    · subst other; simp
    · simpa only [QueryCache.cacheQuery_of_ne _ _ same] using known

theorem PublicReady.reveal {table : PointTable} {cache : QueryCache PointSpec}
    (ready : PublicReady table cache) (points : List Point) : PublicReady table (revealCache table points cache) := by
  intro address step isPublic
  exact revealCache_preserves table points cache _ (ready address step isPublic)

theorem metadata_ready (table : PointTable) (nonces : NonceTable) (metadata : MetadataTable)
    (cache : QueryCache PointSpec) (ready : PublicReady table cache) :
    MetadataAgree (labels (viewFactors cache metadata)) (labels (table,(nonces,metadata))) := by
  intro position isPublic
  cases position with
  | chain address step =>
    simp only [labels, viewFactors, ready address step isPublic, Option.getD_some]
  | leaf level tree side => rfl
  | node level tree => rfl

noncomputable def needed (metadata : MetadataTable) (cache : QueryCache PointSpec) (index : BitVec 152) : List Point :=
  (signaturePoints (labels (viewFactors cache metadata)) index).toList

theorem opened_signature (table : PointTable) (nonces : NonceTable) (metadata : MetadataTable)
    (cache : QueryCache PointSpec) (ready : PublicReady table cache) (r : Bytes 32) (index : BitVec 152) :
    let opened := revealCache table (needed metadata cache index) cache
    signature (privateTable (viewFactors opened metadata)) (labels (viewFactors opened metadata)) r index =
      signature (privateTable (table,(nonces,metadata))) (labels (table,(nonces,metadata))) r index := by
  dsimp only
  apply signature_congr _ _ _ _ (metadata_ready table nonces metadata _ (ready.reveal _))
  intro point member
  have original : point ∈ needed metadata cache index := by
    rw [needed, Finset.mem_toList]
    have openedSame := signaturePoints_congr _ _ (metadata_ready table nonces metadata _ (ready.reveal (needed metadata cache index))) index
    have originalSame := signaturePoints_congr _ _ (metadata_ready table nonces metadata cache ready) index
    rw [originalSame]
    rwa [openedSame] at member
  simp only [assembled_chainPoint, viewFactors,
    revealCache_mem table (needed metadata cache index) cache point original, Option.getD_some]

theorem run_disclose {α : Type} (table : PointTable) (points : List Point) (cache : QueryCache PointSpec)
    (next : QueryCache PointSpec → Program α) :
    run table cache (SecurityGraphMonitorOracle.disclose points cache next) =
      run table (revealCache table points cache) (next (revealCache table points cache)) := by
  induction points generalizing cache with
  | nil => rfl
  | cons point rest ih => exact ih (cache.cacheQuery point (table point))

/-- A residual H5 call has no graph contact tests; private nonces are fixed separately. -/
noncomputable def indexStep {α : Type} (cache : QueryCache HashSpec) (query : Query)
    (next : BitVec 256 → QueryCache HashSpec → Program α) : Program α :=
  match cache query with
  | some answer => next answer cache
  | none => .bits (fun answer => next answer (cache.cacheQuery query answer))

theorem run_indexStep {α : Type} (table : PointTable) (exposed : QueryCache PointSpec)
    (cache : QueryCache HashSpec) (query : Query)
    (next : BitVec 256 → QueryCache HashSpec → Program α) :
    run table exposed (indexStep cache query next) =
      ((randomOracle (spec := HashSpec) query).run cache >>= fun result => run table exposed (next result.1 result.2)) := by
  cases present : cache query <;> simp only [indexStep, present, run, randomOracle.run_eq, pure_bind, bind_assoc]

def SignResult := SignatureEncoding.Compact × QueryCache PointSpec × QueryCache HashSpec

/-- Honest signing reveals exactly its needed canonical points after one H5 call. -/
noncomputable def sign (nonces : NonceTable) (metadata : MetadataTable) (exposed : QueryCache PointSpec)
    (cache : QueryCache HashSpec) (pk : PublicKey) (message : Message) : Program SignResult :=
  let r := nonces message
  indexStep cache (SecurityRandomOracle.indexInput pk message r) (fun answer residual =>
    let index := answer.extractLsb' 0 152
    SecurityGraphMonitorOracle.disclose (needed metadata exposed index) exposed (fun opened =>
      .done (signature (privateTable (viewFactors opened metadata)) (labels (viewFactors opened metadata)) r index,
        opened,residual)))

theorem run_sign (table : PointTable) (nonces : NonceTable) (metadata : MetadataTable)
    (exposed : QueryCache PointSpec) (ready : PublicReady table exposed)
    (cache : QueryCache HashSpec) (pk : PublicKey) (message : Message) :
    run table exposed (sign nonces metadata exposed cache pk message) =
      (fun result => (⟨(signature (privateTable (table,(nonces,metadata))) (labels (table,(nonces,metadata)))
        (nonces message) (result.1.extractLsb' 0 152),
          revealCache table (needed metadata exposed (result.1.extractLsb' 0 152)) exposed,result.2),false,0⟩ : Outcome SignResult)) <$>
        (randomOracle (spec := HashSpec) (SecurityRandomOracle.indexInput pk message (nonces message))).run cache := by
  simp only [sign, run_indexStep, run_disclose, run, opened_signature table nonces metadata exposed ready,
    ← map_eq_pure_bind]

/-- info: 'SigGolfCandidate.Hypertree.SecurityGraphMonitorSign.run_sign' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms run_sign
end SigGolfCandidate.Hypertree.SecurityGraphMonitorSign
