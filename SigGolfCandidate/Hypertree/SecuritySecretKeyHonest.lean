import SigGolfCandidate.Hypertree.SecurityMonitorView
import SigGolfCandidate.Hypertree.SecurityDomains

namespace SigGolfCandidate.Hypertree.SecuritySecretKeyHonest
open SigGolf OracleComp OracleSpec Reference SecurityDerivation SecurityGameHop SecuritySeparation
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

/-- Every query on every answer history satisfies the given domain predicate. -/
inductive Safe {ι : Type} {spec : OracleSpec ι} {α : Type} (allowed : spec.Domain → Prop) :
    OracleComp spec α → Prop where
  | pure (value : α) : Safe allowed (pure value)
  | query (input : spec.Domain) (next : spec.Range input → OracleComp spec α)
      (good : allowed input) (tails : ∀ answer, Safe allowed (next answer)) :
      Safe allowed (liftM (spec.query input) >>= next)

theorem Safe.bind {ι : Type} {spec : OracleSpec ι} {α β : Type} {allowed : spec.Domain → Prop}
    {program : OracleComp spec α} (safe : Safe allowed program) (next : α → OracleComp spec β)
    (tails : ∀ value, Safe allowed (next value)) : Safe allowed (program >>= next) := by
  induction safe with
  | pure value => simpa only [pure_bind] using tails value
  | query input continuation good safe ih =>
    simpa only [bind_assoc] using Safe.query input _ good ih

theorem Safe.map {ι : Type} {spec : OracleSpec ι} {α β : Type} {allowed : spec.Domain → Prop}
    {program : OracleComp spec α} (safe : Safe allowed program) (f : α → β) : Safe allowed (f <$> program) := by
  simpa only [←map_eq_pure_bind] using safe.bind (fun value => Pure.pure (f value)) (fun _ => Safe.pure _)

theorem Safe.ask {ι : Type} {spec : OracleSpec ι} (allowed : spec.Domain → Prop)
    (input : spec.Domain) (good : allowed input) : Safe allowed (liftM (spec.query input) : OracleComp spec _) := by
  simpa only [bind_pure] using Safe.query input Pure.pure good (fun value => Safe.pure value)

def allowed : SplitWorld.Domain → Prop
  | .inl _ => True
  | .inr input => ¬ SecretKeyEligible input

/-- Safe honest blocks pass through the secret key stop without changing the program
or observing any of the monitor's decisions. -/
theorem Safe.stop_bind {α β : Type} (secretKey : SecretKey) {program : OracleComp GameWorld α}
    (safe : Safe (fun query => ¬isBad secretKey query) program) (next : α → OracleComp GameWorld β) :
    stop secretKey (program >>= next) = (program >>= fun value => stop secretKey (next value)) := by
  induction safe with
  | pure value => simp only [pure_bind]
  | query input continuation good safe ih =>
    rw [bind_assoc, stop_query_bind, if_neg good, bind_assoc]
    exact bind_congr ih

theorem Safe.lift {α : Type} (secretKey : SecretKey) {program : OracleComp SplitWorld α}
    (safe : Safe allowed program) : Safe (fun query => ¬isBad secretKey query) (program.liftComp GameWorld) := by
  induction safe with
  | pure value => exact Safe.pure _
  | query input next good safe ih =>
    simp only [liftComp_bind, liftComp_query, OracleQuery.input_query, OracleQuery.cont_query, id_map]
    change Safe _ (liftM (GameWorld.query (.inr input)) >>= _)
    apply Safe.query _ _ _ ih
    cases input with
    | inl slot => simp only [isBad, publicSecretKeyHit, not_false_eq_true]
    | inr query => exact fun hit => good hit.1

@[simp] theorem ask (tag level tree leaf chain step : Nat) (payload : List Byte)
    (notChain : tag % 256 ≠ 1) (notNonce : tag % 256 ≠ 6) :
    Safe (fun query => ¬SecretKeyEligible query) (SecurityReference.ask tag level tree leaf chain step payload) :=
  Safe.ask _ _ (SecurityDomains.not_secretKeyEligible_addressedInput _ _ _ _ _ _ _ notChain notNonce)

@[simp] theorem chainHash (level tree : Nat) (side : Bool) (chain : Chain) (step : Nat) (value : Digest) :
    Safe (fun query => ¬SecretKeyEligible query) (SecurityReference.chainHash level tree side chain step value) :=
  (ask 2 level tree (sideNumber side) chain.val step (bytes value) (by decide) (by decide)).map truncate

@[simp] theorem compressLeaf (level tree : Nat) (side : Bool) (values : Chain → Digest) :
    Safe (fun query => ¬SecretKeyEligible query) (SecurityReference.compressLeaf level tree side values) :=
  (ask 3 level tree (sideNumber side) 0 0 _ (by decide) (by decide)).map truncate

@[simp] theorem node (level tree : Nat) (left right : Digest) :
    Safe (fun query => ¬SecretKeyEligible query) (SecurityReference.node level tree left right) :=
  (ask 4 level tree 0 0 0 _ (by decide) (by decide)).map truncate

@[simp] theorem publicCall {α : Type} {program : OracleComp HashSpec α}
    (safe : Safe (fun query => ¬SecretKeyEligible query) program) : Safe allowed (SecurityIdealKeygen.publicCall program) := by
  induction safe with
  | pure value => exact Safe.pure _
  | query input next good safe ih =>
    simp only [SecurityIdealKeygen.publicCall, liftComp_bind, liftComp_query,
      OracleQuery.input_query, OracleQuery.cont_query, id_map]
    change Safe allowed (liftM (SplitWorld.query (.inr input)) >>= _)
    exact Safe.query _ _ good ih

@[simp] theorem secret (address : ChainAddress) : Safe allowed (SecurityIdealKeygen.secret address) :=
  (Safe.ask (spec := SplitWorld) allowed (.inl (.chain address)) trivial).map truncate

theorem walk {α : Type} (body : Nat → α → OracleComp HashSpec α) (start count : Nat) (value : α)
    (safe : ∀ step value, Safe (fun query => ¬SecretKeyEligible query) (body step value)) :
    Safe (fun query => ¬SecretKeyEligible query) (SecurityReference.walk body start count value) := by
  induction count generalizing start value with
  | zero => exact Safe.pure _
  | succ count ih => exact (safe start value).bind _ (fun value' => ih (start+1) value')

theorem sequenceFin {α : Type} (n : Nat) (body : Fin n → OracleComp SplitWorld α)
    (safe : ∀ i, Safe allowed (body i)) : Safe allowed (SecurityIdealKeygen.sequenceFin n body) := by
  induction n with
  | zero => exact Safe.pure _
  | succ n ih =>
    simpa only [SecurityIdealKeygen.sequenceFin, map_eq_pure_bind] using
      (safe 0).bind _ (fun head => (ih (fun i => body i.succ) (fun i => safe i.succ)).map
        (fun tail => (Fin.cases head tail : Fin (n+1) → α)))

@[simp] theorem endpoint (address : ChainAddress) : Safe allowed (SecurityIdealKeygen.endpoint address) :=
  (secret address).bind _ (fun value => publicCall
    (walk _ 0 7 value (chainHash address.level.val address.tree.toNat address.side address.chain)))

theorem leafRoot (level : Fin 160) (tree : BitVec 192) (side : Bool) :
    Safe allowed (SecurityIdealKeygen.leafRoot level tree side) := by
  unfold SecurityIdealKeygen.leafRoot
  split
  · exact (secret ⟨level,tree,side,0⟩).bind _ (fun value => publicCall (chainHash _ _ _ _ _ value))
  · exact (sequenceFin 46 _ (fun chain => endpoint ⟨level,tree,side,chain⟩)).bind _
      (fun values => publicCall (compressLeaf _ _ _ values))

theorem treeRoot (level : Fin 160) (tree : BitVec 192) : Safe allowed (SecurityIdealKeygen.treeRoot level tree) :=
  (leafRoot level tree false).bind _ (fun left =>
    (leafRoot level tree true).bind _ (fun right => publicCall (node level.val tree.toNat left right)))

theorem keygen : Safe allowed SecurityIdealKeygen.keygen := treeRoot ⟨159, by decide⟩ 0

end SigGolfCandidate.Hypertree.SecuritySecretKeyHonest
