import SigGolfCandidate.Hypertree.PreludeSecurityInterface
namespace SigGolfCandidate.Hypertree.PreludeSecurity
open SigGolf OracleComp OracleSpec SecurityBytecode SecurityCache SecurityGraphHidden
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
theorem observe_coin_bind {α : Type} (n : Nat) (next : Fin (n+1) → OracleComp World α)
    (cache : QueryCache HashSpec) :
    observe ((liftM (unifSpec.query n) : OracleComp World _) >>= next) cache =
      (do let answer ← liftM (unifSpec.query n); observe (next answer) cache) := by
  unfold observe
  change (simulateQ implementation ((liftM (World.query (.inl n))) >>= next)).run' cache = _
  rw [run'_query_bind]
  change ((fun answer => (answer,cache)) <$> (liftM (unifSpec.query n) : ProbComp _) >>= _) = _
  simp only [map_eq_bind_pure_comp,Function.comp_apply,bind_assoc,pure_bind]

/-- Adaptive interaction preserves every adversary observation, signing history,
private coin and total charged count, under the key established by key generation. -/
theorem interact_equivalent_generic (left right : Interface) (fact : Hash → Prop)
    (adversary : Adversary submission.sizes) (secretKey : SecretKey) (pk : PublicKey)
    (rounds : Nat) (state : adversary.State) (transcript : Transcript submission.sizes)
    (cache : QueryCache HashSpec) (known : Knows cache fact)
    (sameSign : ∀ hash, fact hash → ∀ request,
      evalWithAnswerFn hash (left.sign secretKey pk request)=evalWithAnswerFn hash (right.sign secretKey pk request))
    (sameCheck : ∀ hash transcript candidate,
      evalWithAnswerFn hash (left.check pk transcript candidate)=evalWithAnswerFn hash (right.check pk transcript candidate)) :
    𝒮[observe (interactWith left adversary secretKey pk rounds state transcript) cache] =
      𝒮[observe (interactWith right adversary secretKey pk rounds state transcript) cache] := by
  induction rounds generalizing state transcript cache with
  | zero => rfl
  | succ rounds ih =>
    simp only [interactWith]
    cases action : adversary.step state <;> simp only
    case submit candidate =>
      simpa only [bind_pure] using contextual_equivalence
        (left.check pk transcript candidate) (right.check pk transcript candidate)
        (fun hash => sameCheck hash transcript candidate) (pure : AttackResult → OracleComp World AttackResult) cache
    case hash input resume =>
      change 𝒮[observe ((liftM (HashSpec.query input) : OracleComp HashSpec _).liftComp World >>= _) cache] =
        𝒮[observe ((liftM (HashSpec.query input) : OracleComp HashSpec _).liftComp World >>= _) cache]
      rw [observe_hash_bind,observe_hash_bind]
      apply evalSPMF_bind_congr
      intro result mem
      exact ih (resume result.1) _ result.2 (known.after _ cache result mem)
    case sign request resume =>
      split
      · calc
          _ = 𝒮[observe ((right.sign secretKey pk request).liftComp World >>= fun result =>
            interactWith left adversary secretKey pk rounds (resume result.1)
              (recordView transcript request.message result)) cache] :=
            contextual_equivalence_at _ _ _ cache (fun hash agree => sameSign hash (known hash agree) request)
          _ = _ := by
            rw [observe_hash_bind,observe_hash_bind]
            apply evalSPMF_bind_congr
            intro result mem
            exact ih (resume result.1.1) _ result.2 (known.after _ cache result mem)
      · rfl
    case sample n resume =>
      rw [observe_coin_bind,observe_coin_bind]
      apply evalSPMF_bind_congr
      intro answer _
      exact ih (resume answer) transcript cache known
    case step next => exact ih next transcript cache known

/-- info: 'SigGolfCandidate.Hypertree.PreludeSecurity.interact_equivalent_generic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms interact_equivalent_generic
end SigGolfCandidate.Hypertree.PreludeSecurity
