import SigGolfCandidate.Hypertree.SecurityExperimentAtomic

namespace SigGolfCandidate.Hypertree.SecurityMonitorView
open SigGolf OracleComp OracleSpec Reference SignatureEncoding SecurityDerivation SecurityGameHop
  SecurityExperiment
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

/-- The actual adversary-visible operations. Honest signing remains one atomic
operation with its complete reference implementation in `realize`; it will be
charged its already-proved 117508 calls by every monitor interpretation. -/
inductive View (α : Type) where
  | done (value : α)
  | hash (query : Query) (next : BitVec 256 → View α)
  | sign (pk : PublicKey) (message : Message) (next : Option (Bytes signatureBytes) → View α)
  | coin (n : Nat) (next : Fin (n + 1) → View α)

def realize {α : Type} : View α → OracleComp GameWorld α
  | .done value => pure value
  | .hash input next => do
      let answer ← liftM (GameWorld.query (.inr (.inr input)))
      realize (next answer)
  | .sign pk message next => do
      let answer ← (signWire pk message).liftComp GameWorld
      realize (next answer)
  | .coin n next => do
      let answer ← liftM (GameWorld.query (.inl n))
      realize (next answer)

/-- The real verifier's entire hash computation becomes public operations in the
same view as the adversary's own oracle probes. -/
def ofHash {α β : Type} (program : OracleComp HashSpec α) (next : α → View β) : View β :=
  OracleComp.construct next (fun query _ continuation => .hash query continuation) program

@[simp] theorem ofHash_pure {α β : Type} (value : α) (next : α → View β) :
    ofHash (pure value) next = next value := rfl

theorem ofHash_query {α β : Type} (query : Query) (resume : BitVec 256 → OracleComp HashSpec α)
    (next : α → View β) :
    ofHash (liftM (HashSpec.query query) >>= resume) next =
      .hash query (fun answer => ofHash (resume answer) next) := rfl

/-- Exact realization, including the adaptive verifier query order. -/
theorem realize_ofHash {α β : Type} (program : OracleComp HashSpec α) (next : α → View β) :
    realize (ofHash program next) = program.liftComp GameWorld >>= fun value => realize (next value) := by
  induction program using OracleComp.inductionOn with
  | pure value => simp [ofHash_pure, realize]
  | query_bind query resume ih =>
    rw [ofHash_query]
    simp only [realize, liftComp_bind, bind_assoc]
    change (liftM (GameWorld.query (.inr (.inr query))) >>= fun answer =>
      realize (ofHash (resume answer) next)) =
      (liftM (GameWorld.query (.inr (.inr query))) >>= fun answer =>
        (resume answer).liftComp GameWorld >>= fun value => realize (next value))
    exact bind_congr ih

def ofCheck (pk : PublicKey) (transcript : Transcript submission.sizes) :
    Forgery submission.sizes → View Result
  | .witness message witness =>
      let signature := decode witness
      ofHash (SecurityVerify.verifyCompact pk message signature) (fun accepted =>
        .done ⟨accepted && transcript.freshMessage message, some (message, signature), transcript⟩)
  | .signature message wire =>
      let signature := decode wire
      ofHash (SecurityVerify.verifyCompact pk message signature) (fun accepted =>
        .done ⟨accepted && transcript.freshSignature message wire, some (message, signature), transcript⟩)

@[simp] theorem realize_ofCheck (pk : PublicKey) (transcript : Transcript submission.sizes)
    (forgery : Forgery submission.sizes) : realize (ofCheck pk transcript forgery) = check pk transcript forgery := by
  cases forgery <;> simp only [ofCheck, realize_ofHash, check, realize]

/-- A syntax tree of the actual finite adversary interaction. Supplied cache bytes,
both submission modes, all private coin ranges, and the lifetime gate are retained. -/
def ofInteract (adversary : Adversary submission.sizes) (pk : PublicKey) :
    Nat → adversary.State → Transcript submission.sizes → View Result
  | 0, _, transcript => .done ⟨false, none, transcript⟩
  | rounds + 1, state, transcript =>
      match adversary.step state with
      | .submit forgery => ofCheck pk transcript forgery
      | .hash input resume => .hash input (fun answer => ofInteract adversary pk rounds (resume answer) transcript)
      | .sign request resume =>
          if transcript.signingRequests < LIFETIME then
            .sign pk request.message (fun result =>
              let next : Transcript submission.sizes :=
                { transcript with
                  signed := match result with
                    | none => transcript.signed
                    | some signature => (request.message, signature) :: transcript.signed
                  signingRequests := transcript.signingRequests + 1 }
              ofInteract adversary pk rounds (resume result) next)
          else .done ⟨false, none, transcript⟩
      | .sample n resume => .coin n (fun answer => ofInteract adversary pk rounds (resume answer) transcript)
      | .step next => ofInteract adversary pk rounds next transcript

/-- The shared view realizes exactly the organizer-style reference interaction;
this is a semantic identity, before any probability or security assumptions. -/
theorem realize_ofInteract (adversary : Adversary submission.sizes) (pk : PublicKey)
    (rounds : Nat) (state : adversary.State) (transcript : Transcript submission.sizes) :
    realize (ofInteract adversary pk rounds state transcript) = interact adversary pk rounds state transcript := by
  induction rounds generalizing state transcript with
  | zero => rfl
  | succ rounds ih =>
    unfold ofInteract interact
    cases action : adversary.step state with
    | submit forgery => exact realize_ofCheck pk transcript forgery
    | hash query resume =>
      change (liftM (GameWorld.query (.inr (.inr query))) >>= _) = _
      exact bind_congr (fun answer => ih (resume answer) transcript)
    | sign request resume =>
      dsimp only
      by_cases allowed : transcript.signingRequests < LIFETIME
      · rw [if_pos allowed, if_pos allowed]
        change ((signWire pk request.message).liftComp GameWorld >>= _) = _
        exact bind_congr (fun result => ih (resume result) _)
      · rw [if_neg allowed, if_neg allowed]
        rfl
    | sample n resume =>
      change (liftM (GameWorld.query (.inl n)) >>= _) = _
      exact bind_congr (fun answer => ih (resume answer) transcript)
    | step next => exact ih next transcript

/-- Full reference program factorization: actual key generation followed by the
same shared view interpreted by every cryptographic monitor. -/
theorem program_eq (publicCache : Cache) (adversary : Adversary submission.sizes) (rounds : Nat) :
    program publicCache adversary rounds = (do
      let pk ← SecurityIdealKeygen.keygen.liftComp GameWorld
      realize (ofInteract adversary pk rounds (adversary.initial pk publicCache) {})) := by
  unfold program
  apply bind_congr
  intro pk
  exact (realize_ofInteract adversary pk rounds _ _).symm

end SigGolfCandidate.Hypertree.SecurityMonitorView
