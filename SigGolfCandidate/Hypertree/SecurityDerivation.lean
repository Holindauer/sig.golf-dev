import SigGolfCandidate.Hypertree.SecuritySecretKey
import SigGolfCandidate.Hypertree.SecurityReference

namespace SigGolfCandidate.Hypertree.SecurityDerivation
open SigGolf OracleSpec OracleComp Reference SecurityRandomOracle SecurityPacking SecuritySecretKey

/-- Explicit bounds ensure that distinct private chain slots cannot alias through
header overflow or tree truncation. -/
structure ChainAddress where
  level : Fin 160
  tree : BitVec 192
  side : Bool
  chain : Chain
  deriving DecidableEq

inductive Slot where
  | chain (address : ChainAddress)
  | randomizer (message : Message)
  deriving DecidableEq

abbrev SecretSpec : OracleSpec Slot := Slot →ₒ BitVec 256
abbrev SplitWorld := SecretSpec + HashSpec

def header (address : ChainAddress) : BitVec 64 :=
  BitVec.ofNat 64 (1 + address.level.val * 2 ^ 8 + sideNumber address.side * 2 ^ 16 +
    address.chain.val * 2 ^ 24)

private theorem header_bound (address : ChainAddress) :
    1 + address.level.val * 2 ^ 8 + sideNumber address.side * 2 ^ 16 +
      address.chain.val * 2 ^ 24 < 2 ^ 64 := by
  have hl := address.level.isLt
  have hc := address.chain.isLt
  cases hs : address.side <;> simp [sideNumber] <;> omega

private theorem header_fields (first second : ChainAddress) (same : header first = header second) :
    first.level = second.level ∧ first.side = second.side ∧ first.chain = second.chain := by
  have h := congrArg BitVec.toNat same
  simp only [header, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (header_bound first),
    Nat.mod_eq_of_lt (header_bound second)] at h
  have hl := first.level.isLt
  have hl' := second.level.isLt
  have hc := first.chain.isLt
  have hc' := second.chain.isLt
  have level : first.level.val = second.level.val := by
    cases hfirst : first.side <;> cases hsecond : second.side <;>
      simp [sideNumber, hfirst, hsecond] at h <;> omega
  have chain : first.chain.val = second.chain.val := by
    cases hfirst : first.side <;> cases hsecond : second.side <;>
      simp [sideNumber, hfirst, hsecond] at h <;> omega
  refine ⟨Fin.ext level, ?_, Fin.ext chain⟩
  cases hfirst : first.side <;> cases hsecond : second.side <;>
    simp [sideNumber, hfirst, hsecond] at h ⊢ <;> omega

/-- A private slot is implemented by precisely one actual reference H input. -/
def input (secretKey : SecretKey) : Slot → Query
  | .chain address => addressedInput 1 address.level.val address.tree.toNat
      (sideNumber address.side) address.chain.val 0 (bytes secretKey)
  | .randomizer message => randomizerInput secretKey message

@[simp] theorem chain_input_length (secretKey : SecretKey) (address : ChainAddress) :
    (input secretKey (.chain address)).1 = 512 := by simp [input, bytes]

@[simp] theorem nonce_input_length (secretKey : SecretKey) (message : Message) :
    (input secretKey (.randomizer message)).1 = 768 := by simp [input]

theorem input_secretKeyAt (secretKey : SecretKey) (slot : Slot) : SecretKeyAt (input secretKey slot) secretKey := by
  cases slot with
  | chain address =>
    exact secretKeyAt_secret secretKey address.level.val address.tree.toNat
      (sideNumber address.side) address.chain.val
  | randomizer message => exact secretKeyAt_randomizer secretKey message

/-- A normalization lemma keeps byte packing opaque in the injectivity proof. -/
theorem chain_input_eq (secretKey : SecretKey) (address : ChainAddress) :
    input secretKey (.chain address) =
      packed (bytes (n := 8) (header address) ++ bytes (n := 24) address.tree ++ bytes secretKey) := by
  simp [input, addressedInput, header]

/-- Private slots remain distinct under the exact reference byte packing. -/
theorem input_injective (secretKey : SecretKey) : Function.Injective (input secretKey) := by
  intro first second same
  cases first with
  | chain first =>
    cases second with
    | chain second =>
      rw [chain_input_eq, chain_input_eq] at same
      have h := packed_injective same
      have payload := List.append_cancel_right h
      have hh := bytes_injective 8 (List.append_inj_left payload (by simp [bytes]))
      have tree := bytes_injective 24 (List.append_inj_right payload (by simp [bytes]))
      obtain ⟨level, side, chain⟩ := header_fields first second hh
      have addresses : first = second := by
        cases first; cases second; cases level; cases tree; cases side; cases chain; rfl
      exact congrArg Slot.chain addresses
    | randomizer message =>
      have h := congrArg Sigma.fst same
      simp at h
  | randomizer message =>
    cases second with
    | chain address =>
      have h := congrArg Sigma.fst same
      simp at h
    | randomizer message' =>
      have h := packed_injective same
      have hb : bytes message = bytes message' := by
        simpa [input, randomizerInput, addressedInput, List.append_assoc] using h
      exact congrArg Slot.randomizer (bytes_injective 32 hb)

/-- Changing either the secret key or private slot changes the actual oracle input. -/
theorem secretKeyed_input_injective : Function.Injective (fun pair : SecretKey × Slot => input pair.1 pair.2) := by
  intro first second same
  change input first.1 first.2 = input second.1 second.2 at same
  have hf : SecretKeyAt (input second.1 second.2) first.1 := by
    rw [← same]
    exact input_secretKeyAt first.1 first.2
  have secretKeys : first.1 = second.1 := secretKeyAt_unique hf (input_secretKeyAt second.1 second.2)
  apply Prod.ext secretKeys
  apply input_injective second.1
  simpa [secretKeys] using same

/-- Real interpretation of the private derivation oracle: each query makes one H call. -/
def realDerivation (secretKey : SecretKey) : QueryImpl SecretSpec (OracleComp HashSpec) :=
  fun slot => liftM (HashSpec.query (input secretKey slot))

def realImplementation (secretKey : SecretKey) : QueryImpl SplitWorld (OracleComp HashSpec) :=
  realDerivation secretKey + (HasQuery.toQueryImpl (spec := HashSpec) (m := OracleComp HashSpec))

/-- The chain-secret slot is exactly the secretKeyed source used by the reference algorithm. -/
theorem eval_real_chain (hash : Hash) (secretKey : SecretKey) (address : ChainAddress) :
    Reference.truncate (evalWithAnswerFn hash (realDerivation secretKey (.chain address))) =
      Reference.secret hash secretKey address.level.val address.tree.toNat address.side address.chain := rfl

theorem eval_real_randomizer (hash : Hash) (secretKey : SecretKey) (message : Message) :
    evalWithAnswerFn hash (realDerivation secretKey (.randomizer message)) =
      Reference.randomizer hash secretKey message := rfl

end SigGolfCandidate.Hypertree.SecurityDerivation
