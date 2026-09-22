import SigGolfCandidate.Hypertree.SecurityForgery
import SigGolfCandidate.Hypertree.SecurityGraphQuery

namespace SigGolfCandidate.Hypertree.SecurityIndexQuery
open SigGolf OracleComp OracleSpec Reference SecurityRandomOracle SecurityGraph SecurityGraphQuery
open scoped Classical
set_option backward.isDefEq.respectTransparency false

/-- Parse only exact index inputs for the original public key. Malformed inputs return none. -/
noncomputable def parse (pk : PublicKey) (query : Query) : Option (Message × Bytes 32) :=
  if found : ∃ pair : Message × Bytes 32, indexInput pk pair.1 pair.2 = query then some found.choose else none

theorem parse_some_iff (pk : PublicKey) (query : Query) (pair : Message × Bytes 32) :
    parse pk query = some pair ↔ indexInput pk pair.1 pair.2 = query := by
  unfold parse
  split
  next found =>
    constructor
    · intro same
      exact (Option.some.inj same) ▸ found.choose_spec
    · intro same
      exact congrArg some (SecurityForgery.indexInput_pair_injective pk (found.choose_spec.trans same.symm))
  next absent =>
    constructor
    · intro impossible; cases impossible
    · intro same; exact False.elim (absent ⟨pair,same⟩)

@[simp] theorem parse_index (pk : PublicKey) (message : Message) (r : Bytes 32) :
    parse pk (indexInput pk message r) = some (message,r) :=
  (parse_some_iff pk _ _).2 rfl

theorem parse_none_iff (pk : PublicKey) (query : Query) :
    parse pk query = none ↔ ∀ message r, indexInput pk message r ≠ query := by
  simp only [parse]
  split
  next found =>
    simp only [reduceCtorEq, false_iff]
    intro absent
    exact absent found.choose.1 found.choose.2 found.choose_spec
  next absent =>
    simp only [true_iff]
    intro message r same
    exact absent ⟨(message,r),same⟩

theorem locate_index (pk : PublicKey) (message : Message) (r : Bytes 32) :
    locate (indexInput pk message r) = none := by
  unfold locate
  split
  next found =>
    obtain ⟨payload,same⟩ := found.choose_spec
    change found.choose.address.input payload = (⟨5,0,0,0,0,0⟩ : Address).input _ at same
    have tag := congrArg Address.tag (Address.eq_of_input_eq same)
    have impossible (position : Position) (same : position.address.tag = 5) : False := by
      cases position <;> cases same
    exact False.elim (impossible found.choose tag)
  next absent => rfl

theorem parse_graph (pk : PublicKey) (position : Position) (payload : List Byte) :
    parse pk (position.address.input payload) = none := by
  rw [parse_none_iff]
  intro message r same
  have located := congrArg locate same
  rw [locate_index, locate_address] at located
  cases located

theorem parsed_not_seedEligible (pk : PublicKey) (query : Query) (pair : Message × Bytes 32)
    (parsed : parse pk query = some pair) : ¬SecuritySeparation.SeedEligible query := by
  rw [← (parse_some_iff pk query pair).1 parsed]
  exact SecurityDomains.not_seedEligible_addressedInput 5 0 0 0 0 0 _ (by decide) (by decide)

noncomputable def parsedInputs (pk : PublicKey) (inputs : List Query) : List (Message × Bytes 32) :=
  inputs.filterMap (parse pk)

theorem mem_parsedInputs (pk : PublicKey) (inputs : List Query) (message : Message) (r : Bytes 32) :
    (message,r) ∈ parsedInputs pk inputs ↔ indexInput pk message r ∈ inputs := by
  simp only [parsedInputs, List.mem_filterMap, parse_some_iff]
  constructor
  · rintro ⟨query,member,same⟩
    exact same ▸ member
  · intro member
    exact ⟨indexInput pk message r,member,rfl⟩

/-- Every populated residual cell has an earlier recorded public query. -/
def Covered (cache : QueryCache HashSpec) (inputs : List Query) : Prop :=
  ∀ query, cache query ≠ none → query ∈ inputs

@[simp] theorem covered_empty : Covered ∅ [] := by
  intro query present
  exact False.elim (present rfl)

theorem Covered.cacheQuery {cache : QueryCache HashSpec} {inputs : List Query}
    (covered : Covered cache inputs) (query : Query) (answer : BitVec 256) :
    Covered (cache.cacheQuery query answer) (query::inputs) := by
  intro other present
  by_cases same : other = query
  · subst other; exact List.mem_cons_self ..
  · apply List.mem_cons_of_mem
    apply covered other
    simpa only [QueryCache.cacheQuery_of_ne _ _ same] using present

/-- A cached first-signing index input necessarily appeared earlier with that exact nonce. -/
theorem cached_nonce_was_queried (pk : PublicKey) (cache : QueryCache HashSpec) (inputs : List Query)
    (covered : Covered cache inputs) (message : Message) (r : Bytes 32)
    (cached : cache (indexInput pk message r) ≠ none) : (message,r) ∈ parsedInputs pk inputs :=
  (mem_parsedInputs pk inputs message r).2 (covered _ cached)

/-- info: 'SigGolfCandidate.Hypertree.SecurityIndexQuery.cached_nonce_was_queried' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms cached_nonce_was_queried
end SigGolfCandidate.Hypertree.SecurityIndexQuery
