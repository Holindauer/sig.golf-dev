import SigGolf.Parameters

namespace SigGolf
open OracleSpec OracleComp

/-- Exact bit strings, including their lengths; no implicit domain separation. -/
abbrev Query := (n : Nat) × BitVec n
abbrev HashSpec : OracleSpec Query := Query →ₒ BitVec 256
abbrev Hash := QueryImpl HashSpec Id
abbrev World := unifSpec + HashSpec

/-- One shared lazy random oracle. Repeated inputs receive the same answer. -/
noncomputable def withRandomOracle {α : Type} (program : OracleComp HashSpec α) : ProbComp α :=
  (simulateQ (randomOracle : QueryImpl HashSpec (StateT (QueryCache HashSpec) ProbComp)) program).run' ∅

/-- Private coins and the secret key sampler do not replace or reset the shared oracle. -/
noncomputable def withRandomness {α : Type} (program : OracleComp World α) : ProbComp α :=
  (simulateQ (unifFwdImpl HashSpec +
    (randomOracle : QueryImpl HashSpec (StateT (QueryCache HashSpec) ProbComp))) program).run' ∅

noncomputable def sampleSecretKey : ProbComp SecretKey := $ᵗ SecretKey

end SigGolf
