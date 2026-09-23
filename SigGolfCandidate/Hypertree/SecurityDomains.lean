import SigGolfCandidate.Hypertree.SecuritySeparation

namespace SigGolfCandidate.Hypertree.SecurityDomains
open SigGolf OracleSpec Reference SecurityRandomOracle SecurityPacking SecurityDerivation SecuritySeparation

/-- Equality of complete packed inputs implies equality of their serialized headers,
even when all tree identifiers and payloads are adversarially chosen. -/
theorem addressedInput_header_eq {tag level tree leaf chain step tag' level' tree' leaf' chain' step' : Nat}
    {payload payload' : List Byte}
    (same : addressedInput tag level tree leaf chain step payload =
      addressedInput tag' level' tree' leaf' chain' step' payload') :
    BitVec.ofNat 64 (tag + level * 2 ^ 8 + leaf * 2 ^ 16 + chain * 2 ^ 24 + step * 2 ^ 32) =
      BitVec.ofNat 64 (tag' + level' * 2 ^ 8 + leaf' * 2 ^ 16 + chain' * 2 ^ 24 + step' * 2 ^ 32) := by
  have h := packed_injective same
  have headers := List.append_inj_left h (by simp [bytes])
  exact bytes_injective 8 (List.append_inj_left headers (by simp [bytes]))

private theorem header_tag (tag level leaf chain step : Nat) :
    (BitVec.ofNat 64 (tag + level * 2 ^ 8 + leaf * 2 ^ 16 + chain * 2 ^ 24 + step * 2 ^ 32)).toNat % 256 =
      tag % 256 := by
  rw [BitVec.toNat_ofNat, Nat.mod_mod_of_dvd _ (by decide : 256 ∣ 2 ^ 64)]
  simp [Nat.add_mod, Nat.mul_mod]

/-- The tag occupies the first byte and remains separated under every other field,
including unbounded attacker-controlled numeric arguments. -/
theorem addressedInput_tag_eq {tag level tree leaf chain step tag' level' tree' leaf' chain' step' : Nat}
    {payload payload' : List Byte}
    (same : addressedInput tag level tree leaf chain step payload =
      addressedInput tag' level' tree' leaf' chain' step' payload') :
    tag % 256 = tag' % 256 := by
  have h := congrArg (fun header : BitVec 64 => header.toNat % 256) (addressedInput_header_eq same)
  simpa only [header_tag] using h

/-- Exact secret key-guess candidates can occur only in derivation tags 1 and 6.
Consequently chain, leaf-compression, node, and index queries consume no secret key budget. -/
theorem not_secretKeyEligible_addressedInput (tag level tree leaf chain step : Nat) (payload : List Byte)
    (notChain : tag % 256 ≠ 1) (notNonce : tag % 256 ≠ 6) :
    ¬SecretKeyEligible (addressedInput tag level tree leaf chain step payload) := by
  rintro ⟨secretKey, slot, same⟩
  cases slot with
  | chain address =>
    have h := addressedInput_tag_eq same
    exact notChain h.symm
  | randomizer message =>
    have h := addressedInput_tag_eq same
    exact notNonce h.symm

end SigGolfCandidate.Hypertree.SecurityDomains
