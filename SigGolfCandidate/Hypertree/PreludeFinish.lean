import SigGolfCandidate.Hypertree.SignFinish
import SigGolfCandidate.Hypertree.ImagesPrelude

namespace SigGolfCandidate.Hypertree.Signing.Prelude
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 OracleComp Expansion
set_option maxRecDepth 4096
theorem sign_footer_code : FooterCode signPrelude 0x12f8 := by
  intro s i pc
  simp only [fetch, pc]
  fin_cases i <;> decide


theorem sign_footer_executes (hash : Hash) (s : MachineState) (pc : s.pc = 0x12f8) :
    ∃ (steps : Nat) (final : MachineState), steps ≤ 15 ∧
      Executes hash signPrelude s steps
        ⟨if RootMatches s then .success else .failure, final, steps, 0, 0⟩ ∧
      ∀ a, final.getMem a = s.getMem a :=
  footer_executes hash signPrelude 0x12f8 sign_footer_code s pc

/-- info: 'SigGolfCandidate.Hypertree.Signing.Prelude.sign_footer_executes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sign_footer_executes

end SigGolfCandidate.Hypertree.Signing.Prelude
