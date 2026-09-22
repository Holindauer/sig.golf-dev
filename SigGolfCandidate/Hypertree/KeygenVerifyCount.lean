import SigGolfCandidate.Hypertree.VerifyLeafLoop

namespace SigGolfCandidate.Hypertree.KeygenVerifyCount
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 Keygen Signing Verifying
set_option maxRecDepth 4096

def chainPrefix (message : Reference.Digest) (count : Nat) : Nat :=
  ∑ i ∈ Finset.range count, (7-(Reference.digit message ⟨i%46, Nat.mod_lt _ (by decide)⟩).val)

theorem chainPrefix_zero (message : Reference.Digest) : chainPrefix message 0=0 := by simp [chainPrefix]

theorem chainPrefix_succ (message : Reference.Digest) (n : Nat) (bound : n<46) :
    chainPrefix message (n+1)=chainPrefix message n+(7-(Reference.digit message ⟨n,bound⟩).val) := by
  simp [chainPrefix,Finset.sum_range_succ,Nat.mod_eq_of_lt bound]

def chainCalls (message : Reference.Digest) : Nat := ∑ chain : Reference.Chain, (7-(Reference.digit message chain).val)

theorem chainPrefix_full (message : Reference.Digest) : chainPrefix message 46=chainCalls message := by
  unfold chainCalls chainPrefix
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Nat.mod_eq_of_lt i.isLt]

end SigGolfCandidate.Hypertree.KeygenVerifyCount
