import SigGolfCandidate.Hypertree.VerifyLoopState

namespace SigGolfCandidate.Hypertree.Verifying
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 Keygen Signing
set_option maxRecDepth 4096

theorem advance_low_frame (s : MachineState) : LowFrame s (advanceState s) := by
  intro address _ bound
  have level : BitVec.ofNat 64 address ≠ 0x80400 := by
    intro eq
    have h := congrArg BitVec.toNat eq
    change address % 2^64 = 0x80400 at h
    omega
  have pointer : BitVec.ofNat 64 address ≠ 0x80448 := by
    intro eq
    have h := congrArg BitVec.toNat eq
    change address % 2^64 = 0x80448 at h
    omega
  rw [advanceState_mem, if_neg level, if_neg pointer]

theorem LoopData.advance (s : MachineState) (level index : Nat) (current : Reference.Digest)
    (witness : Bytes signatureBytes) (data : LoopData s level index current witness) (small : level < 160) :
    LoopData (advanceState s) (level+1) index current witness := by
  have updated := advanceState_layer s 0x3d3b0 level small data.levelEq data.pointerEq
  refine ⟨(advanceState_sp s).trans data.stack, updated.1, ?_, updated.2, ?_, ?_⟩
  · intro i
    rw [advanceState_mem]
    have h := data.indexEq i
    fin_cases i <;> simpa [wordAddress] using h
  · intro i
    rw [advanceState_mem]
    have h := data.currentEq i
    fin_cases i <;> simpa [wordAddress] using h
  · exact data.witnessEq.transfer_words s _ witness (advance_low_frame s)

end SigGolfCandidate.Hypertree.Verifying
