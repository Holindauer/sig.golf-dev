import SigGolfCandidate.Hypertree.VerifyWitness
import SigGolfCandidate.Hypertree.LoopIndexArithmetic
import SigGolfCandidate.Hypertree.LoopDispatchFrame
import SigGolfCandidate.Hypertree.VerifyControl

namespace SigGolfCandidate.Hypertree.Verifying
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 Keygen Signing
set_option maxRecDepth 4096

/-- Word preservation in the fixed input region; the byte view follows from aligned words. -/
def LowFrame (s final : MachineState) : Prop :=
  ∀ address : Nat, address % 8 = 0 → address+8 ≤ 0x80000 →
    final.getMem (BitVec.ofNat 64 address) = s.getMem (BitVec.ofNat 64 address)

theorem LowFrame.trans (s middle final : MachineState) (first : LowFrame s middle)
    (second : LowFrame middle final) : LowFrame s final := by
  intro address aligned bound
  exact (second address aligned bound).trans (first address aligned bound)

theorem WitnessStored.transfer_words (s final : MachineState) (witness : Bytes signatureBytes)
    (stored : WitnessStored s witness) (frame : LowFrame s final) : WitnessStored final witness := by
  intro i hi
  rw [getByte_word final 0x3d3b0 i (by decide) (by change i < 119632 at hi; omega)]
  have words := frame (0x3d3b0+8*(i/8)) (by omega) (by change i < 119632 at hi; omega)
  change final.getMem (wordAddress 0x3d3b0 (i/8)) = s.getMem (wordAddress 0x3d3b0 (i/8)) at words
  rw [words]
  simpa only [getByte_word s 0x3d3b0 i (by decide) (by change i < 119632 at hi; omega)] using stored i hi

structure LoopData (s : MachineState) (level index : Nat) (current : Reference.Digest)
    (witness : Bytes signatureBytes) : Prop where
  stack : s.getReg .x2 = 0x1000000
  levelEq : s.getMem 0x80400 = BitVec.ofNat 64 level
  indexEq : StoredIndex s (BitVec.ofNat 192 index)
  pointerEq : s.getMem 0x80448 = BitVec.ofNat 64 (0x3d3b0+layerOffset level)
  currentEq : ∀ i : Fin 2, s.getMem (wordAddress 0x80500 i.val) = current.extractLsb' (64*i.val) 64
  witnessEq : WitnessStored s witness

theorem shift_low_frame (s : MachineState) : LowFrame s (shiftIndexState s) := by
  intro address _ bound
  rw [shiftIndexState_mem]
  have h (target : Nat) (high : 0x80000 ≤ target) (small : target < 2^64) :
      BitVec.ofNat 64 address ≠ BitVec.ofNat 64 target := by
    intro eq
    have nat := congrArg BitVec.toNat eq
    simp only [BitVec.toNat_ofNat] at nat
    omega
  have h18 : BitVec.ofNat 64 address ≠ 0x80418 := h _ (by decide) (by decide)
  have h10 : BitVec.ofNat 64 address ≠ 0x80410 := h _ (by decide) (by decide)
  have h08 : BitVec.ofNat 64 address ≠ 0x80408 := h _ (by decide) (by decide)
  have h20 : BitVec.ofNat 64 address ≠ 0x80420 := h _ (by decide) (by decide)
  rw [if_neg h18, if_neg h10, if_neg h08, if_neg h20]

theorem LoopData.shift (s : MachineState) (level index : Nat) (current : Reference.Digest)
    (witness : Bytes signatureBytes) (data : LoopData s level index current witness) (small : index < 2^192) :
    LoopData (shiftIndexState s) level (index/2) current witness := by
  refine ⟨(shiftIndexState_sp s).trans data.stack, ?_, (shift_index_nat s index small data.indexEq).1, ?_, ?_, ?_⟩
  · rw [shiftIndexState_mem]; simpa using data.levelEq
  · rw [shiftIndexState_mem]; simpa using data.pointerEq
  · intro i
    rw [shiftIndexState_mem]
    have h := data.currentEq i
    fin_cases i <;> simpa [wordAddress] using h
  · exact data.witnessEq.transfer_words s _ witness (shift_low_frame s)

end SigGolfCandidate.Hypertree.Verifying
