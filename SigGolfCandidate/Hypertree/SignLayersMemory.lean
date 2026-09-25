import SigGolfCandidate.Hypertree.SignLayer

namespace SigGolfCandidate.Hypertree.Signing
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 Keygen Verifying
set_option maxRecDepth 4096

def LayersStored (s : MachineState) : Nat → List Reference.LayerSignature → Prop
  | _, [] => True
  | level, signature :: rest => LayerStored s (0x20060+layerOffset level) level signature ∧ LayersStored s (level+1) rest

theorem layerOffset_mono (a b : Nat) (le : a ≤ b) : layerOffset a ≤ layerOffset b := by
  unfold layerOffset
  split <;> split <;> omega

theorem layer_value_before_next (level : Nat) (_bound : level<160) (chain : Reference.Chain)
    (usable : level=0 → chain.val=0) (i : Fin 2) :
    0x20060+layerOffset level+16*chain.val+8*i.val < 0x20060+layerOffset (level+1) := by
  rw [layerOffset_succ]
  have cb := chain.isLt; have ib := i.isLt
  split <;> rename_i h <;> simp_all <;> omega

theorem LayerStored.prefix_frame (s final : MachineState) (level : Nat) (signature : Reference.LayerSignature)
    (bound : level<160) (stored : LayerStored s (0x20060+layerOffset level) level signature)
    (frame : ∀ address : Nat, address<0x80000 → address%8=0 → address<0x20060+layerOffset (level+1) →
      final.getMem (BitVec.ofNat 64 address) = s.getMem (BitVec.ofNat 64 address)) :
    LayerStored final (0x20060+layerOffset level) level signature := by
  have valid := sign_pointer_valid level bound
  have aligned := valid.2.2
  have upper := valid.2.1
  unfold LayerStored at *
  split at stored <;> rename_i h
  · rw [if_pos h]
    constructor
    · intro i
      have ib := i.isLt
      change final.getMem (BitVec.ofNat 64 (0x20060+layerOffset level+16*(0:Reference.Chain).val+8*i.val)) = _
      rw [frame _ (by omega) (by omega) (layer_value_before_next level bound 0 (by simp) i)]
      exact stored.1 i
    · intro i
      have ib := i.isLt
      change final.getMem (BitVec.ofNat 64 (0x20060+layerOffset level+16+8*i.val)) = _
      rw [frame _ (by omega) (by omega) (by rw [layerOffset_succ]; rw [if_pos h]; omega)]
      exact stored.2 i
  · rw [if_neg h]
    constructor
    · intro chain i
      have cb := chain.isLt; have ib := i.isLt
      change final.getMem (BitVec.ofNat 64 (0x20060+layerOffset level+16*chain.val+8*i.val)) = _
      rw [frame _ (by omega) (by omega) (layer_value_before_next level bound chain (by simp [h]) i)]
      exact stored.1 chain i
    · intro i
      have ib := i.isLt
      change final.getMem (BitVec.ofNat 64 (0x20060+layerOffset level+736+8*i.val)) = _
      rw [frame _ (by omega) (by omega) (by rw [layerOffset_succ]; rw [if_neg h]; omega)]
      exact stored.2 i

end SigGolfCandidate.Hypertree.Signing
