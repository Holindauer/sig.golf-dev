import SigGolfCandidate.Hypertree.SignBottomTreeHelpers

namespace SigGolfCandidate.Hypertree.Signing
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 Keygen Verifying
set_option maxRecDepth 4096

def BottomLowFrame (s final : MachineState) (hash : Hash) (secretKey : SecretKey) (pointer tree : Nat) (side : Bool) : Prop :=
  ∀ a, a.toNat < 0x80000 → final.getMem a =
    if s.getMem 0x80440 ≠ 0 ∧ s.getMem 0x80428 = s.getMem 0x80420 then
      if a = BitVec.ofNat 64 pointer + 8 then (Reference.secret hash secretKey 0 tree side 0).extractLsb' 64 64 else
      if a = BitVec.ofNat 64 pointer then (Reference.secret hash secretKey 0 tree side 0).extractLsb' 0 64 else s.getMem a
    else s.getMem a

theorem bottom_selected_value (s final : MachineState) (hash : Hash) (secretKey : SecretKey) (pointer tree : Nat)
    (side : Bool) (valid : CapturePointerValid pointer) (data : LeafContext s secretKey 0 tree side)
    (settings : BottomTreeSettings s pointer side) (frame : BottomLowFrame s final hash secretKey pointer tree side) :
    CapturedValue final pointer 0 (Reference.secret hash secretKey 0 tree side 0) := by
  have condition : s.getMem 0x80440 ≠ 0 ∧ s.getMem 0x80428 = s.getMem 0x80420 :=
    ⟨settings.enabled, data.leafEq.trans settings.selectorEq.symm⟩
  have ne : BitVec.ofNat 64 pointer ≠ BitVec.ofNat 64 pointer + 8 := by
    intro eq
    have : (8 : Word) = 0 := BitVec.add_right_eq_self.mp eq.symm
    contradiction
  intro i
  have low := signature_word_low pointer valid 0 i
  have h := frame _ low
  rw [if_pos condition] at h
  fin_cases i
  · simpa [wordAddress, ne] using h
  · have addr : wordAddress (pointer+16*(0:Reference.Chain).val) 1 = BitVec.ofNat 64 pointer + 8 := by
      simpa [wordAddress] using BitVec.ofNat_add (n := 64) pointer 8
    rw [addr, if_pos rfl] at h
    rw [addr]
    exact h

theorem bottom_unselected_low (s final : MachineState) (hash : Hash) (secretKey : SecretKey) (pointer tree : Nat)
    (side selected : Bool) (data : LeafContext s secretKey 0 tree side) (settings : BottomTreeSettings s pointer selected)
    (different : side ≠ selected) (frame : BottomLowFrame s final hash secretKey pointer tree side)
    (a : Word) (low : a.toNat < 0x80000) : final.getMem a = s.getMem a := by
  rw [frame a low]
  have ne : s.getMem 0x80428 ≠ s.getMem 0x80420 := by
    rw [data.leafEq, settings.selectorEq]
    cases side <;> cases selected <;> simp_all [Reference.sideNumber]
  simp only [ne, and_false, if_false]

end SigGolfCandidate.Hypertree.Signing
