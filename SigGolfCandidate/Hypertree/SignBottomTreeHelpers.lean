import SigGolfCandidate.Hypertree.SignTreeFinish

namespace SigGolfCandidate.Hypertree.Signing
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 Keygen Verifying
set_option maxRecDepth 4096

structure BottomTreeSettings (s : MachineState) (pointer : Nat) (selected : Bool) : Prop where
  pointerEq : s.getMem 0x80448 = BitVec.ofNat 64 pointer
  enabled : s.getMem 0x80440 ≠ 0
  selectorEq : s.getMem 0x80420 = BitVec.ofNat 64 (Reference.sideNumber selected)

def BottomLeafFrame (s final : MachineState) (pointer : Nat) (side : Bool) : Prop :=
  ∀ a, a ≠ 0xffffe0 → a ≠ 0x80430 → a ≠ 0x80438 → OutsideBottomWork side a →
    (∀ i : Fin 2, a ≠ wordAddress pointer i.val) → final.getMem a = s.getMem a

theorem bottomOutside_of_leafResult (side : Bool) (a : Word) (outside : OutsideLeafResult side a) :
    OutsideBottomWork side a := ⟨outside.1.1.1, outside.1.1.2.1, outside.1.1.2.2.1, outside.2.2⟩

theorem BottomLeafFrame.keep (s final : MachineState) (pointer : Nat) (side : Bool)
    (valid : CapturePointerValid pointer) (frame : BottomLeafFrame s final pointer side)
    (a : Word) (stack : a ≠ 0xffffe0) (chain : a ≠ 0x80430) (step : a ≠ 0x80438)
    (outside : OutsideBottomWork side a) (range : a.toNat < 0x20060 ∨ 0x80000 ≤ a.toNat) :
    final.getMem a = s.getMem a := by
  apply frame a stack chain step outside
  intro i eq
  have ib := i.isLt
  rcases valid with ⟨lower, upper, aligned⟩
  have h := congrArg BitVec.toNat eq
  simp only [wordAddress, BitVec.toNat_ofNat] at h
  omega

theorem treeContext_after_bottom_leaf (s final : MachineState) (secretKey : SecretKey) (pointer tree : Nat)
    (side : Bool) (valid : CapturePointerValid pointer) (data : TreeContext s secretKey 0 tree)
    (frame : BottomLeafFrame s final pointer side) : TreeContext final secretKey 0 tree := by
  have keep := frame.keep s final pointer side valid
  constructor
  · rw [keep _ (by decide) (by decide) (by decide) (by unfold OutsideBottomWork; cases side <;> decide) (by decide)]
    exact data.levelEq
  · intro i
    rw [keep _ (by fin_cases i <;> decide) (by fin_cases i <;> decide) (by fin_cases i <;> decide)
      (by fin_cases i <;> unfold OutsideBottomWork <;> cases side <;> decide) (by fin_cases i <;> decide)]
    exact data.indexEq i
  · intro i
    rw [keep _ (by fin_cases i <;> decide) (by fin_cases i <;> decide) (by fin_cases i <;> decide)
      (by fin_cases i <;> unfold OutsideBottomWork <;> cases side <;> decide) (by fin_cases i <;> decide)]
    exact data.secretKeyEq i

theorem bottomSettings_after_leaf (s final : MachineState) (pointer : Nat) (side selected : Bool)
    (valid : CapturePointerValid pointer) (settings : BottomTreeSettings s pointer selected)
    (frame : BottomLeafFrame s final pointer side) : BottomTreeSettings final pointer selected := by
  have keep := frame.keep s final pointer side valid
  constructor
  · rw [keep _ (by decide) (by decide) (by decide) (by unfold OutsideBottomWork; cases side <;> decide) (by decide)]
    exact settings.pointerEq
  · rw [keep _ (by decide) (by decide) (by decide) (by unfold OutsideBottomWork; cases side <;> decide) (by decide)]
    exact settings.enabled
  · rw [keep _ (by decide) (by decide) (by decide) (by unfold OutsideBottomWork; cases side <;> decide) (by decide)]
    exact settings.selectorEq

theorem treeControl_bottom_settings (s : MachineState) (pointer : Nat) (selected : Bool)
    (side : BitVec 12) (jump : BitVec 21) (settings : BottomTreeSettings s pointer selected) :
    BottomTreeSettings (KeygenTreeControl.state s side jump) pointer selected := by
  constructor
  · rw [KeygenTreeControl.mem, if_neg (by decide)]; exact settings.pointerEq
  · rw [KeygenTreeControl.mem, if_neg (by decide)]; exact settings.enabled
  · rw [KeygenTreeControl.mem, if_neg (by decide)]; exact settings.selectorEq

theorem treeLeft_bottom_settings (s : MachineState) (pointer : Nat) (selected : Bool)
    (sp : s.getReg .x2 = 0x1000000) (settings : BottomTreeSettings s pointer selected) :
    BottomTreeSettings (treeLeftState s) pointer selected := by
  constructor
  · rw [treeLeft_frame s sp _ (by decide) (by decide)]; exact settings.pointerEq
  · rw [treeLeft_frame s sp _ (by decide) (by decide)]; exact settings.enabled
  · rw [treeLeft_frame s sp _ (by decide) (by decide)]; exact settings.selectorEq

end SigGolfCandidate.Hypertree.Signing
