import SigGolfCandidate.Hypertree.VerifyLeafCall
import SigGolfCandidate.Hypertree.VerifyTreeEntry
import SigGolfCandidate.Hypertree.VerifyTreeFinish
import SigGolfCandidate.Hypertree.KeygenVerifyBottomLeaf

namespace SigGolfCandidate.Hypertree.Verifying
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 Keygen Signing
set_option maxRecDepth 4096

/-- Only the bottom layer's first value is serialized; upper layers serialize all 46. -/
structure LayerData (s : MachineState) (level tree base : Nat) (side : Bool)
    (message : Reference.Digest) (signature : Reference.LayerSignature) : Prop where
  levelEq : s.getMem 0x80400 = BitVec.ofNat 64 level
  indexEq : ∀ i : Fin 3, s.getMem (wordAddress 0x80408 i.val) = (BitVec.ofNat 192 tree).extractLsb' (64*i.val) 64
  pointerEq : s.getMem 0x80448 = BitVec.ofNat 64 base
  selectorEq : s.getMem 0x80420 = BitVec.ofNat 64 (Reference.sideNumber side)
  valueEq : ∀ chain : Reference.Chain, level ≠ 0 ∨ chain = 0 → ∀ i : Fin 2,
    s.getMem (BitVec.ofNat 64 (base+16*chain.val+8*i.val)) = (signature.values chain).extractLsb' (64*i.val) 64
  digitEq : level ≠ 0 → ∀ chain : Reference.Chain,
    s.getByte (BitVec.ofNat 64 (0x80600+chain.val)) = BitVec.ofNat 8 (Reference.digit message chain).val
  siblingEq : ∀ i : Fin 2, s.getMem (BitVec.ofNat 64 (base+siblingOffset level+8*i.val)) = signature.sibling.extractLsb' (64*i.val) 64

theorem LayerData.upper (s : MachineState) (level tree base : Nat) (side : Bool)
    (message : Reference.Digest) (signature : Reference.LayerSignature)
    (data : LayerData s level tree base side message signature) (nonzero : level ≠ 0)
    (leaf : s.getMem 0x80428 = BitVec.ofNat 64 (Reference.sideNumber side)) :
    LeafData s level tree side base message signature.values :=
  ⟨data.levelEq, leaf, data.pointerEq, data.indexEq,
    fun chain => data.valueEq chain (Or.inl nonzero), data.digitEq nonzero⟩

theorem LayerData.bottom (s : MachineState) (tree base : Nat) (side : Bool)
    (message : Reference.Digest) (signature : Reference.LayerSignature)
    (data : LayerData s 0 tree base side message signature)
    (leaf : s.getMem 0x80428 = BitVec.ofNat 64 (Reference.sideNumber side)) :
    KeygenVerifyBottom.Data s tree side base (signature.values 0) := by
  refine ⟨data.levelEq, leaf, data.pointerEq, data.indexEq, ?_⟩
  intro i
  simpa [wordAddress] using data.valueEq 0 (Or.inr rfl) i

/-- A uniform complete leaf call for either serialized layer format. -/
theorem recover_leaf_call (hash : Hash) (s : MachineState) (level tree base : Nat) (side : Bool)
    (message : Reference.Digest) (signature : Reference.LayerSignature)
    (pc : s.pc = 0x1458) (sp : s.getReg .x2 = 0xfffff0)
    (data : LayerData s level tree base side message signature)
    (leaf : s.getMem 0x80428 = BitVec.ofNat 64 (Reference.sideNumber side))
    (small : level < 160) (aligned : base % 8 = 0) (bound : base+752 ≤ 0x80000) :
    ∃ final steps cycles calls blocks, Trace hash verify s steps cycles calls blocks final ∧
      steps ≤ 33795 ∧ cycles ≤ 36144 ∧ calls ≤ 323 ∧ blocks ≤ 334 ∧
      final.pc = s.getReg .x1 &&& ~~~1#64 ∧ final.getReg .x2 = s.getReg .x2 ∧
      (∀ i : Fin 2, final.getMem (KeygenSavePublic.wordAddress side i.val) =
        (Reference.recoverLeaf hash level tree side message signature).extractLsb' (64*i.val) 64) ∧
      (∀ a, a ≠ 0xffffe0 → OutsideUpperLeaf side a → final.getMem a = s.getMem a) := by
  by_cases zero : level = 0
  · subst level
    obtain ⟨final, run, fpc, fsp, output, frame⟩ := KeygenVerifyBottom.call hash s tree side base message signature pc sp
      (data.bottom s tree base side message signature leaf) aligned (by omega)
    refine ⟨final, 109, 116, 1, 1, run, by decide, by decide, by decide, by decide, fpc, fsp, output, ?_⟩
    intro a hs outside
    apply frame a hs outside.1.2.2.2.2.1 outside.1.2.2.2.2.2
    exact ⟨fun i => outside.1.1 ⟨i.val, by have := i.isLt; omega⟩, outside.1.2.1, outside.1.2.2.1, outside.2⟩
  · have nonzero : BitVec.ofNat 64 level ≠ 0 := by
      intro eq
      have h := congrArg BitVec.toNat eq
      change level % 2^64 = 0 at h
      omega
    obtain ⟨final, steps, cycles, calls, run, hsteps, hcycles, hcalls, fpc, fsp, output, frame⟩ :=
      upper_leaf_call hash s level tree side base message signature pc sp
        (data.upper s level tree base side message signature zero leaf) nonzero aligned (by omega)
    exact ⟨final, steps, cycles, calls+1, calls+12, run, hsteps, hcycles, by omega, by omega, fpc, fsp, output, frame⟩

/-- info: 'SigGolfCandidate.Hypertree.Verifying.recover_leaf_call' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms recover_leaf_call

end SigGolfCandidate.Hypertree.Verifying
