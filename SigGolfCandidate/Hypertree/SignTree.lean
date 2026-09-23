import SigGolfCandidate.Hypertree.SignBottomTreeFinish
import SigGolfCandidate.Hypertree.SignAdvance

namespace SigGolfCandidate.Hypertree.Signing
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 Keygen Verifying
set_option maxRecDepth 4096

def LayerStored (s : MachineState) (pointer level : Nat) (signature : Reference.LayerSignature) : Prop :=
  if level = 0 then BottomLayerStored s pointer signature else UpperLayerStored s pointer signature

def layerBytes (level : Nat) : Nat := if level = 0 then 32 else 752

def OutsideLayer (pointer level : Nat) (a : Word) : Prop :=
  a.toNat < pointer ∨ pointer + layerBytes level ≤ a.toNat

theorem outsideLayer_value (pointer level : Nat) (valid : CapturePointerValid pointer) (a : Word)
    (outside : OutsideLayer pointer level a) (chain : Reference.Chain) (usable : level = 0 → chain.val = 0)
    (i : Fin 2) : a ≠ wordAddress (pointer+16*chain.val) i.val := by
  intro eq
  have h := congrArg BitVec.toNat eq
  have cb := chain.isLt; have ib := i.isLt
  rcases valid with ⟨lower,upper,aligned⟩
  simp only [wordAddress,BitVec.toNat_ofNat] at h
  unfold OutsideLayer layerBytes at outside
  split at outside <;> rename_i hl <;> simp_all <;> omega

theorem outsideLayer_sibling (pointer level : Nat) (valid : CapturePointerValid pointer) (a : Word)
    (outside : OutsideLayer pointer level a) (i : Fin 2) :
    a ≠ wordAddress (pointer + (if level = 0 then 16 else 736)) i.val := by
  intro eq
  have h := congrArg BitVec.toNat eq
  have ib := i.isLt
  rcases valid with ⟨lower,upper,aligned⟩
  simp only [wordAddress,BitVec.toNat_ofNat] at h
  unfold OutsideLayer layerBytes at outside
  split at outside <;> rename_i hl <;> simp_all <;> omega

/-- Both signer tree paths produce exactly the reference layer's serialized fields. -/
theorem sign_tree (hash : Hash) (s : MachineState) (secretKey : SecretKey) (pointer level tree : Nat)
    (message : Reference.Digest) (selected : Bool) (pc : s.pc = 0x13c8) (sp : s.getReg .x2 = 0x1000000)
    (bound : level < 160) (valid : CapturePointerValid pointer) (data : TreeContext s secretKey level tree)
    (ptr : s.getMem 0x80448 = BitVec.ofNat 64 pointer) (enabled : s.getMem 0x80440 ≠ 0)
    (selector : s.getMem 0x80420 = BitVec.ofNat 64 (Reference.sideNumber selected))
    (digits : level ≠ 0 → ∀ chain : Reference.Chain,
      s.getByte (BitVec.ofNat 64 (0x80600+chain.val)) = BitVec.ofNat 8 (Reference.digit message chain).val) :
    ∃ final instructions cycles, Trace hash sign s instructions cycles
      (if level = 0 then 5 else 739) (if level = 0 then 5 else 761) final ∧
      instructions ≤ (if level = 0 then 537 else 99910) ∧ cycles ≤ (if level = 0 then 572 else 105259) ∧
      final.pc = s.getReg .x1 &&& ~~~1#64 ∧ final.getReg .x2 = s.getReg .x2 ∧
      (∀ i : Fin 2, final.getMem (wordAddress 0x80500 i.val) =
        (Reference.treeRoot hash secretKey level tree).extractLsb' (64*i.val) 64) ∧
      LayerStored final pointer level (Reference.signLayer hash secretKey level tree selected message) ∧
      (∀ a, OutsideTreeWork a → OutsideLayer pointer level a → final.getMem a = s.getMem a) := by
  by_cases zero : level = 0
  · subst level
    obtain ⟨final,n,c,run,nb,cb,fpc,fsp,root,stored,frame⟩ :=
      sign_bottom_tree hash s secretKey pointer tree selected pc sp valid data ⟨ptr,enabled,selector⟩
    refine ⟨final,n,c,run,nb,cb,fpc,fsp,root,?_,?_⟩
    · simpa [LayerStored,BottomLayerStored,Reference.signLayer] using stored
    · intro a work outside
      apply frame a work
      · intro i
        simpa using outsideLayer_value pointer 0 valid a outside 0 (by simp) i
      · exact fun i => outsideLayer_sibling pointer 0 valid a outside i
  · have wordNonzero : BitVec.ofNat 64 level ≠ 0 := by
      intro eq
      have h := congrArg BitVec.toNat eq
      change level % 2^64 = 0 at h
      omega
    obtain ⟨final,n,c,run,nb,cb,fpc,fsp,root,stored,frame⟩ :=
      sign_upper_tree hash s secretKey pointer level tree message selected pc sp wordNonzero valid data
        ⟨ptr,enabled,selector,digits zero⟩
    refine ⟨final,n,c,?_,?_,?_,fpc,fsp,root,?_,?_⟩
    · simpa only [if_neg zero] using run
    · simpa only [if_neg zero] using nb
    · simpa only [if_neg zero] using cb
    · simpa only [LayerStored,if_neg zero] using stored
    · intro a work outside
      apply frame a work
      · exact fun chain i => outsideLayer_value pointer level valid a outside chain (by simp [zero]) i
      · intro i
        simpa only [if_neg zero] using outsideLayer_sibling pointer level valid a outside i

/-- Low memory is untouched by the tree's scratch work. -/
theorem outsideTreeWork_low (a : Word) (low : a.toNat < 0x80000) : OutsideTreeWork a := by
  have ne (b : Word) (high : 0x80000 ≤ b.toNat) : a ≠ b := low_ne_high a b low high
  refine ⟨⟨outsideLeaf_regions false a (Or.inl low) (ne _ (by decide)) (ne _ (by decide)),
    outsideLeaf_regions true a (Or.inl low) (ne _ (by decide)) (ne _ (by decide)),
    ne _ (by decide),ne _ (by decide),ne _ (by decide)⟩,(low_outside_node a low).2.2⟩

/-- info: 'SigGolfCandidate.Hypertree.Signing.sign_tree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sign_tree
end SigGolfCandidate.Hypertree.Signing
