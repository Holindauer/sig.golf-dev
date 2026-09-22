import SigGolfCandidate.Hypertree.VerifyEndpoint

namespace SigGolfCandidate.Hypertree.Verifying
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 Keygen Signing
set_option maxRecDepth 4096

/-- Words outside the work buffers of the 46-chain verifier loop. -/
def OutsideLeafWork (a : Word) : Prop :=
  (∀ i : Fin 96, a ≠ wordAddress 0x80000 i.val) ∧
  (∀ i : Fin 4, a ≠ wordAddress 0x80300 i.val) ∧
  (∀ i : Fin 2, a ≠ wordAddress 0x80510 i.val) ∧
  (∀ i : Fin 92, a ≠ wordAddress 0x80800 i.val) ∧ a ≠ 0x80430 ∧ a ≠ 0x80438

theorem outside_leaf_chain (a : Word) (outside : OutsideLeafWork a) : OutsideChainWork a :=
  ⟨fun i => outside.1 ⟨i.val, by have := i.isLt; omega⟩, outside.2.1, outside.2.2.1, outside.2.2.2.2.2⟩

theorem outside_leaf_endpoint (a : Word) (outside : OutsideLeafWork a) (chain : Reference.Chain) (i : Fin 2) :
    a ≠ KeygenEndpoint.endpointAddress chain.val i.val := by
  have different := outside.2.2.2.1 ⟨2*chain.val+i.val, by have hc := chain.isLt; have hi := i.isLt; omega⟩
  have eq : KeygenEndpoint.endpointAddress chain.val i.val = wordAddress 0x80800 (2*chain.val+i.val) := by
    unfold wordAddress KeygenEndpoint.endpointAddress
    apply congrArg (BitVec.ofNat 64)
    omega
  rw [eq]
  exact different

theorem outside_leaf_of_lt (a : Word) (low : a.toNat < 0x80000) : OutsideLeafWork a := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i eq
    have h := congrArg BitVec.toNat eq
    change a.toNat = (0x80000+8*i.val) % 2^64 at h
    have := i.isLt
    omega
  · intro i eq
    have h := congrArg BitVec.toNat eq
    change a.toNat = (0x80300+8*i.val) % 2^64 at h
    have := i.isLt
    omega
  · intro i eq
    have h := congrArg BitVec.toNat eq
    change a.toNat = (0x80510+8*i.val) % 2^64 at h
    have := i.isLt
    omega
  · intro i eq
    have h := congrArg BitVec.toNat eq
    change a.toNat = (0x80800+8*i.val) % 2^64 at h
    have := i.isLt
    omega
  · intro eq; subst a; contradiction
  · intro eq; subst a; contradiction

structure LeafData (s : MachineState) (level tree : Nat) (side : Bool) (base : Nat)
    (message : Reference.Digest) (values : Reference.Chain → Reference.Digest) : Prop where
  levelEq : s.getMem 0x80400 = BitVec.ofNat 64 level
  leafEq : s.getMem 0x80428 = BitVec.ofNat 64 (Reference.sideNumber side)
  pointerEq : s.getMem 0x80448 = BitVec.ofNat 64 base
  indexEq : ∀ i : Fin 3, s.getMem (wordAddress 0x80408 i.val) = (BitVec.ofNat 192 tree).extractLsb' (64*i.val) 64
  valueEq : ∀ chain : Reference.Chain, ∀ i : Fin 2,
    s.getMem (BitVec.ofNat 64 (base+16*chain.val+8*i.val)) = (values chain).extractLsb' (64*i.val) 64
  digitEq : ∀ chain : Reference.Chain,
    s.getByte (BitVec.ofNat 64 (0x80600+chain.val)) = BitVec.ofNat 8 (Reference.digit message chain).val

/-- The loop's frame condition preserves every input needed by later chains. -/
theorem LeafData.transfer (s final : MachineState) (level tree : Nat) (side : Bool) (base : Nat)
    (message : Reference.Digest) (values : Reference.Chain → Reference.Digest)
    (data : LeafData s level tree side base message values) (bound : base+736 ≤ 0x80000)
    (frame : ∀ a, OutsideLeafWork a → final.getMem a = s.getMem a) :
    LeafData final level tree side base message values := by
  constructor
  · rw [frame _ (by unfold OutsideLeafWork; decide)]; exact data.levelEq
  · rw [frame _ (by unfold OutsideLeafWork; decide)]; exact data.leafEq
  · rw [frame _ (by unfold OutsideLeafWork; decide)]; exact data.pointerEq
  · intro i
    rw [frame _ (by fin_cases i <;> unfold OutsideLeafWork <;> decide)]
    exact data.indexEq i
  · intro chain i
    rw [frame _ (outside_leaf_of_lt _ ?_)]
    · exact data.valueEq chain i
    · have hc := chain.isLt
      have hi := i.isLt
      change (base+16*chain.val+8*i.val) % 2^64 < 0x80000
      omega
  · intro chain
    rw [getByte_word final 0x80600 chain.val (by decide) (by have := chain.isLt; omega),
      frame _ (by fin_cases chain <;> unfold OutsideLeafWork <;> decide),
      ← getByte_word s 0x80600 chain.val (by decide) (by have := chain.isLt; omega)]
    exact data.digitEq chain

/-- Previously recovered endpoint words are pairwise distinct from the next endpoint's words. -/
theorem endpointAddress_ne (first second : Reference.Chain) (i j : Fin 2) (different : first ≠ second) :
    KeygenEndpoint.endpointAddress first.val i.val ≠ KeygenEndpoint.endpointAddress second.val j.val := by
  intro same
  have h := congrArg BitVec.toNat same
  have hf := first.isLt
  have hs := second.isLt
  have hi := i.isLt
  have hj := j.isLt
  have vals : first.val ≠ second.val := fun eq => different (Fin.ext eq)
  change (0x80800+16*first.val+8*i.val) % 2^64 = (0x80800+16*second.val+8*j.val) % 2^64 at h
  omega

theorem endpoint_outside_chain (chain : Reference.Chain) (i : Fin 2) :
    OutsideChainWork (KeygenEndpoint.endpointAddress chain.val i.val) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  all_goals
    first
    | intro j same
      have h := congrArg BitVec.toNat same
      simp only [KeygenEndpoint.endpointAddress, wordAddress, BitVec.toNat_ofNat] at h
      have hc := chain.isLt
      have hi := i.isLt
      have hj := j.isLt
      omega
    | intro same
      have h := congrArg BitVec.toNat same
      change (0x80800+16*chain.val+8*i.val) % 2^64 = 0x80438 at h
      have hc := chain.isLt
      have hi := i.isLt
      omega

end SigGolfCandidate.Hypertree.Verifying
