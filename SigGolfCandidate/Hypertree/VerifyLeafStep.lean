import SigGolfCandidate.Hypertree.VerifyLeafState

namespace SigGolfCandidate.Hypertree.Verifying
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 Keygen Signing
set_option maxRecDepth 4096

def recoveredEndpoint (hash : Hash) (level tree : Nat) (side : Bool) (message : Reference.Digest)
    (values : Reference.Chain → Reference.Digest) (chain : Reference.Chain) : Reference.Digest :=
  walk (Reference.chainHash hash level tree side chain) (Reference.digit message chain).val
    (7-(Reference.digit message chain).val) (values chain)

/-- One complete verifier leaf iteration: witness load, chain recovery, endpoint store, and counter advance. -/
theorem leaf_step (hash : Hash) (s : MachineState) (level tree : Nat) (side : Bool) (base : Nat)
    (message : Reference.Digest) (values : Reference.Chain → Reference.Digest) (chain : Reference.Chain)
    (pc : s.pc = 0x1490) (data : LeafData s level tree side base message values)
    (counter : s.getMem 0x80430 = BitVec.ofNat 64 chain.val)
    (aligned : base % 8 = 0) (bound : base+736 ≤ 0x80000) :
    ∃ final, Trace hash verify s (96*(7-(Reference.digit message chain).val)+49)
      (103*(7-(Reference.digit message chain).val)+49)
      (7-(Reference.digit message chain).val) (7-(Reference.digit message chain).val) final ∧
      final.pc = (if chain.val+1 = 46 then 0x1690 else 0x1490) ∧
      final.getMem 0x80430 = BitVec.ofNat 64 (chain.val+1) ∧
      LeafData final level tree side base message values ∧
      (∀ i : Fin 2, final.getMem (KeygenEndpoint.endpointAddress chain.val i.val) =
        (recoveredEndpoint hash level tree side message values chain).extractLsb' (64*i.val) 64) ∧
      final.getReg .x1 = s.getReg .x1 ∧ final.getReg .x2 = s.getReg .x2 ∧
      (∀ a, OutsideChainWork a → a ≠ 0x80430 →
        (∀ i : Fin 2, a ≠ KeygenEndpoint.endpointAddress chain.val i.val) → final.getMem a = s.getMem a) := by
  have safe := chainSource_safe s base chain data.pointerEq counter aligned (by
    have hc := chain.isLt
    simp only [MEMORY_BYTES]
    omega)
  have source := chainSource_eq s base chain data.pointerEq counter
  have value0 : s.getMem (chainSource s) = (values chain).extractLsb' 0 64 := by
    rw [source]
    simpa only [Fin.val_zero, Nat.mul_zero, Nat.add_zero] using data.valueEq chain 0
  have value8 : s.getMem (chainSource s+8) = (values chain).extractLsb' 64 64 := by
    rw [source]
    have add : BitVec.ofNat 64 (base+16*chain.val)+8 = BitVec.ofNat 64 (base+16*chain.val+8) :=
      (BitVec.ofNat_add _ _).symm
    rw [add]
    simpa only [Fin.val_one, Nat.mul_one] using data.valueEq chain 1
  obtain ⟨recovered, run, recoveredPC, recoveredData, recoveredRA, recoveredSP, recoveredFrame⟩ :=
    recover_chain_fragment hash s level tree side chain (Reference.digit message chain) (values chain) pc
      safe.1 safe.2 data.levelEq data.leafEq counter data.indexEq value0 value8 (data.digitEq chain)
  obtain ⟨final, store, finalPC, finalCounter, endpoints, finalRA, finalSP, storeFrame⟩ := store_endpoint recovered chain
    (recoveredEndpoint hash level tree side message values chain) recoveredPC recoveredData.chainEq recoveredData.valueEq
  have frame (a : Word) (outside : OutsideChainWork a) (notCounter : a ≠ 0x80430)
      (notEndpoint : ∀ i : Fin 2, a ≠ KeygenEndpoint.endpointAddress chain.val i.val) :
      final.getMem a = s.getMem a :=
    (storeFrame a notCounter notEndpoint).trans (recoveredFrame a outside)
  refine ⟨final, ?_, finalPC, finalCounter, ?_, endpoints, finalRA.trans recoveredRA, finalSP.trans recoveredSP, frame⟩
  · convert run.trans store.trace using 1 <;> omega
  · exact data.transfer s final level tree side base message values bound (fun a outside =>
      frame a (outside_leaf_chain a outside) outside.2.2.2.2.1 (outside_leaf_endpoint a outside chain))

/-- info: 'SigGolfCandidate.Hypertree.Verifying.leaf_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms leaf_step

end SigGolfCandidate.Hypertree.Verifying
