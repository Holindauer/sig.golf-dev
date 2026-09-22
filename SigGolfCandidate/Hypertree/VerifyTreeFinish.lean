import SigGolfCandidate.Hypertree.VerifySiblingRefine

namespace SigGolfCandidate.Hypertree.Verifying
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 Keygen Signing
set_option maxRecDepth 4096

/-- Memory unaffected by the sibling load and parent hash. -/
def OutsideParentWork (side : Bool) (a : Word) : Prop :=
  (∀ i : Fin 8, a ≠ wordAddress 0x80000 i.val) ∧
  (∀ i : Fin 4, a ≠ wordAddress 0x80300 i.val) ∧
  (∀ i : Fin 2, a ≠ wordAddress 0x80500 i.val) ∧
  (∀ i : Fin 2, a ≠ KeygenSavePublic.wordAddress (!side) i.val)

/-- The real sibling load, parent hash, and protected return recover one witness layer. -/
theorem finish_tree (hash : Hash) (s : MachineState) (level tree base : Nat) (side : Bool)
    (message : Reference.Digest) (signature : Reference.LayerSignature)
    (pc : s.pc = 0x1314) (sp : s.getReg .x2 = 0xfffff0)
    (small : level < 160) (aligned : base % 8 = 0) (bound : base+752 ≤ 0x80000)
    (levelEq : s.getMem 0x80400 = BitVec.ofNat 64 level)
    (indexEq : ∀ i : Fin 3, s.getMem (wordAddress 0x80408 i.val) =
      (BitVec.ofNat 192 tree).extractLsb' (64*i.val) 64)
    (pointer : s.getMem 0x80448 = BitVec.ofNat 64 base)
    (selector : s.getMem 0x80420 = BitVec.ofNat 64 (Reference.sideNumber side))
    (leaf : ∀ i : Fin 2, s.getMem (KeygenSavePublic.wordAddress side i.val) =
      (Reference.recoverLeaf hash level tree side message signature).extractLsb' (64*i.val) 64)
    (witness : ∀ i : Fin 2, s.getMem (BitVec.ofNat 64 (base+siblingOffset level+8*i.val)) =
      signature.sibling.extractLsb' (64*i.val) 64) :
    ∃ final steps cycles, Trace hash verify s steps cycles 1 1 final ∧
      steps ≤ 104 ∧ cycles ≤ 111 ∧ final.pc = s.getMem 0xfffff0 &&& ~~~1#64 ∧
      final.getReg .x2 = 0x1000000 ∧
      (∀ i : Fin 2, final.getMem (wordAddress 0x80500 i.val) =
        (Reference.recoverLayer hash level tree side message signature).extractLsb' (64*i.val) 64) ∧
      (∀ a, OutsideParentWork side a → final.getMem a = s.getMem a) := by
  obtain ⟨src, srcNext, dst, dstNext⟩ := sibling_access s level base side small aligned bound levelEq pointer selector
  have pre := load_sibling s pc src srcNext dst dstNext
  have child := sibling_loaded_children s level base side _ signature.sibling small levelEq pointer selector leaf witness
  have frame := sibling_loaded_frame s side selector
  have loadedLevel : (siblingLoaded s).getMem 0x80400 = BitVec.ofNat 64 level := by
    rw [frame _ (by cases side <;> decide)]
    exact levelEq
  have loadedIndex : ∀ i : Fin 3, (siblingLoaded s).getMem (wordAddress 0x80408 i.val) =
      (BitVec.ofNat 192 tree).extractLsb' (64*i.val) 64 := by
    intro i
    rw [frame _ (by cases side <;> fin_cases i <;> decide)]
    exact indexEq i
  have loadedSP : (siblingLoaded s).getReg .x2 = 0xfffff0 := (siblingLoaded_sp s).trans sp
  obtain ⟨final, post, fpc, fsp, current, out⟩ := KeygenNode.compute_return verify hash 0x136c
    node_body_code node_return_code (siblingLoaded s) (siblingLoaded_pc s pc) level tree _ _
    loadedLevel loadedIndex child
    (by rw [loadedSP]; decide)
    (by rw [loadedSP]; decide)
    (by rw [loadedSP]; decide)
    (by rw [loadedSP]; decide)
  let n := if s.getMem 0x80400 = 0 then 20 else 21
  refine ⟨final, n+83, n+90, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [Nat.zero_add] using pre.trace.trans post
  · dsimp [n]; split <;> decide
  · dsimp [n]; split <;> decide
  · rw [fpc, loadedSP, frame _ (by cases side <;> decide)]
  · rw [fsp, loadedSP]; rfl
  · intro i
    have value := current i
    cases side <;> simpa only [Reference.recoverLayer, Bool.false_eq_true, if_false, if_true] using value
  · intro a outside
    rw [out a outside.1 outside.2.1 outside.2.2.1, frame a outside.2.2.2]

/-- info: 'SigGolfCandidate.Hypertree.Verifying.finish_tree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms finish_tree

end SigGolfCandidate.Hypertree.Verifying
