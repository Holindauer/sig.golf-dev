import SigGolfCandidate.Hypertree.KeygenVerifyBottomPrologue

namespace SigGolfCandidate.Hypertree.KeygenVerifyBottom
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 Keygen Signing
set_option maxRecDepth 4096

theorem hash_code : SignBottomHash.Code verify 0x17d0 := by decide
theorem return_code : ReturnCode verify 0x18fc := by decide

theorem load_safe (s : MachineState) (base : Nat)
    (pointer : s.getMem 0x80448 = BitVec.ofNat 64 base)
    (aligned : base % 8 = 0) (bound : base+16 ≤ 0x80000) :
    accessValid (s.getMem 0x80448) 8 = true ∧ accessValid (s.getMem 0x80448+8) 8 = true := by
  rw [pointer, show BitVec.ofNat 64 base + 8 = BitVec.ofNat 64 (base+8) from (BitVec.ofNat_add _ _).symm]
  have small : base < 2^64 := by omega
  have smallNext : base+8 < 2^64 := by omega
  simp [accessValid, rangeValid, BitVec.toNat_ofNat, Nat.add_mod, aligned, MEMORY_BYTES]
  omega

theorem load_value (s : MachineState) (tree : Nat) (side : Bool) (base : Nat) (value : Reference.Digest)
    (data : Data s tree side base value) (i : Fin 2) :
    (KeygenVerifyBottomLoad.state s).getMem (wordAddress 0x80510 i.val) = value.extractLsb' (64*i.val) 64 := by
  fin_cases i
  · rw [KeygenVerifyBottomLoad.mem, if_neg (by decide), if_pos (by decide), data.pointerEq]
    exact data.valueEq 0
  · rw [KeygenVerifyBottomLoad.mem, if_pos (by decide), data.pointerEq]
    simpa [wordAddress, BitVec.ofNat_add] using data.valueEq 1

theorem body (hash : Hash) (s : MachineState) (tree : Nat) (side : Bool) (base : Nat) (value : Reference.Digest)
    (pc : s.pc = 0x17a4) (sp : s.getReg .x2 = 0xffffe0)
    (data : Data s tree side base value) (chain : s.getMem 0x80430 = 0) (step : s.getMem 0x80438 = 0)
    (aligned : base % 8 = 0) (bound : base+16 ≤ 0x80000) :
    ∃ final, Trace hash verify s 95 102 1 1 final ∧
      final.pc = s.getMem 0xffffe0 &&& ~~~1#64 ∧ final.getReg .x2 = 0xfffff0 ∧
      (∀ i : Fin 2, final.getMem (KeygenSavePublic.wordAddress side i.val) =
        (Reference.chainHash hash 0 tree side 0 0 value).extractLsb' (64*i.val) 64) ∧
      (∀ a, OutsideBottomWork side a → final.getMem a = s.getMem a) := by
  have safe := load_safe s base data.pointerEq aligned bound
  have pre := KeygenVerifyBottomLoad.block verify 0x17a4 KeygenVerifyBottomLoad.code s pc safe.1 safe.2
  let loaded := KeygenVerifyBottomLoad.state s
  have loadedPC : loaded.pc = 0x17d0 := by rw [KeygenVerifyBottomLoad.pc, pc]; rfl
  have keep (a : Word) (h0 : a ≠ 0x80510) (h1 : a ≠ 0x80518) : loaded.getMem a = s.getMem a := by
    rw [KeygenVerifyBottomLoad.mem, if_neg h1, if_neg h0]
  have levelEq : loaded.getMem 0x80400 = BitVec.ofNat 64 0 := by
    rw [keep _ (by decide) (by decide)]; exact data.levelEq
  have leafEq : loaded.getMem 0x80428 = BitVec.ofNat 64 (Reference.sideNumber side) := by
    rw [keep _ (by decide) (by decide)]; exact data.leafEq
  have chainEq : loaded.getMem 0x80430 = BitVec.ofNat 64 (0 : Reference.Chain).val := by
    rw [keep _ (by decide) (by decide)]; exact chain
  have stepEq : loaded.getMem 0x80438 = BitVec.ofNat 64 0 := by
    rw [keep _ (by decide) (by decide)]; exact step
  have indexEq : ∀ i : Fin 3, loaded.getMem (wordAddress 0x80408 i.val) = (BitVec.ofNat 192 tree).extractLsb' (64*i.val) 64 := by
    intro i
    rw [keep _ (by fin_cases i <;> decide) (by fin_cases i <;> decide)]
    exact data.indexEq i
  obtain ⟨hashed, core, hashedPC, root, hashedRA, hashedSP, hashedFrame⟩ :=
    SignBottomHash.compute verify hash 0x17d0 hash_code loaded loadedPC 0 tree 0 side 0 value
      levelEq leafEq chainEq stepEq indexEq (load_value s tree side base value data)
  have loadedSP : loaded.getReg .x2 = 0xffffe0 := (KeygenVerifyBottomLoad.stack s).2.trans sp
  have ret := return_block verify 0x18fc return_code hashed hashedPC (by rw [hashedSP, loadedSP]; decide)
  have frame (a : Word) (outside : OutsideBottomWork side a) : (returnState hashed).getMem a = s.getMem a := by
    rw [return_mem, hashedFrame a (fun i => outside.1 ⟨i.val, by omega⟩) outside.2.1 outside.2.2.2]
    exact keep a (outside.2.2.1 0) (outside.2.2.1 1)
  refine ⟨returnState hashed, pre.trace.trans (core.trans ret.trace), ?_, ?_, ?_, frame⟩
  · rw [return_pc, hashedSP, loadedSP]
    have eq := frame 0xffffe0 (by unfold OutsideBottomWork; cases side <;> decide)
    rw [return_mem] at eq
    rw [eq]
  · rw [return_sp, hashedSP, loadedSP]; rfl
  · intro i; rw [return_mem]; exact root i

/-- Complete protected verifier bottom-leaf call with its exact resource counts. -/
theorem call (hash : Hash) (s : MachineState) (tree : Nat) (side : Bool) (base : Nat)
    (message : Reference.Digest) (signature : Reference.LayerSignature)
    (pc : s.pc = 0x1458) (sp : s.getReg .x2 = 0xfffff0)
    (data : Data s tree side base (signature.values 0))
    (aligned : base % 8 = 0) (bound : base+16 ≤ 0x80000) :
    ∃ final, Trace hash verify s 109 116 1 1 final ∧
      final.pc = s.getReg .x1 &&& ~~~1#64 ∧ final.getReg .x2 = s.getReg .x2 ∧
      (∀ i : Fin 2, final.getMem (KeygenSavePublic.wordAddress side i.val) =
        (Reference.recoverLeaf hash 0 tree side message signature).extractLsb' (64*i.val) 64) ∧
      (∀ a, a ≠ 0xffffe0 → a ≠ 0x80430 → a ≠ 0x80438 → OutsideBottomWork side a →
        final.getMem a = s.getMem a) := by
  obtain ⟨ready, pre, rpc, rdata, counter, step, rsp, saved, preFrame⟩ :=
    prepare hash s tree side base (signature.values 0) pc sp data bound
  obtain ⟨final, run, finalPC, finalSP, output, frame⟩ :=
    body hash ready tree side base (signature.values 0) rpc rsp rdata counter step aligned bound
  refine ⟨final, pre.trans run, ?_, ?_, ?_, ?_⟩
  · rw [finalPC, saved]
  · rw [finalSP, sp]
  · exact output
  · intro a hs hc ht outside
    rw [frame a outside, preFrame a hs hc ht]

/-- info: 'SigGolfCandidate.Hypertree.KeygenVerifyBottom.call' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms call

end SigGolfCandidate.Hypertree.KeygenVerifyBottom
