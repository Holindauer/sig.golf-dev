import SigGolfCandidate.Hypertree.VerifySibling
import SigGolfCandidate.Hypertree.KeygenSavePublic

namespace SigGolfCandidate.Hypertree.Verifying
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 Keygen Signing
set_option maxRecDepth 4096

/-- The location following this layer's one or 46 disclosed chain values. -/
def siblingOffset (level : Nat) : Nat := if level = 0 then 16 else 736

theorem sibling_source (s : MachineState) (side : Bool)
    (selector : s.getMem 0x80420 = BitVec.ofNat 64 (Reference.sideNumber side)) :
    siblingSource s = KeygenSavePublic.wordAddress (!side) 0 := by
  rw [siblingSource, selector]
  cases side <;> rfl

theorem sibling_destination (s : MachineState) (level base : Nat) (small : level < 160)
    (levelEq : s.getMem 0x80400 = BitVec.ofNat 64 level)
    (pointer : s.getMem 0x80448 = BitVec.ofNat 64 base) :
    siblingDestination s = BitVec.ofNat 64 (base+siblingOffset level) := by
  have zero : BitVec.ofNat 64 level = 0 ↔ level = 0 := by
    constructor
    · intro eq
      have h := congrArg BitVec.toNat eq
      change level % 2^64 = 0 at h
      omega
    · intro eq; rw [eq]; rfl
  simp only [siblingDestination, levelEq, pointer, zero, siblingOffset]
  split <;> simp only [BitVec.ofNat_add] <;> rfl

theorem sibling_access (s : MachineState) (level base : Nat) (side : Bool)
    (small : level < 160) (aligned : base % 8 = 0) (bound : base+752 ≤ 0x80000)
    (levelEq : s.getMem 0x80400 = BitVec.ofNat 64 level)
    (pointer : s.getMem 0x80448 = BitVec.ofNat 64 base)
    (selector : s.getMem 0x80420 = BitVec.ofNat 64 (Reference.sideNumber side)) :
    accessValid (siblingDestination s) 8 = true ∧
    accessValid (siblingDestination s+8) 8 = true ∧
    accessValid (siblingSource s) 8 = true ∧
    accessValid (siblingSource s+8) 8 = true := by
  rw [sibling_destination s level base small levelEq pointer, sibling_source s side selector]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [siblingOffset]
    split <;> simp [accessValid, rangeValid, MEMORY_BYTES, BitVec.toNat_ofNat, Nat.add_mod, aligned] <;> omega
  · change accessValid (BitVec.ofNat 64 (base+siblingOffset level) + BitVec.ofNat 64 8) 8 = true
    rw [← BitVec.ofNat_add]
    simp only [siblingOffset]
    split <;>
      simp [accessValid, rangeValid, MEMORY_BYTES, BitVec.toNat_ofNat, Nat.add_mod, aligned] <;> omega
  · cases side <;> decide
  · cases side <;> decide

theorem sibling_loaded_frame (s : MachineState) (side : Bool)
    (selector : s.getMem 0x80420 = BitVec.ofNat 64 (Reference.sideNumber side))
    (a : Word) (outside : ∀ i : Fin 2, a ≠ KeygenSavePublic.wordAddress (!side) i.val) :
    (siblingLoaded s).getMem a = s.getMem a := by
  rw [siblingLoaded_mem, sibling_source s side selector]
  have h0 : a ≠ KeygenSavePublic.wordAddress (!side) 0 := outside 0
  have h1 : a ≠ KeygenSavePublic.wordAddress (!side) 0+8 := by
    simpa [KeygenSavePublic.wordAddress, wordAddress, BitVec.ofNat_add, BitVec.add_assoc] using outside 1
  rw [if_neg h1, if_neg h0]

theorem sibling_loaded_children (s : MachineState) (level base : Nat) (side : Bool)
    (current sibling : Reference.Digest)
    (small : level < 160)
    (levelEq : s.getMem 0x80400 = BitVec.ofNat 64 level)
    (pointer : s.getMem 0x80448 = BitVec.ofNat 64 base)
    (selector : s.getMem 0x80420 = BitVec.ofNat 64 (Reference.sideNumber side))
    (leaf : ∀ i : Fin 2, s.getMem (KeygenSavePublic.wordAddress side i.val) = current.extractLsb' (64*i.val) 64)
    (witness : ∀ i : Fin 2, s.getMem (BitVec.ofNat 64 (base+siblingOffset level+8*i.val)) = sibling.extractLsb' (64*i.val) 64) :
    ∀ i : Fin 4, (siblingLoaded s).getMem (wordAddress 0x80520 i.val) =
      if i.val < 2 then (if side then sibling else current).extractLsb' (64*i.val) 64
      else (if side then current else sibling).extractLsb' (64*(i.val-2)) 64 := by
  intro i
  rw [siblingLoaded_mem, sibling_source s side selector,
    sibling_destination s level base small levelEq pointer]
  have l0 := leaf 0
  have l1 := leaf 1
  have w0 := witness 0
  have w1 := witness 1
  cases side <;> fin_cases i <;>
    simpa [KeygenSavePublic.wordAddress, wordAddress, Reference.sideNumber, ← BitVec.ofNat_add] using (by first | exact l0 | exact l1 | exact w0 | exact w1)

end SigGolfCandidate.Hypertree.Verifying
