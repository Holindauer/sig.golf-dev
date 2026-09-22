import SigGolfCandidate.Hypertree.VerifyLeafPrologue
import SigGolfCandidate.Hypertree.KeygenVerifyBottomLoad
import SigGolfCandidate.Hypertree.SignBottomFrame

namespace SigGolfCandidate.Hypertree.KeygenVerifyBottom
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 Keygen Signing
set_option maxRecDepth 4096

structure Data (s : MachineState) (tree : Nat) (side : Bool) (base : Nat) (value : Reference.Digest) : Prop where
  levelEq : s.getMem 0x80400 = 0
  leafEq : s.getMem 0x80428 = BitVec.ofNat 64 (Reference.sideNumber side)
  pointerEq : s.getMem 0x80448 = BitVec.ofNat 64 base
  indexEq : ∀ i : Fin 3, s.getMem (wordAddress 0x80408 i.val) = (BitVec.ofNat 192 tree).extractLsb' (64*i.val) 64
  valueEq : ∀ i : Fin 2, s.getMem (wordAddress base i.val) = value.extractLsb' (64*i.val) 64

theorem prologue_pc (s : MachineState) (pc : s.pc = 0x1458) (sp : s.getReg .x2 = 0xfffff0)
    (level : s.getMem 0x80400 = 0) : (VerifyLeafPrologue.ready s).pc = 0x17a4 := by
  have eq : (enterState s).getMem 0x80400 = 0 := by
    rw [enter_mem, sp, if_neg (by decide)]; exact level
  unfold VerifyLeafPrologue.ready
  rw [KeygenLeafEntry.pc, eq, if_pos rfl, enter_pc, pc]
  rfl

theorem prologue_step (s : MachineState) : (VerifyLeafPrologue.ready s).getMem 0x80438 = 0 := by
  unfold VerifyLeafPrologue.ready
  rw [KeygenLeafEntry.mem, if_pos rfl]

theorem prologue_data (s : MachineState) (tree : Nat) (side : Bool) (base : Nat) (value : Reference.Digest)
    (sp : s.getReg .x2 = 0xfffff0) (data : Data s tree side base value) (bound : base+16 ≤ 0x80000) :
    Data (VerifyLeafPrologue.ready s) tree side base value := by
  constructor
  · rw [VerifyLeafPrologue.frame s sp _ (by decide) (by decide) (by decide)]; exact data.levelEq
  · rw [VerifyLeafPrologue.frame s sp _ (by decide) (by decide) (by decide)]; exact data.leafEq
  · rw [VerifyLeafPrologue.frame s sp _ (by decide) (by decide) (by decide)]; exact data.pointerEq
  · intro i
    rw [VerifyLeafPrologue.frame s sp _ (by fin_cases i <;> decide) (by fin_cases i <;> decide) (by fin_cases i <;> decide)]
    exact data.indexEq i
  · intro i
    have low : (wordAddress base i.val).toNat < 0x80000 := by
      have hi := i.isLt
      change (base+8*i.val) % 2^64 < 0x80000
      omega
    rw [VerifyLeafPrologue.frame s sp]
    · exact data.valueEq i
    all_goals intro eq; rw [eq] at low
    · change 0xffffe0 < 0x80000 at low; omega
    · change 0x80430 < 0x80000 at low; omega
    · change 0x80438 < 0x80000 at low; omega

theorem prepare (hash : Hash) (s : MachineState) (tree : Nat) (side : Bool) (base : Nat) (value : Reference.Digest)
    (pc : s.pc = 0x1458) (sp : s.getReg .x2 = 0xfffff0)
    (data : Data s tree side base value) (bound : base+16 ≤ 0x80000) :
    ∃ ready, Trace hash verify s 14 14 0 0 ready ∧ ready.pc = 0x17a4 ∧
      Data ready tree side base value ∧ ready.getMem 0x80430 = 0 ∧ ready.getMem 0x80438 = 0 ∧
      ready.getReg .x2 = 0xffffe0 ∧ ready.getMem 0xffffe0 = s.getReg .x1 ∧
      (∀ a, a ≠ 0xffffe0 → a ≠ 0x80430 → a ≠ 0x80438 → ready.getMem a = s.getMem a) := by
  exact ⟨VerifyLeafPrologue.ready s, (VerifyLeafPrologue.block s pc sp).trace,
    prologue_pc s pc sp data.levelEq, prologue_data s tree side base value sp data bound,
    VerifyLeafPrologue.counter s, prologue_step s, VerifyLeafPrologue.stack s sp,
    VerifyLeafPrologue.saved s sp, VerifyLeafPrologue.frame s sp⟩

end SigGolfCandidate.Hypertree.KeygenVerifyBottom
