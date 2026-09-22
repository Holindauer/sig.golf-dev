import SigGolfCandidate.Hypertree.VerifyUpperLeaf
import SigGolfCandidate.Hypertree.KeygenLeafEntry

namespace SigGolfCandidate.Hypertree.VerifyLeafPrologue
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 Keygen Signing Verifying
set_option maxRecDepth 4096

theorem entry_code : KeygenLeafEntry.Code verify 0x1460 792 := by decide

def ready (s : MachineState) : MachineState := KeygenLeafEntry.state (enterState s) 792

theorem frame (s : MachineState) (sp : s.getReg .x2 = 0xfffff0)
    (a : Word) (hs : a ≠ 0xffffe0) (hc : a ≠ 0x80430) (ht : a ≠ 0x80438) :
    (ready s).getMem a = s.getMem a := by
  unfold ready
  rw [KeygenLeafEntry.mem, if_neg ht, if_neg hc, enter_mem, sp]
  exact if_neg hs

theorem stack (s : MachineState) (sp : s.getReg .x2 = 0xfffff0) :
    (ready s).getReg .x2 = 0xffffe0 := by
  unfold ready
  rw [(KeygenLeafEntry.stack _ _).2, enter_sp, sp]
  rfl

theorem saved (s : MachineState) (sp : s.getReg .x2 = 0xfffff0) :
    (ready s).getMem 0xffffe0 = s.getReg .x1 := by
  unfold ready
  rw [KeygenLeafEntry.mem, if_neg (by decide), if_neg (by decide), enter_mem, sp, if_pos (by decide)]

theorem pc (s : MachineState) (pc : s.pc = 0x1458) (sp : s.getReg .x2 = 0xfffff0)
    (level : Nat) (nonzero : BitVec.ofNat 64 level ≠ 0) (levelEq : s.getMem 0x80400 = BitVec.ofNat 64 level) :
    (ready s).pc = 0x1490 := by
  have eq : (enterState s).getMem 0x80400 = BitVec.ofNat 64 level := by
    rw [enter_mem, sp, if_neg (by decide)]
    exact levelEq
  unfold ready
  rw [KeygenLeafEntry.pc, eq, if_neg nonzero, enter_pc, pc]
  rfl

theorem counter (s : MachineState) : (ready s).getMem 0x80430 = 0 := by
  unfold ready
  rw [KeygenLeafEntry.mem, if_neg (by decide), if_pos rfl]

theorem context (s : MachineState) (sp : s.getReg .x2 = 0xfffff0)
    (level tree : Nat) (side : Bool) (base : Nat) (message : Reference.Digest) (signature : Reference.LayerSignature)
    (data : LeafData s level tree side base message signature.values) (bound : base+736 ≤ 0x80000) :
    LeafData (ready s) level tree side base message signature.values := by
  constructor
  · rw [frame s sp _ (by decide) (by decide) (by decide)]; exact data.levelEq
  · rw [frame s sp _ (by decide) (by decide) (by decide)]; exact data.leafEq
  · rw [frame s sp _ (by decide) (by decide) (by decide)]; exact data.pointerEq
  · intro i
    rw [frame s sp _ (by fin_cases i <;> decide) (by fin_cases i <;> decide) (by fin_cases i <;> decide)]
    exact data.indexEq i
  · intro chain i
    have low : (BitVec.ofNat 64 (base+16*chain.val+8*i.val)).toNat < 0x80000 := by
      have hc := chain.isLt
      have hi := i.isLt
      change (base+16*chain.val+8*i.val) % 2^64 < 0x80000
      omega
    rw [frame s sp]
    · exact data.valueEq chain i
    · intro eq; rw [eq] at low; change 0xffffe0 < 0x80000 at low; omega
    · intro eq; rw [eq] at low; change 0x80430 < 0x80000 at low; omega
    · intro eq; rw [eq] at low; change 0x80438 < 0x80000 at low; omega
  · intro chain
    rw [getByte_word (ready s) 0x80600 chain.val (by decide) (by have := chain.isLt; omega),
      frame s sp _ (by fin_cases chain <;> decide) (by fin_cases chain <;> decide) (by fin_cases chain <;> decide),
      ← getByte_word s 0x80600 chain.val (by decide) (by have := chain.isLt; omega)]
    exact data.digitEq chain

theorem block (s : MachineState) (pc : s.pc = 0x1458) (sp : s.getReg .x2 = 0xfffff0) :
    OrdinarySteps verify s 14 (ready s) := by
  have entered := enter_block verify 0x1458 leaf_enter_code s pc (by rw [sp]; decide)
  have epc : (enterState s).pc = 0x1460 := by rw [enter_pc, pc]; rfl
  have entry := KeygenLeafEntry.block verify 0x1460 792 entry_code (enterState s) epc
  exact ordinary_trans verify _ _ _ 2 12 entered entry

end SigGolfCandidate.Hypertree.VerifyLeafPrologue
