import SigGolfCandidate.Hypertree.SignBottomLeaf
import SigGolfCandidate.Hypertree.KeygenLeafEntry

namespace SigGolfCandidate.Hypertree.Signing
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 Keygen Verifying
set_option maxRecDepth 4096

structure LeafContext (s : MachineState) (secretKey : SecretKey) (level tree : Nat) (side : Bool) : Prop where
  levelEq : s.getMem 0x80400 = BitVec.ofNat 64 level
  leafEq : s.getMem 0x80428 = BitVec.ofNat 64 (Reference.sideNumber side)
  indexEq : ∀ i : Fin 3, s.getMem (wordAddress 0x80408 i.val) = (BitVec.ofNat 192 tree).extractLsb' (64*i.val) 64
  secretKeyEq : ∀ i : Fin 4, s.getMem (wordAddress 0x20 i.val) = secretKey.extractLsb' (64*i.val) 64

theorem sign_leaf_entry_code : KeygenLeafEntry.Code sign 0x1554 1116 := by decide

def leafReady (s : MachineState) : MachineState := KeygenLeafEntry.state (enterState s) 1116

theorem leafReady_frame (s : MachineState) (sp : s.getReg .x2 = 0xfffff0)
    (a : Word) (hs : a ≠ 0xffffe0) (hc : a ≠ 0x80430) (ht : a ≠ 0x80438) :
    (leafReady s).getMem a = s.getMem a := by
  unfold leafReady
  rw [KeygenLeafEntry.mem, if_neg ht, if_neg hc, enter_mem, sp]
  exact if_neg hs

theorem leafReady_sp (s : MachineState) (sp : s.getReg .x2 = 0xfffff0) :
    (leafReady s).getReg .x2 = 0xffffe0 := by
  rw [leafReady, (KeygenLeafEntry.stack _ _).2, enter_sp, sp]; rfl

theorem leafReady_saved (s : MachineState) (sp : s.getReg .x2 = 0xfffff0) :
    (leafReady s).getMem 0xffffe0 = s.getReg .x1 := by
  rw [leafReady, KeygenLeafEntry.mem, if_neg (by decide), if_neg (by decide), enter_mem, sp, if_pos (by decide)]

theorem leafReady_step (s : MachineState) : (leafReady s).getMem 0x80438 = 0 := by
  rw [leafReady, KeygenLeafEntry.mem, if_pos rfl]

theorem leafReady_pc (s : MachineState) (pc : s.pc = 0x154c) (sp : s.getReg .x2 = 0xfffff0) :
    (leafReady s).pc = if s.getMem 0x80400 = 0 then 0x19dc else 0x1584 := by
  have level : (enterState s).getMem 0x80400 = s.getMem 0x80400 := by
    rw [enter_mem, sp, if_neg (by decide)]
  rw [leafReady, KeygenLeafEntry.pc, level, enter_pc, pc]
  split <;> rfl

theorem leafReady_block (s : MachineState) (pc : s.pc = 0x154c) (sp : s.getReg .x2 = 0xfffff0) :
    OrdinarySteps sign s 14 (leafReady s) := by
  have entered := enter_block sign 0x154c sign_leaf_enter_code s pc (by rw [sp]; decide)
  have epc : (enterState s).pc = 0x1554 := by rw [enter_pc, pc]; rfl
  have entry := KeygenLeafEntry.block sign 0x1554 1116 sign_leaf_entry_code (enterState s) epc
  exact ordinary_trans sign _ _ _ 2 12 entered entry

theorem leafReady_data (s : MachineState) (secretKey : SecretKey) (level tree : Nat) (side : Bool)
    (sp : s.getReg .x2 = 0xfffff0) (data : LeafContext s secretKey level tree side) :
    LeafData (leafReady s) secretKey level tree side 0 := by
  constructor
  · rw [leafReady_frame s sp _ (by decide) (by decide) (by decide)]; exact data.levelEq
  · rw [leafReady_frame s sp _ (by decide) (by decide) (by decide)]; exact data.leafEq
  · rw [leafReady, KeygenLeafEntry.mem, if_neg (by decide), if_pos rfl]; rfl
  · intro i
    rw [leafReady_frame s sp _ (by fin_cases i <;> decide) (by fin_cases i <;> decide) (by fin_cases i <;> decide)]
    exact data.indexEq i
  · intro i
    rw [leafReady_frame s sp _ (by fin_cases i <;> decide) (by fin_cases i <;> decide) (by fin_cases i <;> decide)]
    exact data.secretKeyEq i

theorem leafReady_settings (s : MachineState) (pointer : Nat) (message : Reference.Digest)
    (sp : s.getReg .x2 = 0xfffff0) (settings : LeafSignatureSettings s pointer message) :
    LeafSignatureSettings (leafReady s) pointer message := by
  intro chain
  constructor
  · rw [leafReady_frame s sp _ (by decide) (by decide) (by decide)]; exact (settings chain).pointerEq
  · rw [leafReady_frame s sp _ (by decide) (by decide) (by decide)]; exact (settings chain).enabled
  · rw [leafReady_frame s sp _ (by decide) (by decide) (by decide), leafReady_frame s sp _ (by decide) (by decide) (by decide)]
    exact (settings chain).selected
  · have bound := chain.isLt
    rw [getByte_word (leafReady s) 0x80600 chain.val (by decide) (by omega)]
    rw [leafReady_frame]
    · rw [← getByte_word s 0x80600 chain.val (by decide) (by omega)]
      exact (settings chain).digitEq
    · exact sp
    all_goals intro eq
    all_goals have h := congrArg BitVec.toNat eq
    all_goals simp [wordAddress] at h
    all_goals omega

theorem leafReady_low_frame (s : MachineState) (sp : s.getReg .x2 = 0xfffff0)
    (a : Word) (low : a.toNat < 0x80000) : (leafReady s).getMem a = s.getMem a := by
  apply leafReady_frame s sp a
  all_goals intro eq
  all_goals have h := congrArg BitVec.toNat eq
  all_goals simp at h
  all_goals omega

end SigGolfCandidate.Hypertree.Signing
