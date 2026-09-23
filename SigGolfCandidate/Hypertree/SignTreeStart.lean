import SigGolfCandidate.Hypertree.SignTreeHelpers

namespace SigGolfCandidate.Hypertree.Signing
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 Keygen Verifying
set_option maxRecDepth 4096

/-- The tree entry saves its caller and selects the left leaf before calling it. -/
def treeLeftState (s : MachineState) : MachineState := KeygenTreeControl.state (enterState s) 0 364

theorem treeLeft_frame (s : MachineState) (sp : s.getReg .x2 = 0x1000000)
    (a : Word) (stack : a ≠ 0xfffff0) (leaf : a ≠ 0x80428) :
    (treeLeftState s).getMem a = s.getMem a := by
  rw [treeLeftState, KeygenTreeControl.mem, if_neg leaf, enter_mem, sp, if_neg (by simpa using stack)]

theorem treeLeft_block (s : MachineState) (pc : s.pc = 0x13c8) (sp : s.getReg .x2 = 0x1000000) :
    OrdinarySteps sign s 7 (treeLeftState s) := by
  have enter := enter_block sign 0x13c8 sign_tree_enter_code s pc (by rw [sp]; decide)
  have epc : (enterState s).pc = 0x13d0 := by rw [enter_pc, pc]; rfl
  have call := KeygenTreeControl.block sign 0x13d0 0 364 sign_tree_left_code (enterState s) epc
  exact ordinary_trans sign s _ _ 2 5 enter call

theorem treeLeft_pc (s : MachineState) (pc : s.pc = 0x13c8) : (treeLeftState s).pc = 0x154c := by
  rw [treeLeftState, KeygenTreeControl.pc, enter_pc, pc]; rfl

theorem treeLeft_ra (s : MachineState) (pc : s.pc = 0x13c8) : (treeLeftState s).getReg .x1 = 0x13e4 := by
  rw [treeLeftState, KeygenTreeControl.ra, enter_pc, pc]; rfl

theorem treeLeft_sp (s : MachineState) (sp : s.getReg .x2 = 0x1000000) : (treeLeftState s).getReg .x2 = 0xfffff0 := by
  rw [treeLeftState, KeygenTreeControl.sp, enter_sp, sp]; rfl

theorem treeLeft_saved (s : MachineState) (sp : s.getReg .x2 = 0x1000000) :
    (treeLeftState s).getMem 0xfffff0 = s.getReg .x1 := by
  rw [treeLeftState, KeygenTreeControl.mem, if_neg (by decide), enter_mem, sp, if_pos (by decide)]

theorem treeLeft_context (s : MachineState) (secretKey : SecretKey) (level tree : Nat)
    (sp : s.getReg .x2 = 0x1000000) (data : TreeContext s secretKey level tree) :
    LeafContext (treeLeftState s) secretKey level tree false := by
  constructor
  · rw [treeLeft_frame s sp _ (by decide) (by decide)]; exact data.levelEq
  · rw [treeLeftState, KeygenTreeControl.mem, if_pos rfl]; rfl
  · intro i
    rw [treeLeft_frame s sp _ (by fin_cases i <;> decide) (by fin_cases i <;> decide)]
    exact data.indexEq i
  · intro i
    rw [treeLeft_frame s sp _ (by fin_cases i <;> decide) (by fin_cases i <;> decide)]
    exact data.secretKeyEq i

theorem treeLeft_settings (s : MachineState) (pointer : Nat) (message : Reference.Digest) (selected : Bool)
    (sp : s.getReg .x2 = 0x1000000) (settings : TreeSettings s pointer message selected) :
    TreeSettings (treeLeftState s) pointer message selected := by
  constructor
  · rw [treeLeft_frame s sp _ (by decide) (by decide)]; exact settings.pointerEq
  · rw [treeLeft_frame s sp _ (by decide) (by decide)]; exact settings.enabled
  · rw [treeLeft_frame s sp _ (by decide) (by decide)]; exact settings.selectorEq
  · intro chain
    have cb := chain.isLt
    rw [getByte_word _ 0x80600 chain.val (by decide) (by omega), treeLeft_frame]
    · rw [← getByte_word s 0x80600 chain.val (by decide) (by omega)]
      exact settings.digits chain
    · exact sp
    all_goals intro eq
    all_goals have h := congrArg BitVec.toNat eq
    all_goals simp [wordAddress] at h
    all_goals omega

end SigGolfCandidate.Hypertree.Signing
