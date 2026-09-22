import SigGolfCandidate.Hypertree.KeygenLeafCall
import SigGolfCandidate.Hypertree.KeygenTreeControl
import SigGolfCandidate.Hypertree.KeygenNodeExecution
import SigGolfCandidate.Hypertree.SignCapture

namespace SigGolfCandidate.Hypertree.KeygenTree
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 OracleComp Keygen KeygenSecretStart
set_option maxRecDepth 4096

theorem context_after_leaf (s t : MachineState) (level tree : Nat) (side : Bool) (seed : Seed)
    (ctx : Context level tree side seed s)
    (frame : ∀ a, KeygenLeafCall.Outside side a → t.getMem a=s.getMem a) :
    Context level tree side seed t := by
  constructor
  · rw [frame _ (by cases side <;> decide)]; exact ctx.levelWord
  · rw [frame _ (by cases side <;> decide)]; exact ctx.leafWord
  · intro i; rw [frame _ (by cases side <;> fin_cases i <;> decide)]; exact ctx.indexWords i
  · intro i; rw [frame _ (by cases side <;> fin_cases i <;> decide)]; exact ctx.seedWords i
  · rw [frame _ (by cases side <;> decide)]; exact ctx.modeWord

theorem control_context (s : MachineState) (old side : Bool) (jump : BitVec 21)
    (level tree : Nat) (seed : Seed) (ctx : Context level tree old seed s) :
    Context level tree side seed (KeygenTreeControl.state s (BitVec.ofNat 12 (Reference.sideNumber side)) jump) := by
  constructor
  · rw [KeygenTreeControl.mem,if_neg (by decide)]; exact ctx.levelWord
  · rw [KeygenTreeControl.mem,if_pos rfl]; cases side <;> decide
  · intro i
    rw [KeygenTreeControl.mem,if_neg (by fin_cases i <;> decide)]
    exact ctx.indexWords i
  · intro i
    rw [KeygenTreeControl.mem,if_neg (by fin_cases i <;> decide)]
    exact ctx.seedWords i
  · rw [KeygenTreeControl.mem,if_neg (by decide)]; exact ctx.modeWord

def entered (s : MachineState) : MachineState := enterState s

theorem entered_context (s : MachineState) (sp : s.getReg .x2=0x1000000)
    (level tree : Nat) (seed : Seed) (ctx : Context level tree false seed s) :
    Context level tree false seed (entered s) := by
  constructor
  · rw [entered,enter_mem,sp,if_neg (by decide)]; exact ctx.levelWord
  · rw [entered,enter_mem,sp,if_neg (by decide)]; exact ctx.leafWord
  · intro i
    rw [entered,enter_mem,sp,if_neg (by fin_cases i <;> decide)]
    exact ctx.indexWords i
  · intro i
    rw [entered,enter_mem,sp,if_neg (by fin_cases i <;> decide)]
    exact ctx.seedWords i
  · rw [entered,enter_mem,sp,if_neg (by decide)]; exact ctx.modeWord

def leftState (s : MachineState) := KeygenTreeControl.state (entered s) 0 364

theorem left_block (s : MachineState) (pc : s.pc=0x1048) (sp : s.getReg .x2=0x1000000) :
    OrdinarySteps keygen s 7 (leftState s) := by
  have entry := enter_block keygen 0x1048 keygen_tree_enter s pc (by rw [sp]; decide)
  have epc : (entered s).pc=0x1050 := by rw [entered,enter_pc,pc]; rfl
  have setup := KeygenTreeControl.block keygen 0x1050 0 364 KeygenTreeControl.left_code (entered s) epc
  exact ordinary_trans keygen _ _ _ 2 5 entry setup

theorem left_pc (s : MachineState) (pc : s.pc=0x1048) : (leftState s).pc=0x11cc := by
  rw [leftState,KeygenTreeControl.pc,entered,enter_pc,pc]; rfl

theorem left_ra (s : MachineState) (pc : s.pc=0x1048) : (leftState s).getReg .x1=0x1064 := by
  rw [leftState,KeygenTreeControl.ra,entered,enter_pc,pc]; rfl

theorem left_sp (s : MachineState) (sp : s.getReg .x2=0x1000000) : (leftState s).getReg .x2=0xfffff0 := by
  rw [leftState,KeygenTreeControl.sp,entered,enter_sp,sp]; rfl

theorem left_saved (s : MachineState) (sp : s.getReg .x2=0x1000000) :
    (leftState s).getMem 0xfffff0=s.getReg .x1 := by
  rw [leftState,KeygenTreeControl.mem,if_neg (by decide),entered,enter_mem,sp,if_pos (by decide)]

theorem left_context (s : MachineState) (sp : s.getReg .x2=0x1000000)
    (level tree : Nat) (seed : Seed) (ctx : Context level tree false seed s) :
    Context level tree false seed (leftState s) :=
  control_context (entered s) false false 364 level tree seed (entered_context s sp level tree seed ctx)

theorem start (s : MachineState) (pc : s.pc=0x1048) (sp : s.getReg .x2=0x1000000)
    (level tree : Nat) (seed : Seed) (ctx : Context level tree false seed s) :
    ∃ ready, OrdinarySteps keygen s 7 ready ∧ ready.pc=0x11cc ∧ ready.getReg .x1=0x1064 ∧
      ready.getReg .x2=0xfffff0 ∧ ready.getMem 0xfffff0=s.getReg .x1 ∧ Context level tree false seed ready := by
  exact ⟨leftState s,left_block s pc sp,left_pc s pc,left_ra s pc,left_sp s sp,left_saved s sp,left_context s sp level tree seed ctx⟩

theorem skip_code : Signing.captureModeCode keygen 0x1078 92 := by
  intro s i pc
  simp only [fetch,pc]
  fin_cases i <;> decide

end SigGolfCandidate.Hypertree.KeygenTree
