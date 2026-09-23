import SigGolfCandidate.Hypertree.KeygenLeafCall
import SigGolfCandidate.Hypertree.KeygenTreeControl
import SigGolfCandidate.Hypertree.KeygenNodeExecution
import SigGolfCandidate.Hypertree.SignCapture

namespace SigGolfCandidate.Hypertree.KeygenTree
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 OracleComp Keygen KeygenSecretStart
set_option maxRecDepth 4096

theorem context_after_leaf (s t : MachineState) (level tree : Nat) (side : Bool) (secretKey : SecretKey)
    (ctx : Context level tree side secretKey s)
    (frame : ∀ a, KeygenLeafCall.Outside side a → t.getMem a=s.getMem a) :
    Context level tree side secretKey t := by
  constructor
  · rw [frame _ (by cases side <;> decide)]; exact ctx.levelWord
  · rw [frame _ (by cases side <;> decide)]; exact ctx.leafWord
  · intro i; rw [frame _ (by cases side <;> fin_cases i <;> decide)]; exact ctx.indexWords i
  · intro i; rw [frame _ (by cases side <;> fin_cases i <;> decide)]; exact ctx.secretKeyWords i
  · rw [frame _ (by cases side <;> decide)]; exact ctx.modeWord

theorem control_context (s : MachineState) (old side : Bool) (jump : BitVec 21)
    (level tree : Nat) (secretKey : SecretKey) (ctx : Context level tree old secretKey s) :
    Context level tree side secretKey (KeygenTreeControl.state s (BitVec.ofNat 12 (Reference.sideNumber side)) jump) := by
  constructor
  · rw [KeygenTreeControl.mem,if_neg (by decide)]; exact ctx.levelWord
  · rw [KeygenTreeControl.mem,if_pos rfl]; cases side <;> decide
  · intro i
    rw [KeygenTreeControl.mem,if_neg (by fin_cases i <;> decide)]
    exact ctx.indexWords i
  · intro i
    rw [KeygenTreeControl.mem,if_neg (by fin_cases i <;> decide)]
    exact ctx.secretKeyWords i
  · rw [KeygenTreeControl.mem,if_neg (by decide)]; exact ctx.modeWord

def entered (s : MachineState) : MachineState := enterState s

theorem entered_context (s : MachineState) (sp : s.getReg .x2=0x1000000)
    (level tree : Nat) (secretKey : SecretKey) (ctx : Context level tree false secretKey s) :
    Context level tree false secretKey (entered s) := by
  constructor
  · rw [entered,enter_mem,sp,if_neg (by decide)]; exact ctx.levelWord
  · rw [entered,enter_mem,sp,if_neg (by decide)]; exact ctx.leafWord
  · intro i
    rw [entered,enter_mem,sp,if_neg (by fin_cases i <;> decide)]
    exact ctx.indexWords i
  · intro i
    rw [entered,enter_mem,sp,if_neg (by fin_cases i <;> decide)]
    exact ctx.secretKeyWords i
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
    (level tree : Nat) (secretKey : SecretKey) (ctx : Context level tree false secretKey s) :
    Context level tree false secretKey (leftState s) :=
  control_context (entered s) false false 364 level tree secretKey (entered_context s sp level tree secretKey ctx)

theorem start (s : MachineState) (pc : s.pc=0x1048) (sp : s.getReg .x2=0x1000000)
    (level tree : Nat) (secretKey : SecretKey) (ctx : Context level tree false secretKey s) :
    ∃ ready, OrdinarySteps keygen s 7 ready ∧ ready.pc=0x11cc ∧ ready.getReg .x1=0x1064 ∧
      ready.getReg .x2=0xfffff0 ∧ ready.getMem 0xfffff0=s.getReg .x1 ∧ Context level tree false secretKey ready := by
  exact ⟨leftState s,left_block s pc sp,left_pc s pc,left_ra s pc,left_sp s sp,left_saved s sp,left_context s sp level tree secretKey ctx⟩

theorem skip_code : Signing.captureModeCode keygen 0x1078 92 := by
  intro s i pc
  simp only [fetch,pc]
  fin_cases i <;> decide

theorem low_ne_word (a : Word) (low : a.toNat < 0x80000)
    (base n : Nat) (lower : 0x80000 ≤ base) (upper : base+8*n < 2^64) (i : Fin n) :
    a ≠ Signing.wordAddress base i.val := by
  intro eq
  have h := congrArg BitVec.toNat eq
  have hi := i.isLt
  change a.toNat = (base+8*i.val)%2^64 at h
  omega

theorem low_outside_leaf (side : Bool) (a : Word) (low : a.toNat < 0x80000) :
    KeygenLeafCall.Outside side a := by
  have ne (n : Nat) (hn : 0x80000 ≤ n) (small : n < 2^64) : a ≠ BitVec.ofNat 64 n := by
    intro eq
    have h := congrArg BitVec.toNat eq
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt small] at h
    omega
  unfold KeygenLeafCall.Outside KeygenLeafLoop.Outside KeygenChainLoop.Outside
  refine ⟨ne _ (by decide) (by decide), ⟨ne _ (by decide) (by decide),
    ⟨ne _ (by decide) (by decide), ?_, ?_, ?_⟩, ?_⟩, ?_, ?_⟩
  · exact low_ne_word a low _ _ (by decide) (by decide)
  · exact low_ne_word a low _ _ (by decide) (by decide)
  · exact low_ne_word a low _ _ (by decide) (by decide)
  · exact low_ne_word a low _ _ (by decide) (by decide)
  · exact low_ne_word a low _ _ (by decide) (by decide)
  · cases side <;> exact low_ne_word a low _ _ (by decide) (by decide)

theorem left_low_frame (s : MachineState) (sp : s.getReg .x2=0x1000000)
    (a : Word) (low : a.toNat < 0x80000) : (leftState s).getMem a=s.getMem a := by
  have hs : a ≠ 0xfffff0 := by intro eq; rw [eq] at low; change 0xfffff0 < 0x80000 at low; omega
  have hl : a ≠ 0x80428 := by intro eq; rw [eq] at low; change 0x80428 < 0x80000 at low; omega
  rw [leftState,KeygenTreeControl.mem,if_neg hl,entered,enter_mem,sp]
  exact if_neg hs

theorem start_framed (s : MachineState) (pc : s.pc=0x1048) (sp : s.getReg .x2=0x1000000)
    (level tree : Nat) (secretKey : SecretKey) (ctx : Context level tree false secretKey s) :
    ∃ ready, OrdinarySteps keygen s 7 ready ∧ ready.pc=0x11cc ∧ ready.getReg .x1=0x1064 ∧
      ready.getReg .x2=0xfffff0 ∧ ready.getMem 0xfffff0=s.getReg .x1 ∧ Context level tree false secretKey ready ∧
      (∀ a, a.toNat < 0x80000 → ready.getMem a=s.getMem a) := by
  exact ⟨leftState s,left_block s pc sp,left_pc s pc,left_ra s pc,left_sp s sp,left_saved s sp,
    left_context s sp level tree secretKey ctx,left_low_frame s sp⟩

end SigGolfCandidate.Hypertree.KeygenTree
