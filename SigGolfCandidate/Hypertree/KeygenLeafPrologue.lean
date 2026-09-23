import SigGolfCandidate.Hypertree.KeygenLeafLoop
import SigGolfCandidate.Hypertree.KeygenLeafEntry
namespace SigGolfCandidate.Hypertree.KeygenLeafPrologue
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 OracleComp Keygen KeygenSecretStart
set_option maxRecDepth 4096

def ready (s : MachineState) := KeygenLeafEntry.state (enterState s) 1116

theorem frame (s : MachineState) (sp : s.getReg .x2=0xfffff0)
    (a : Word) (hs : a≠0xffffe0) (hc : a≠0x80430) (ht : a≠0x80438) :
    (ready s).getMem a=s.getMem a  := by
  unfold ready
  rw [KeygenLeafEntry.mem,if_neg ht,if_neg hc,enter_mem,sp]
  exact if_neg hs


theorem stack (s : MachineState) (sp : s.getReg .x2=0xfffff0) :
    (ready s).getReg .x2=0xffffe0  := by
  unfold ready
  rw [(KeygenLeafEntry.stack _ _).2,enter_sp,sp]; rfl


theorem saved (s : MachineState) (sp : s.getReg .x2=0xfffff0) :
    (ready s).getMem 0xffffe0=s.getReg .x1  := by
  unfold ready
  rw [KeygenLeafEntry.mem,if_neg (by decide),if_neg (by decide),enter_mem,sp,if_pos (by decide)]


theorem pc (s : MachineState) (pc : s.pc=0x11cc) (sp : s.getReg .x2=0xfffff0)
    (level : Nat) (nonzero : BitVec.ofNat 64 level ≠ 0) (hl : s.getMem 0x80400=BitVec.ofNat 64 level) :
    (ready s).pc=0x1204 := by
  have levelEq : (enterState s).getMem 0x80400=BitVec.ofNat 64 level := by
    rw [enter_mem,sp,if_neg (by decide)]
    exact hl
  unfold ready
  rw [KeygenLeafEntry.pc,levelEq,if_neg nonzero,enter_pc,pc]; rfl


theorem context (s : MachineState) (sp : s.getReg .x2=0xfffff0)
    (level tree : Nat) (side : Bool) (secretKey : SecretKey) (context : Context level tree side secretKey s) :
    Context level tree side secretKey (ready s) := by
  constructor
  · rw [frame _ sp _ (by decide) (by decide) (by decide)]; exact context.levelWord
  · rw [frame _ sp _ (by decide) (by decide) (by decide)]; exact context.leafWord
  · intro i
    rw [frame _ sp _ (by fin_cases i <;> decide) (by fin_cases i <;> decide) (by fin_cases i <;> decide)]
    exact context.indexWords i
  · intro i
    rw [frame _ sp _ (by fin_cases i <;> decide) (by fin_cases i <;> decide) (by fin_cases i <;> decide)]
    exact context.secretKeyWords i
  · rw [frame _ sp _ (by decide) (by decide) (by decide)]; exact context.modeWord

theorem counter (s : MachineState) : (ready s).getMem 0x80430=0 := by
  unfold ready
  rw [KeygenLeafEntry.mem,if_neg (by decide),if_pos rfl]

theorem block (s : MachineState) (pc : s.pc=0x11cc) (sp : s.getReg .x2=0xfffff0) :
    OrdinarySteps keygen s 14 (ready s) := by
  have entered := enter_block keygen 0x11cc keygen_leaf_enter s pc (by rw [sp]; decide)
  have epc : (enterState s).pc=0x11d4 := by rw [enter_pc,pc]; rfl
  have entry := KeygenLeafEntry.block keygen 0x11d4 1116 KeygenLeafEntry.keygen_code (enterState s) epc
  exact ordinary_trans keygen _ _ _ 2 12 entered entry

theorem prepare (s : MachineState) (atPC : s.pc=0x11cc) (sp : s.getReg .x2=0xfffff0)
    (level tree : Nat) (side : Bool) (secretKey : SecretKey)
    (nonzero : BitVec.ofNat 64 level ≠ 0) (ctx : Context level tree side secretKey s) :
    ∃ final, OrdinarySteps keygen s 14 final ∧ final.pc=0x1204 ∧
      Context level tree side secretKey final ∧ final.getMem 0x80430=0 ∧
      final.getReg .x2=0xffffe0 ∧ final.getMem 0xffffe0=s.getReg .x1 ∧
      (∀ a, a≠0xffffe0 → a≠0x80430 → a≠0x80438 → final.getMem a=s.getMem a) := by
  exact ⟨ready s,block s atPC sp,pc s atPC sp level nonzero ctx.levelWord,
    context s sp level tree side secretKey ctx,counter s,stack s sp,saved s sp,frame s sp⟩

end SigGolfCandidate.Hypertree.KeygenLeafPrologue
