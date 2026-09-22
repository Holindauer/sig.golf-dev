import SigGolfCandidate.Execution
import SigGolfCandidate.Hypertree.Proofs

namespace SigGolfCandidate.Hypertree
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 OracleComp

deriving instance DecidableEq for SigGolf.Riscv.Instruction

namespace Expansion
set_option maxRecDepth 4096
set_option Elab.async false

@[simp] theorem reg_setMem (s : MachineState) (a v : Word) (r : Reg) :
    (s.setMem a v).getReg r = s.getReg r := by cases r <;> rfl

@[simp] theorem reg_ite (p : Prop) [Decidable p] (s t : MachineState) (r : Reg) :
    (if p then s else t).getReg r = if p then s.getReg r else t.getReg r := by split <;> rfl

@[simp] theorem pc_ite (p : Prop) [Decidable p] (s t : MachineState) :
    (if p then s else t).pc = if p then s.pc else t.pc := by split <;> rfl

@[simp] theorem mem_ite (p : Prop) [Decidable p] (s t : MachineState) (a : Word) :
    (if p then s else t).getMem a = if p then s.getMem a else t.getMem a := by split <;> rfl

@[simp] theorem pc_setPC (s : MachineState) (pc : Word) : (s.setPC pc).pc = pc := rfl
@[simp] theorem reg_zero (s : MachineState) : s.getReg .x0 = 0 := rfl
@[simp] theorem mem_setMem (s : MachineState) (a v b : Word) :
    (s.setMem a v).getMem b = if b = a then v else s.getMem b := by simp [MachineState.setMem, MachineState.getMem]

def loopBody (s : MachineState) : MachineState :=
  let s := execInstrBr s (.LD .x11 .x6 0)
  let s := execInstrBr s (.SD .x7 .x11 0)
  let s := execInstrBr s (.ADDI .x6 .x6 8)
  let s := execInstrBr s (.ADDI .x7 .x7 8)
  execInstrBr s (.ADDI .x10 .x10 (-1))

def loopNext (s : MachineState) : MachineState :=
  execInstrBr (loopBody s) (.BNE .x10 .x0 (-20))

theorem loop_block (s : MachineState) (pc : s.pc = 0x1018)
    (src : accessValid (s.getReg .x6) 8 = true)
    (dst : accessValid (s.getReg .x7) 8 = true) :
    OrdinarySteps expand s 6 (loopNext s) := by
  let s1 := execInstrBr s (.LD .x11 .x6 0)
  let s2 := execInstrBr s1 (.SD .x7 .x11 0)
  let s3 := execInstrBr s2 (.ADDI .x6 .x6 8)
  let s4 := execInstrBr s3 (.ADDI .x7 .x7 8)
  let s5 := execInstrBr s4 (.ADDI .x10 .x10 (-1))
  let s6 := execInstrBr s5 (.BNE .x10 .x0 (-20))
  apply OrdinarySteps.step s s1 _ (.base (.LD .x11 .x6 0)) 5
  · simp only [fetch, pc, expand]; decide
  · simp [s1, ordinaryStep, memoryArgumentsValid, signExtend12, src]
  apply OrdinarySteps.step s1 s2 _ (.base (.SD .x7 .x11 0)) 4
  · simp only [fetch, s1, execInstrBr, MachineState.setPC, pc, expand]; decide
  · have hd : accessValid (s1.getReg .x7) 8 = true := by simpa [s1, execInstrBr, signExtend12, MachineState.getReg, MachineState.setReg, MachineState.setPC] using dst
    simp [s2, ordinaryStep, memoryArgumentsValid, signExtend12, hd]
  apply OrdinarySteps.step s2 s3 _ (.base (.ADDI .x6 .x6 8)) 3
  · simp only [fetch, s1, s2, execInstrBr, MachineState.setPC, pc, expand]; decide
  · rfl
  apply OrdinarySteps.step s3 s4 _ (.base (.ADDI .x7 .x7 8)) 2
  · simp only [fetch, s1, s2, s3, execInstrBr, MachineState.setPC, pc, expand]; decide
  · rfl
  apply OrdinarySteps.step s4 s5 _ (.base (.ADDI .x10 .x10 (-1))) 1
  · simp only [fetch, s1, s2, s3, s4, execInstrBr, MachineState.setPC, pc, expand]; decide
  · rfl
  apply OrdinarySteps.step s5 s6 _ (.base (.BNE .x10 .x0 (-20))) 0
  · simp only [fetch, s1, s2, s3, s4, s5, execInstrBr, MachineState.setPC, pc, expand]; decide
  · rfl
  exact OrdinarySteps.refl _

theorem loop_next_regs (s : MachineState) :
    (loopNext s).getReg .x6 = s.getReg .x6 + 8 ∧
    (loopNext s).getReg .x7 = s.getReg .x7 + 8 ∧
    (loopNext s).getReg .x10 = s.getReg .x10 - 1 := by
  unfold loopNext loopBody
  simp only [execInstrBr]
  simp [MachineState.getReg_setReg_ne, MachineState.getReg_setReg_eq,
    signExtend12, BitVec.sub_eq_add_neg]

theorem loop_body_pc (s : MachineState) : (loopBody s).pc = s.pc + 20 := by
  simp [loopBody, execInstrBr, BitVec.add_assoc]

theorem loop_body_count (s : MachineState) : (loopBody s).getReg .x10 = s.getReg .x10 - 1 := by
  unfold loopBody
  simp [execInstrBr, MachineState.getReg_setReg_ne, MachineState.getReg_setReg_eq,
    signExtend12, BitVec.sub_eq_add_neg]

theorem loop_next_pc (s : MachineState) (pc : s.pc = 0x1018) :
    (loopNext s).pc = if s.getReg .x10 = 1 then 0x1030 else 0x1018 := by
  have decrement (x : BitVec 64) : x - 1#64 = 0#64 ↔ x = 1#64 := by
    exact BitVec.sub_left_inj (x := x) (y := 1) 1
  simp only [loopNext, execInstrBr, pc_ite, pc_setPC, loop_body_pc, loop_body_count, reg_zero, pc]
  simp only [signExtend13]
  simp
  simp only [decrement]

theorem loop_next_mem (s : MachineState) (address : BitVec 64) :
    (loopNext s).getMem address =
      if address = s.getReg .x7 then s.getMem (s.getReg .x6) else s.getMem address := by
  unfold loopNext loopBody
  simp only [execInstrBr]
  simp [signExtend12,
    MachineState.getReg_setReg_ne, MachineState.getReg_setReg_eq]

def finishState (s : MachineState) : MachineState :=
  execInstrBr (execInstrBr s (.ADDI .x5 .x0 0)) (.ADDI .x10 .x0 1)

theorem finish (hash : Hash) (s : MachineState) (pc : s.pc = 0x1030) :
    Executes hash expand s 3 ⟨.success, finishState s, 3, 0, 0⟩ := by
  have block : OrdinarySteps expand s 2 (finishState s) := by
    apply OrdinarySteps.step s (execInstrBr s (.ADDI .x5 .x0 0)) _ (.base (.ADDI .x5 .x0 0)) 1
    · simp only [fetch, pc, expand]; decide
    · rfl
    apply OrdinarySteps.step _ (finishState s) _ (.base (.ADDI .x10 .x0 1)) 0
    · simp only [fetch, execInstrBr, MachineState.setPC, pc, expand]; decide
    · rfl
    exact OrdinarySteps.refl _
  have hf : fetch expand (finishState s) = some (.base .ECALL) := by
    simp only [fetch, finishState, execInstrBr, MachineState.setPC, pc, expand]; decide
  have hs : (finishState s).getReg .x5 = 0 := by rfl
  have hv : (finishState s).getReg .x10 = 1 := by rfl
  simpa [hv, Execution.charge] using block.then_executes (Executes.halt (hash := hash) _ hf hs)

/-- The loop invariant tracks byte addresses and remaining words; it puts no restrictions on their contents. -/
def Invariant (n : Nat) (s : MachineState) : Prop :=
  n ≤ 14954 ∧ s.pc = (if n = 0 then 0x1030 else 0x1018) ∧
  s.getReg .x6 = BitVec.ofNat 64 (0x20060 + 8 * (14954 - n)) ∧
  s.getReg .x7 = BitVec.ofNat 64 (0x3d3b0 + 8 * (14954 - n)) ∧
  s.getReg .x10 = BitVec.ofNat 64 n

theorem loop_invariant (n : Nat) (s : MachineState) (inv : Invariant (n + 1) s) :
    Invariant n (loopNext s) := by
  obtain ⟨hn, pc, src, dst, count⟩ := inv
  have hp : s.pc = 0x1018 := by simpa using pc
  have heq : BitVec.ofNat 64 (n + 1) = 1 ↔ n = 0 := by
    have hsmall : n + 1 < 2 ^ 64 := by omega
    constructor
    · intro h
      have value := congrArg BitVec.toNat h
      change (n + 1) % 2 ^ 64 = 1 at value
      rw [Nat.mod_eq_of_lt hsmall] at value
      omega
    · intro h
      subst n
      rfl
  refine ⟨by omega, ?_, ?_, ?_, ?_⟩
  · rw [loop_next_pc s hp, count]
    simp only [heq]
  · rw [(loop_next_regs s).1, src]
    change BitVec.ofNat 64 (0x20060 + 8 * (14954 - (n + 1))) + BitVec.ofNat 64 8 = _
    rw [← BitVec.ofNat_add]
    congr 1
    omega
  · rw [(loop_next_regs s).2.1, dst]
    change BitVec.ofNat 64 (0x3d3b0 + 8 * (14954 - (n + 1))) + BitVec.ofNat 64 8 = _
    rw [← BitVec.ofNat_add]
    congr 1
    omega
  · rw [(loop_next_regs s).2.2, count, BitVec.ofNat_add]
    exact BitVec.add_sub_cancel _ _

theorem loop_accesses (n : Nat) (s : MachineState) (inv : Invariant (n + 1) s) :
    accessValid (s.getReg .x6) 8 = true ∧ accessValid (s.getReg .x7) 8 = true := by
  obtain ⟨hn, _, src, dst, _⟩ := inv
  simp [accessValid, rangeValid, src, dst, BitVec.toNat_ofNat,
    MEMORY_BYTES, Nat.add_mod, Nat.mul_mod]
  omega

theorem loop_executes (hash : Hash) (n : Nat) (s : MachineState) (inv : Invariant n s) :
    ∃ final, Executes hash expand s (6 * n + 3) ⟨.success, final, 6 * n + 3, 0, 0⟩ := by
  induction n generalizing s with
  | zero => exact ⟨finishState s, finish hash s (by simpa using inv.2.1)⟩
  | succ n ih =>
    have block := loop_block s (by simpa using inv.2.1)
      (loop_accesses n s inv).1 (loop_accesses n s inv).2
    obtain ⟨final, tail⟩ := ih (loopNext s) (loop_invariant n s inv)
    refine ⟨final, ?_⟩
    have hsteps : 6 * n + 3 + 6 = 6 * (n + 1) + 3 := by omega
    have hcycles : 6 + (6 * n + 3) = 6 * (n + 1) + 3 := by omega
    simpa only [Execution.charge, hsteps, hcycles, Nat.zero_add] using block.then_executes tail

def prefixState (s : MachineState) : MachineState :=
  let s := execInstrBr s (.LUI .x6 0x20)
  let s := execInstrBr s (.ADDI .x6 .x6 0x60)
  let s := execInstrBr s (.LUI .x7 0x3d)
  let s := execInstrBr s (.ADDI .x7 .x7 0x3b0)
  let s := execInstrBr s (.LUI .x10 4)
  execInstrBr s (.ADDI .x10 .x10 0xa6a)

theorem prefix_block (s : MachineState) (pc : s.pc = 0x1000) :
    OrdinarySteps expand s 6 (prefixState s) := by
  let s1 := execInstrBr s (.LUI .x6 0x20)
  let s2 := execInstrBr s1 (.ADDI .x6 .x6 0x60)
  let s3 := execInstrBr s2 (.LUI .x7 0x3d)
  let s4 := execInstrBr s3 (.ADDI .x7 .x7 0x3b0)
  let s5 := execInstrBr s4 (.LUI .x10 4)
  let s6 := execInstrBr s5 (.ADDI .x10 .x10 0xa6a)
  apply OrdinarySteps.step s s1 _ (.base (.LUI .x6 0x20)) 5
  · simp only [fetch, pc, expand]; decide
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.ADDI .x6 .x6 0x60)) 4
  · simp only [fetch, s1, execInstrBr, MachineState.setPC, pc, expand]; decide
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.LUI .x7 0x3d)) 3
  · simp only [fetch, s1, s2, execInstrBr, MachineState.setPC, pc, expand]; decide
  · rfl
  apply OrdinarySteps.step s3 s4 _ (.base (.ADDI .x7 .x7 0x3b0)) 2
  · simp only [fetch, s1, s2, s3, execInstrBr, MachineState.setPC, pc, expand]; decide
  · rfl
  apply OrdinarySteps.step s4 s5 _ (.base (.LUI .x10 4)) 1
  · simp only [fetch, s1, s2, s3, s4, execInstrBr, MachineState.setPC, pc, expand]; decide
  · rfl
  apply OrdinarySteps.step s5 s6 _ (.base (.ADDI .x10 .x10 0xa6a)) 0
  · simp only [fetch, s1, s2, s3, s4, s5, execInstrBr, MachineState.setPC, pc, expand]; decide
  · rfl
  exact OrdinarySteps.refl _

theorem prefix_invariant (s : MachineState) (pc : s.pc = 0x1000) :
    Invariant 14954 (prefixState s) := by
  unfold Invariant prefixState
  simp [execInstrBr, MachineState.getReg_setReg_ne, MachineState.getReg_setReg_eq,
    signExtend12, pc]

/-- The actual expansion image succeeds on arbitrary memory contents in exactly 89,733 cycles, without hash calls. -/
theorem executes (hash : Hash) (s : MachineState) (pc : s.pc = 0x1000) :
    ∃ final, Executes hash expand s 89733 ⟨.success, final, 89733, 0, 0⟩ := by
  obtain ⟨final, tail⟩ := loop_executes hash 14954 (prefixState s) (prefix_invariant s pc)
  refine ⟨final, ?_⟩
  have hsteps : (6 * 14954 + 3) + 6 = 89733 := by decide
  have hcycles : 6 + (6 * 14954 + 3) = 89733 := by decide
  simpa only [Execution.charge, hsteps, hcycles, Nat.zero_add] using (prefix_block s pc).then_executes tail

/-- Universal expansion resource guarantee through the organizer's loader and output decoder. -/
theorem run_bound (hash : Hash) (input : Input submission.sizes .expand) :
    let result := submission.runWith hash .expand input
    result.finished = true ∧ result.value.isSome = true ∧ result.cycles = 89733 ∧
      result.hashCalls = 0 ∧ result.hashCompressions = 0 := by
  obtain ⟨state, loaded, pc⟩ := initialState_exists submission admitted .expand input
  obtain ⟨final, trace⟩ := executes hash state pc
  have bound : 89733 ≤ CYCLE_LIMIT := by decide
  have run := runWith_of_executes submission hash .expand input state 89733
    ⟨.success, final, 89733, 0, 0⟩ loaded trace bound
  simp [run]

/-- info: 'SigGolfCandidate.Hypertree.Expansion.executes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms executes

end Expansion
end SigGolfCandidate.Hypertree
