import SigGolfCandidate.Hypertree.Expand

namespace SigGolfCandidate.Hypertree.Signing
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 OracleComp Expansion
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false

/-- Template for the final root/public-key comparison, independent of the rest of the signer. -/
def footerInstructions : List Instr := [
  .LUI .x28 0x80, .ADDI .x28 .x28 0x500, .LD .x6 .x28 0,
  .ADDI .x28 .x0 0x40, .LD .x7 .x28 0, .BNE .x6 .x7 40,
  .LUI .x28 0x80, .ADDI .x28 .x28 0x508, .LD .x6 .x28 0,
  .ADDI .x28 .x0 0x48, .LD .x7 .x28 0, .BNE .x6 .x7 16,
  .ADDI .x5 .x0 0, .ADDI .x10 .x0 1, .ECALL,
  .ADDI .x5 .x0 0, .ADDI .x10 .x0 0, .ECALL]

/-- Each fetched instruction is checked against the organizer's decoder. -/
def FooterCode (image : Image) (base : Word) : Prop :=
  ∀ (s : MachineState) (i : Fin 18), s.pc = base + BitVec.ofNat 64 (4 * i.val) →
    fetch image s = some (.base (footerInstructions[i.val]'(by simp [footerInstructions])))

def comparisonState (s : MachineState) (i : Fin 2) : MachineState :=
  let s := execInstrBr s (.LUI .x28 0x80)
  let s := execInstrBr s (.ADDI .x28 .x28 (BitVec.ofNat 12 (0x500 + 8 * i.val)))
  let s := execInstrBr s (.LD .x6 .x28 0)
  let s := execInstrBr s (.ADDI .x28 .x0 (BitVec.ofNat 12 (0x40 + 8 * i.val)))
  execInstrBr s (.LD .x7 .x28 0)

theorem comparison_block (image : Image) (base : Word) (code : FooterCode image base)
    (s : MachineState) (i : Fin 2) (pc : s.pc = base + BitVec.ofNat 64 (24 * i.val)) :
    OrdinarySteps image s 5 (comparisonState s i) := by
  fin_cases i
  · let s1 := execInstrBr s (.LUI .x28 0x80)
    let s2 := execInstrBr s1 (.ADDI .x28 .x28 0x500)
    let s3 := execInstrBr s2 (.LD .x6 .x28 0)
    let s4 := execInstrBr s3 (.ADDI .x28 .x0 0x40)
    let s5 := execInstrBr s4 (.LD .x7 .x28 0)
    apply OrdinarySteps.step s s1 _ (.base (.LUI .x28 0x80)) 4
    · apply code _ 0
      simp [execInstrBr, pc, BitVec.add_assoc]
    · simp [s1, ordinaryStep, memoryArgumentsValid, execInstrBr, signExtend12, accessValid, rangeValid, MEMORY_BYTES, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
    apply OrdinarySteps.step s1 s2 _ (.base (.ADDI .x28 .x28 0x500)) 3
    · apply code _ 1
      simp [s1, execInstrBr, pc, BitVec.add_assoc]
    · simp [s2, ordinaryStep, memoryArgumentsValid, s1, execInstrBr, signExtend12, accessValid, rangeValid, MEMORY_BYTES, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
    apply OrdinarySteps.step s2 s3 _ (.base (.LD .x6 .x28 0)) 2
    · apply code _ 2
      simp [s1, s2, execInstrBr, pc, BitVec.add_assoc]
    · simp [s3, ordinaryStep, memoryArgumentsValid, s1, s2, execInstrBr, signExtend12, accessValid, rangeValid, MEMORY_BYTES, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
    apply OrdinarySteps.step s3 s4 _ (.base (.ADDI .x28 .x0 0x40)) 1
    · apply code _ 3
      simp [s1, s2, s3, execInstrBr, pc, BitVec.add_assoc]
    · simp [s4, ordinaryStep, memoryArgumentsValid, s1, s2, s3, execInstrBr, signExtend12, accessValid, rangeValid, MEMORY_BYTES, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
    apply OrdinarySteps.step s4 s5 _ (.base (.LD .x7 .x28 0)) 0
    · apply code _ 4
      simp [s1, s2, s3, s4, execInstrBr, pc, BitVec.add_assoc]
    · simp [s5, ordinaryStep, memoryArgumentsValid, s1, s2, s3, s4, execInstrBr, signExtend12, accessValid, rangeValid, MEMORY_BYTES, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
    exact OrdinarySteps.refl _
  · let s1 := execInstrBr s (.LUI .x28 0x80)
    let s2 := execInstrBr s1 (.ADDI .x28 .x28 0x508)
    let s3 := execInstrBr s2 (.LD .x6 .x28 0)
    let s4 := execInstrBr s3 (.ADDI .x28 .x0 0x48)
    let s5 := execInstrBr s4 (.LD .x7 .x28 0)
    apply OrdinarySteps.step s s1 _ (.base (.LUI .x28 0x80)) 4
    · apply code _ 6
      simp [execInstrBr, pc, BitVec.add_assoc]
    · simp [s1, ordinaryStep, memoryArgumentsValid, execInstrBr, signExtend12, accessValid, rangeValid, MEMORY_BYTES, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
    apply OrdinarySteps.step s1 s2 _ (.base (.ADDI .x28 .x28 0x508)) 3
    · apply code _ 7
      simp [s1, execInstrBr, pc, BitVec.add_assoc]
    · simp [s2, ordinaryStep, memoryArgumentsValid, s1, execInstrBr, signExtend12, accessValid, rangeValid, MEMORY_BYTES, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
    apply OrdinarySteps.step s2 s3 _ (.base (.LD .x6 .x28 0)) 2
    · apply code _ 8
      simp [s1, s2, execInstrBr, pc, BitVec.add_assoc]
    · simp [s3, ordinaryStep, memoryArgumentsValid, s1, s2, execInstrBr, signExtend12, accessValid, rangeValid, MEMORY_BYTES, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
    apply OrdinarySteps.step s3 s4 _ (.base (.ADDI .x28 .x0 0x48)) 1
    · apply code _ 9
      simp [s1, s2, s3, execInstrBr, pc, BitVec.add_assoc]
    · simp [s4, ordinaryStep, memoryArgumentsValid, s1, s2, s3, execInstrBr, signExtend12, accessValid, rangeValid, MEMORY_BYTES, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
    apply OrdinarySteps.step s4 s5 _ (.base (.LD .x7 .x28 0)) 0
    · apply code _ 10
      simp [s1, s2, s3, s4, execInstrBr, pc, BitVec.add_assoc]
    · simp [s5, ordinaryStep, memoryArgumentsValid, s1, s2, s3, s4, execInstrBr, signExtend12, accessValid, rangeValid, MEMORY_BYTES, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
    exact OrdinarySteps.refl _

theorem comparison_regs (s : MachineState) (i : Fin 2) :
    (comparisonState s i).getReg .x6 = s.getMem (BitVec.ofNat 64 (0x80500 + 8 * i.val)) ∧
    (comparisonState s i).getReg .x7 = s.getMem (BitVec.ofNat 64 (0x40 + 8 * i.val)) := by
  fin_cases i <;> simp [comparisonState, execInstrBr, signExtend12,
    MachineState.getReg_setReg_ne, MachineState.getReg_setReg_eq]

theorem comparison_pc (s : MachineState) (i : Fin 2) :
    (comparisonState s i).pc = s.pc + 20 := by
  simp [comparisonState, execInstrBr, BitVec.add_assoc]

theorem comparison_mem (s : MachineState) (i : Fin 2) (a : Word) :
    (comparisonState s i).getMem a = s.getMem a := by
  simp [comparisonState, execInstrBr]

def terminalState (s : MachineState) (accepted : Bool) : MachineState :=
  execInstrBr (execInstrBr s (.ADDI .x5 .x0 0))
    (.ADDI .x10 .x0 (if accepted then 1 else 0))

theorem terminal (hash : Hash) (image : Image) (base : Word) (code : FooterCode image base)
    (s : MachineState) (accepted : Bool)
    (pc : s.pc = base + (if accepted then 48 else 60)) :
    Executes hash image s 3
      ⟨if accepted then .success else .failure, terminalState s accepted, 3, 0, 0⟩ := by
  cases accepted
  · have block : OrdinarySteps image s 2 (terminalState s false) := by
      let s1 := execInstrBr s (.ADDI .x5 .x0 0)
      apply OrdinarySteps.step s s1 _ (.base (.ADDI .x5 .x0 0)) 1
      · apply code _ 15; simpa using pc
      · rfl
      apply OrdinarySteps.step s1 _ _ (.base (.ADDI .x10 .x0 0)) 0
      · apply code _ 16; simp [s1, execInstrBr, pc, BitVec.add_assoc]
      · rfl
      exact OrdinarySteps.refl _
    have hf : fetch image (terminalState s false) = some (.base .ECALL) := by
      apply code _ 17; simp [terminalState, execInstrBr, pc, BitVec.add_assoc]
    have hs : (terminalState s false).getReg .x5 = 0 := rfl
    have hv : (terminalState s false).getReg .x10 = 0 := rfl
    simpa [hv, Execution.charge] using block.then_executes (Executes.halt (hash := hash) _ hf hs)
  · have block : OrdinarySteps image s 2 (terminalState s true) := by
      let s1 := execInstrBr s (.ADDI .x5 .x0 0)
      apply OrdinarySteps.step s s1 _ (.base (.ADDI .x5 .x0 0)) 1
      · apply code _ 12; simpa using pc
      · rfl
      apply OrdinarySteps.step s1 _ _ (.base (.ADDI .x10 .x0 1)) 0
      · apply code _ 13; simp [s1, execInstrBr, pc, BitVec.add_assoc]
      · rfl
      exact OrdinarySteps.refl _
    have hf : fetch image (terminalState s true) = some (.base .ECALL) := by
      apply code _ 14; simp [terminalState, execInstrBr, pc, BitVec.add_assoc]
    have hs : (terminalState s true).getReg .x5 = 0 := rfl
    have hv : (terminalState s true).getReg .x10 = 1 := rfl
    simpa [hv, Execution.charge] using block.then_executes (Executes.halt (hash := hash) _ hf hs)

def comparisonNext (s : MachineState) (i : Fin 2) : MachineState :=
  execInstrBr (comparisonState s i) (.BNE .x6 .x7 (if i.val = 0 then 40 else 16))

theorem comparison_next_block (image : Image) (base : Word) (code : FooterCode image base)
    (s : MachineState) (i : Fin 2) (pc : s.pc = base + BitVec.ofNat 64 (24 * i.val)) :
    OrdinarySteps image (comparisonState s i) 1 (comparisonNext s i) := by
  apply OrdinarySteps.step _ _ _ (.base (.BNE .x6 .x7 (if i.val = 0 then 40 else 16))) 0
  · fin_cases i
    · apply code _ 5; simp [comparison_pc, pc, BitVec.add_assoc]
    · apply code _ 11; simp [comparison_pc, pc, BitVec.add_assoc]
  · rfl
  exact OrdinarySteps.refl _

theorem comparison_next_pc (s : MachineState) (base : Word) (i : Fin 2)
    (pc : s.pc = base + BitVec.ofNat 64 (24 * i.val)) :
    (comparisonNext s i).pc =
      if s.getMem (BitVec.ofNat 64 (0x80500 + 8 * i.val)) =
          s.getMem (BitVec.ofNat 64 (0x40 + 8 * i.val))
      then base + BitVec.ofNat 64 (24 * (i.val + 1)) else base + 60 := by
  simp only [comparisonNext, execInstrBr, pc_ite, pc_setPC,
    (comparison_regs s i).1, (comparison_regs s i).2, comparison_pc, pc]
  fin_cases i <;> simp [signExtend13, BitVec.add_assoc]

theorem comparison_next_mem (s : MachineState) (i : Fin 2) (a : Word) :
    (comparisonNext s i).getMem a = s.getMem a := by
  simp [comparisonNext, execInstrBr, comparison_mem]

theorem comparison_then {hash : Hash} {image : Image} {base : Word}
    (code : FooterCode image base) (s : MachineState) (i : Fin 2)
    (pc : s.pc = base + BitVec.ofNat 64 (24 * i.val))
    {steps : Nat} {result : Execution}
    (tail : Executes hash image (comparisonNext s i) steps result) :
    Executes hash image s (steps + 6) (result.charge 6 0 0) := by
  have branch := (comparison_next_block image base code s i pc).then_executes tail
  simpa [Execution.charge, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
    (comparison_block image base code s i pc).then_executes branch

def RootMatches (s : MachineState) : Prop :=
  s.getMem 0x80500 = s.getMem 0x40 ∧ s.getMem 0x80508 = s.getMem 0x48

instance (s : MachineState) : Decidable (RootMatches s) :=
  inferInstanceAs (Decidable (_ ∧ _))

theorem terminal_mem (s : MachineState) (accepted : Bool) (a : Word) :
    (terminalState s accepted).getMem a = s.getMem a := by
  simp [terminalState, execInstrBr]

/-- Every state at this footer terminates within 15 cycles with no oracle calls.
Success is exactly equality of the two 128-bit root/public-key values. All memory,
including the signature buffer, is preserved. No assumption on the signer prefix is used. -/
theorem footer_executes (hash : Hash) (image : Image) (base : Word)
    (code : FooterCode image base) (s : MachineState) (pc : s.pc = base) :
    ∃ (steps : Nat) (final : MachineState), steps ≤ 15 ∧
      Executes hash image s steps
        ⟨if RootMatches s then .success else .failure, final, steps, 0, 0⟩ ∧
      ∀ a, final.getMem a = s.getMem a := by
  have pc0 : s.pc = base + BitVec.ofNat 64 (24 * (0 : Fin 2).val) := by simpa using pc
  by_cases h0 : s.getMem 0x80500 = s.getMem 0x40
  · have pc1 : (comparisonNext s 0).pc = base + BitVec.ofNat 64 (24 * (1 : Fin 2).val) := by
      have hp := comparison_next_pc s base 0 pc0
      change (comparisonNext s 0).pc = (if s.getMem 0x80500 = s.getMem 0x40 then base + 24 else base + 60) at hp
      rw [if_pos h0] at hp
      exact hp
    by_cases h1 : s.getMem 0x80508 = s.getMem 0x48
    · have pc2 : (comparisonNext (comparisonNext s 0) 1).pc = base + 48 := by
        have hp := comparison_next_pc (comparisonNext s 0) base 1 pc1
        simp only [comparison_next_mem] at hp
        change (comparisonNext (comparisonNext s 0) 1).pc = (if s.getMem 0x80508 = s.getMem 0x48 then base + 48 else base + 60) at hp
        rw [if_pos h1] at hp
        exact hp
      have finish := terminal hash image base code (comparisonNext (comparisonNext s 0) 1) true pc2
      have trace := comparison_then code s 0 pc0 (comparison_then code (comparisonNext s 0) 1 pc1 finish)
      refine ⟨15, terminalState (comparisonNext (comparisonNext s 0) 1) true, by decide, ?_, ?_⟩
      · have hm : RootMatches s := ⟨h0, h1⟩
        rw [if_pos hm]
        simpa [Execution.charge] using trace
      · intro a; simp [terminal_mem, comparison_next_mem]
    · have pc2 : (comparisonNext (comparisonNext s 0) 1).pc = base + 60 := by
        have hp := comparison_next_pc (comparisonNext s 0) base 1 pc1
        simp only [comparison_next_mem] at hp
        change (comparisonNext (comparisonNext s 0) 1).pc = (if s.getMem 0x80508 = s.getMem 0x48 then base + 48 else base + 60) at hp
        rw [if_neg h1] at hp
        exact hp
      have finish := terminal hash image base code (comparisonNext (comparisonNext s 0) 1) false pc2
      have trace := comparison_then code s 0 pc0 (comparison_then code (comparisonNext s 0) 1 pc1 finish)
      refine ⟨15, terminalState (comparisonNext (comparisonNext s 0) 1) false, by decide, ?_, ?_⟩
      · have hm : ¬ RootMatches s := fun h => h1 h.2
        rw [if_neg hm]
        simpa [Execution.charge] using trace
      · intro a; simp [terminal_mem, comparison_next_mem]
  · have pc1 : (comparisonNext s 0).pc = base + 60 := by
      have hp := comparison_next_pc s base 0 pc0
      change (comparisonNext s 0).pc = (if s.getMem 0x80500 = s.getMem 0x40 then base + 24 else base + 60) at hp
      rw [if_neg h0] at hp
      exact hp
    have finish := terminal hash image base code (comparisonNext s 0) false pc1
    have trace := comparison_then code s 0 pc0 finish
    refine ⟨9, terminalState (comparisonNext s 0) false, by decide, ?_, ?_⟩
    · have hm : ¬ RootMatches s := fun h => h0 h.1
      rw [if_neg hm]
      simpa [Execution.charge] using trace
    · intro a; simp [terminal_mem, comparison_next_mem]

/-- info: 'SigGolfCandidate.Hypertree.Signing.footer_executes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms footer_executes

/-- The randomized signing image contains this exact checked footer. -/
theorem sign_footer_code : FooterCode sign 0x12f8 := by
  intro s i pc
  simp only [fetch, pc]
  fin_cases i <;> decide

/-- Actual signing bytecode from its final root check, independent of all prefix invariants. -/
theorem sign_footer_executes (hash : Hash) (s : MachineState) (pc : s.pc = 0x12f8) :
    ∃ (steps : Nat) (final : MachineState), steps ≤ 15 ∧
      Executes hash sign s steps
        ⟨if RootMatches s then .success else .failure, final, steps, 0, 0⟩ ∧
      ∀ a, final.getMem a = s.getMem a :=
  footer_executes hash sign 0x12f8 sign_footer_code s pc

end SigGolfCandidate.Hypertree.Signing
