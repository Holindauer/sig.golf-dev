import SigGolfCandidate.Hypertree.ResourceAbstract

namespace SigGolfCandidate.Resources
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 OracleComp

private def nextReg (a : AbstractState) (rd : Reg) (value : Option Word) : AbstractState :=
  (a.setReg rd value).setPC (a.pc + 4)

private theorem nextReg_models {a : AbstractState} {s : MachineState} (h : a.Models s)
    (rd : Reg) {value : Option Word} {v : Word} (known : Knows value v) :
    (nextReg a rd value).Models ((s.setReg rd v).setPC (s.pc + 4)) := by
  simpa only [nextReg, h.pc] using (h.setReg rd known).setPC (a.pc + 4)

/-- A deliberately partial transfer function: unknown branch conditions or addresses are rejected. -/
def ordinaryTransfer (a : AbstractState) : Instr → Option AbstractState
  | .ADD rd r1 r2 => some (nextReg a rd (map₂ (· + ·) (a.getReg r1) (a.getReg r2)))
  | .ADDI rd rs off => some (nextReg a rd ((a.getReg rs).map (· + signExtend12 off)))
  | .SLLI rd rs n => some (nextReg a rd ((a.getReg rs).map (fun v : Word => v <<< n.toNat)))
  | .SRLI rd rs n => some (nextReg a rd ((a.getReg rs).map (fun v : Word => v >>> n.toNat)))
  | .ANDI rd rs imm => some (nextReg a rd ((a.getReg rs).map (· &&& signExtend12 imm)))
  | .XORI rd rs imm => some (nextReg a rd ((a.getReg rs).map (· ^^^ signExtend12 imm)))
  | .LUI rd imm => some (nextReg a rd (some (((imm.zeroExtend 32) <<< 12).signExtend 64)))
  | .LD rd rs off => do
      let base ← a.getReg rs
      let p := base + signExtend12 off
      if accessValid p 8 then some (nextReg a rd (lookup p a.mem)) else none
  | .SD rs data off => do
      let base ← a.getReg rs
      let p := base + signExtend12 off
      if accessValid p 8 then some ((a.setMem p (a.getReg data)).setPC (a.pc + 4)) else none
  | .BEQ r1 r2 off => do
      let v1 ← a.getReg r1
      let v2 ← a.getReg r2
      some (a.setPC (if v1 == v2 then a.pc + signExtend13 off else a.pc + 4))
  | .BNE r1 r2 off => do
      let v1 ← a.getReg r1
      let v2 ← a.getReg r2
      some (a.setPC (if v1 != v2 then a.pc + signExtend13 off else a.pc + 4))
  | .JAL rd off => some ((a.setReg rd (some (a.pc + 4))).setPC (a.pc + signExtend21 off))
  | .JALR rd rs off => do
      let base ← a.getReg rs
      some ((a.setReg rd (some (a.pc + 4))).setPC ((base + signExtend12 off) &&& ~~~1#64))
  | _ => none

/-- Every successful abstract ordinary step is a valid concrete step and preserves its information. -/
theorem ordinaryTransfer_sound {a next : AbstractState} {s : MachineState} (h : a.Models s)
    (instruction : Instr) (step : ordinaryTransfer a instruction = some next) :
    ordinaryStep s (.base instruction) = some (execInstrBr s instruction) ∧
      next.Models (execInstrBr s instruction) := by
  cases instruction <;> simp only [ordinaryTransfer, reduceCtorEq, Option.some.injEq] at step
  case ADD rd r1 r2 =>
    subst next
    exact ⟨rfl, nextReg_models h rd (Knows.map₂ _ (h.regs r1) (h.regs r2))⟩
  case ADDI rd rs off =>
    subst next
    exact ⟨rfl, nextReg_models h rd ((h.regs rs).map _)⟩
  case SLLI rd rs n =>
    subst next
    exact ⟨rfl, nextReg_models h rd ((h.regs rs).map _)⟩
  case SRLI rd rs n =>
    subst next
    exact ⟨rfl, nextReg_models h rd ((h.regs rs).map _)⟩
  case ANDI rd rs n =>
    subst next
    exact ⟨rfl, nextReg_models h rd ((h.regs rs).map _)⟩
  case XORI rd rs n =>
    subst next
    exact ⟨rfl, nextReg_models h rd ((h.regs rs).map _)⟩
  case LUI rd imm =>
    subst next
    exact ⟨rfl, nextReg_models h rd (Knows.some _)⟩
  case LD rd rs off =>
    cases hr : a.getReg rs with
    | none => simp [hr] at step
    | some base =>
      have eq := h.regs rs base hr
      by_cases valid : accessValid (base + signExtend12 off) 8 = true
      · simp [hr, valid] at step
        subst next
        refine ⟨by simp [ordinaryStep, memoryArgumentsValid, eq, valid], ?_⟩
        simpa only [execInstrBr, eq] using nextReg_models h rd (h.mem (base + signExtend12 off))
      · simp [hr, valid] at step
  case SD rs data off =>
    cases hr : a.getReg rs with
    | none => simp [hr] at step
    | some base =>
      have eq := h.regs rs base hr
      by_cases valid : accessValid (base + signExtend12 off) 8 = true
      · simp [hr, valid] at step
        subst next
        refine ⟨by simp [ordinaryStep, memoryArgumentsValid, eq, valid], ?_⟩
        simpa [execInstrBr, eq, h.pc] using
          (h.setMem (base + signExtend12 off) (h.regs data)).setPC (a.pc + 4)
      · simp [hr, valid] at step
  case BEQ r1 r2 off =>
    cases h1 : a.getReg r1 with
    | none => simp [h1] at step
    | some v1 =>
      cases h2 : a.getReg r2 with
      | none => simp [h1, h2] at step
      | some v2 =>
        simp [h1, h2] at step
        subst next
        refine ⟨rfl, ?_⟩
        have eq1 := h.regs r1 v1 h1
        have eq2 := h.regs r2 v2 h2
        by_cases e : v1 = v2
        · simpa [execInstrBr, eq1, eq2, e, h.pc] using h.setPC (a.pc + signExtend13 off)
        · simpa [execInstrBr, eq1, eq2, e, h.pc] using h.setPC (a.pc + 4)
  case BNE r1 r2 off =>
    cases h1 : a.getReg r1 with
    | none => simp [h1] at step
    | some v1 =>
      cases h2 : a.getReg r2 with
      | none => simp [h1, h2] at step
      | some v2 =>
        simp [h1, h2] at step
        subst next
        refine ⟨rfl, ?_⟩
        have eq1 := h.regs r1 v1 h1
        have eq2 := h.regs r2 v2 h2
        by_cases e : v1 = v2
        · simpa [execInstrBr, eq1, eq2, e, h.pc] using h.setPC (a.pc + 4)
        · simpa [execInstrBr, eq1, eq2, e, h.pc] using h.setPC (a.pc + signExtend13 off)
  case JAL rd off =>
    subst next
    refine ⟨rfl, ?_⟩
    simpa [execInstrBr, h.pc] using
      (h.setReg rd (Knows.some (s.pc + 4))).setPC (a.pc + signExtend21 off)
  case JALR rd rs off =>
    cases hr : a.getReg rs with
    | none => simp [hr] at step
    | some base =>
      simp [hr] at step
      subst next
      refine ⟨rfl, ?_⟩
      have eq := h.regs rs base hr
      simpa [execInstrBr, eq, h.pc] using
        (h.setReg rd (Knows.some (s.pc + 4))).setPC ((base + signExtend12 off) &&& ~~~1#64)

end SigGolfCandidate.Resources
