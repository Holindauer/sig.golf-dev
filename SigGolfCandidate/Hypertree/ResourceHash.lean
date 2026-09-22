import SigGolfCandidate.Hypertree.ResourceTransfer

namespace SigGolfCandidate.Resources
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 OracleComp

/-- HASH overwrites exactly four words; their values become unknown. -/
def forgetHash (a : AbstractState) (destination : Word) : AbstractState :=
  let a := a.setMem destination none
  let a := a.setMem (destination + 8) none
  let a := a.setMem (destination + 16) none
  let a := a.setMem (destination + 24) none
  a.setPC (a.pc + 4)

theorem forgetHash_models {a : AbstractState} {s : MachineState} (h : a.Models s)
    (destination : Word) (hd : s.getReg .x12 = destination) (answer : BitVec 256) :
    (forgetHash a destination).Models (writeHash s answer) := by
  have m1 := h.setMem destination (Knows.none (answer.extractLsb' 0 64))
  have m2 := m1.setMem (destination + 8) (Knows.none (answer.extractLsb' 64 64))
  have m3 := m2.setMem (destination + 16) (Knows.none (answer.extractLsb' 128 64))
  have m4 := m3.setMem (destination + 24) (Knows.none (answer.extractLsb' 192 64))
  simpa [forgetHash, AbstractState.setMem, writeHash, MachineState.writeWords,
    hd, h.pc, BitVec.add_assoc] using m4.setPC (a.pc + 4)

def hashGuard (source bits destination : Word) : Bool :=
  decide (source.toNat % 8 = 0) && rangeValid source ((bits.toNat + 7) / 8) &&
    accessValid destination 8 && rangeValid destination 32

def hashTransfer (a : AbstractState) : Option (AbstractState × Nat) := do
  let source ← a.getReg .x10
  let bits ← a.getReg .x11
  let destination ← a.getReg .x12
  if hashGuard source bits destination then
    some (forgetHash a destination, compressions bits.toNat)
  else none

theorem hashTransfer_sound {a next : AbstractState} {s : MachineState} {blocks : Nat}
    (h : a.Models s) (step : hashTransfer a = some (next, blocks)) (answer : BitVec 256) :
    hashArgumentsValid s = true ∧ blocks = compressions (hashInput s).1 ∧
      next.Models (writeHash s answer) := by
  unfold hashTransfer at step
  cases hsrc : a.getReg .x10 with
  | none => simp [hsrc] at step
  | some source =>
    cases hbits : a.getReg .x11 with
    | none => simp [hsrc, hbits] at step
    | some bits =>
      cases hdst : a.getReg .x12 with
      | none => simp [hsrc, hbits, hdst] at step
      | some destination =>
        by_cases valid : hashGuard source bits destination = true
        · simp [hsrc, hbits, hdst, valid] at step
          rcases step with ⟨rfl, rfl⟩
          have esrc := h.regs .x10 source hsrc
          have ebits := h.regs .x11 bits hbits
          have edst := h.regs .x12 destination hdst
          refine ⟨?_, ?_, forgetHash_models h destination edst answer⟩
          · simpa only [hashArgumentsValid, hashGuard, esrc, ebits, edst] using valid
          · simp only [hashInput, ebits]
        · simp [hsrc, hbits, hdst, valid] at step

end SigGolfCandidate.Resources
