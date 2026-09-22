import SigGolfCandidate.Hypertree.ResourceHash

namespace SigGolfCandidate.Resources
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 OracleComp

structure Summary where
  next : AbstractState
  cycles : Nat
  calls : Nat
  blocks : Nat
  deriving DecidableEq, Repr

def baseAt (image : Image) (pc : Word) : Option Instr := do
  match ← Hypertree.Keygen.instructionAt image pc with
  | .base instruction => some instruction
  | _ => none

theorem baseAt_some (image : Image) (a : AbstractState) (s : MachineState) (h : a.Models s)
    (instruction : Instr) (decoded : baseAt image a.pc = some instruction) :
    fetch image s = some (.base instruction) := by
  unfold baseAt at decoded
  cases hf : Hypertree.Keygen.instructionAt image a.pc with
  | none => simp [hf] at decoded
  | some i =>
    cases i with
    | base i =>
      simp [hf] at decoded
      subst i
      simpa only [Hypertree.Keygen.fetch_at, h.pc] using hf
    | word op rd rs1 rs2 => simp [hf] at decoded
    | sraiw rd rs n => simp [hf] at decoded

/-- HALT is deliberately excluded from prefixes and certified separately. -/
def stepTransfer (image : Image) (a : AbstractState) : Option Summary := do
  let instruction ← baseAt image a.pc
  if instruction = .ECALL then
    if a.getReg .x5 = some 1 then
      let (next, blocks) ← hashTransfer a
      some ⟨next, 8 * blocks, 1, blocks⟩
    else none
  else
    let next ← ordinaryTransfer a instruction
    some ⟨next, 1, 0, 0⟩

theorem stepTransfer_sound {image : Image} {a : AbstractState} {result : Summary}
    (hash : Hash) (s : MachineState) (h : a.Models s)
    (step : stepTransfer image a = some result) :
    ∃ t, Trace hash image s 1 result.cycles result.calls result.blocks t ∧ result.next.Models t := by
  unfold stepTransfer at step
  cases hi : baseAt image a.pc with
  | none => simp [hi] at step
  | some instruction =>
    have hf := baseAt_some image a s h instruction hi
    by_cases he : instruction = .ECALL
    · subst instruction
      by_cases hs : a.getReg .x5 = some 1
      · cases ht : hashTransfer a with
        | none => simp [hi, hs, ht] at step
        | some pair =>
          rcases pair with ⟨next, blocks⟩
          simp [hi, hs, ht] at step
          subst result
          obtain ⟨valid, cost, model⟩ := hashTransfer_sound h ht (hash (hashInput s))
          refine ⟨writeHash s (hash (hashInput s)), ?_, model⟩
          have trace := Trace.hash (hash := hash) s (writeHash s (hash (hashInput s)))
            0 0 0 0 hf (h.regs .x5 1 hs) valid (Trace.refl _)
          simpa only [cost, Nat.zero_add] using trace
      · simp [hi] at step
        exact (hs step.1).elim
    · cases ht : ordinaryTransfer a instruction with
      | none => simp [hi, he, ht] at step
      | some next =>
        simp [hi, he, ht] at step
        subst result
        obtain ⟨valid, model⟩ := ordinaryTransfer_sound h instruction ht
        exact ⟨execInstrBr s instruction,
          Trace.ordinary s (execInstrBr s instruction) _ (.base instruction)
            0 0 0 0 hf valid (Trace.refl _), model⟩

/-- A bounded abstract prefix evaluator. Every accepted step has a concrete proof rule. -/
def runPrefix : Nat → Image → AbstractState → Option Summary
  | 0, _, a => some ⟨a, 0, 0, 0⟩
  | n + 1, image, a => do
      let first ← stepTransfer image a
      let rest ← runPrefix n image first.next
      some ⟨rest.next, first.cycles + rest.cycles,
        first.calls + rest.calls, first.blocks + rest.blocks⟩

theorem runPrefix_sound {image : Image} {a : AbstractState} {result : Summary}
    (n : Nat) (hash : Hash) (s : MachineState) (h : a.Models s)
    (run : runPrefix n image a = some result) :
    ∃ t, Trace hash image s n result.cycles result.calls result.blocks t ∧ result.next.Models t := by
  induction n generalizing a s result with
  | zero =>
    simp only [runPrefix, Option.some.injEq] at run
    subst result
    exact ⟨s, Trace.refl _, h⟩
  | succ n ih =>
    simp only [runPrefix] at run
    cases hs : stepTransfer image a with
    | none => simp [hs] at run
    | some first =>
      cases hr : runPrefix n image first.next with
      | none => simp [hs, hr] at run
      | some rest =>
        simp [hs, hr] at run
        subst result
        obtain ⟨mid, firstTrace, hm⟩ := stepTransfer_sound hash s h hs
        obtain ⟨t, restTrace, ht⟩ := ih mid hm hr
        refine ⟨t, ?_, ht⟩
        simpa only [Nat.add_comm 1 n] using firstTrace.trans restTrace

/-- A resource-exact prefix certificate, universally quantified over concrete state and oracle. -/
def CertifiedPrefix (image : Image) (a b : AbstractState) (steps cycles calls blocks : Nat) : Prop :=
  ∀ (hash : Hash) (s : MachineState), a.Models s →
    ∃ t, Trace hash image s steps cycles calls blocks t ∧ b.Models t

theorem CertifiedPrefix.of_run {image : Image} {a : AbstractState} {result : Summary} {n : Nat}
    (checked : runPrefix n image a = some result) :
    CertifiedPrefix image a result.next n result.cycles result.calls result.blocks := by
  intro hash s h
  exact runPrefix_sound n hash s h checked

theorem CertifiedPrefix.trans {image : Image} {a b c : AbstractState}
    {n cycles calls blocks m moreCycles moreCalls moreBlocks : Nat}
    (first : CertifiedPrefix image a b n cycles calls blocks)
    (second : CertifiedPrefix image b c m moreCycles moreCalls moreBlocks) :
    CertifiedPrefix image a c (n + m) (cycles + moreCycles) (calls + moreCalls) (blocks + moreBlocks) := by
  intro hash s h
  obtain ⟨mid, trace1, hm⟩ := first hash s h
  obtain ⟨t, trace2, ht⟩ := second hash mid hm
  exact ⟨t, trace1.trans trace2, ht⟩

/-- info: 'SigGolfCandidate.Resources.runPrefix_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms runPrefix_sound

end SigGolfCandidate.Resources
