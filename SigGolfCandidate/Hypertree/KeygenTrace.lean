import SigGolfCandidate.Execution

namespace SigGolfCandidate
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 OracleComp

/-- A finite, possibly hashing execution prefix for the organizer's protected interpreter.
Indices record instruction count, cycles, oracle calls, and compressions separately. -/
inductive Trace (hash : Hash) (image : Image) :
    MachineState → Nat → Nat → Nat → Nat → MachineState → Prop where
  | refl (state : MachineState) : Trace hash image state 0 0 0 0 state
  | ordinary (state next final : MachineState) (instruction : Instruction)
      (steps cycles calls blocks : Nat)
      (hf : fetch image state = some instruction)
      (hs : ordinaryStep state instruction = some next)
      (tail : Trace hash image next steps cycles calls blocks final) :
      Trace hash image state (steps + 1) (cycles + 1) calls blocks final
  | hash (state final : MachineState) (steps cycles calls blocks : Nat)
      (hf : fetch image state = some (.base .ECALL))
      (hs : state.getReg .x5 = 1) (hv : hashArgumentsValid state = true)
      (tail : Trace hash image (writeHash state (hash (hashInput state)))
        steps cycles calls blocks final) :
      Trace hash image state (steps + 1)
        (cycles + 8 * compressions (hashInput state).1)
        (calls + 1) (blocks + compressions (hashInput state).1) final

/-- Prefix composition adds every resource counter exactly. -/
theorem Trace.trans {hash : Hash} {image : Image} {s t u : MachineState}
    {steps cycles calls blocks moreSteps moreCycles moreCalls moreBlocks : Nat}
    (first : Trace hash image s steps cycles calls blocks t)
    (second : Trace hash image t moreSteps moreCycles moreCalls moreBlocks u) :
    Trace hash image s (steps + moreSteps) (cycles + moreCycles)
      (calls + moreCalls) (blocks + moreBlocks) u := by
  induction first with
  | refl => simpa using second
  | ordinary state next final instruction steps cycles calls blocks hf hs tail ih =>
    simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
      Trace.ordinary state next u instruction _ _ _ _ hf hs (ih second)
  | hash state final steps cycles calls blocks hf hs hv tail ih =>
    simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
      Trace.hash state u _ _ _ _ hf hs hv (ih second)

/-- Ordinary blocks embed without oracle costs. -/
theorem OrdinarySteps.trace {hash : Hash} {image : Image} {s t : MachineState} {steps : Nat}
    (block : OrdinarySteps image s steps t) : Trace hash image s steps steps 0 0 t := by
  induction block with
  | refl state => exact Trace.refl state
  | step state next final instruction steps hf hs tail ih =>
    exact Trace.ordinary state next final instruction steps steps 0 0 hf hs ih

/-- Any certified prefix followed by a terminating suffix is a certified full execution. -/
theorem Trace.then_executes {hash : Hash} {image : Image} {s t : MachineState}
    {steps cycles calls blocks moreSteps : Nat} {result : Execution}
    (pre : Trace hash image s steps cycles calls blocks t)
    (suffix : Executes hash image t moreSteps result) :
    Executes hash image s (steps + moreSteps) (result.charge cycles calls blocks) := by
  induction pre with
  | refl => simpa [Execution.charge] using suffix
  | ordinary state next final instruction steps cycles calls blocks hf hs tail ih =>
    have he : instruction ≠ .base .ECALL := by
      intro h
      simp [h, ordinaryStep] at hs
    simpa only [Execution.charge, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
      Nat.zero_add, Nat.add_zero] using Executes.ordinary state next instruction _ _ hf he hs (ih suffix)
  | hash state final steps cycles calls blocks hf hs hv tail ih =>
    simpa only [Execution.charge, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      Executes.hash state _ _ hf hs hv (ih suffix)

/-- Prefix soundness, stated directly against the organizer's interpreter and arbitrary extra fuel. -/
theorem Trace.sound {hash : Hash} {image : Image} {s t : MachineState}
    {steps cycles calls blocks moreSteps : Nat} {result : Execution}
    (pre : Trace hash image s steps cycles calls blocks t)
    (suffix : Executes hash image t moreSteps result)
    (fuel : Nat) (enough : steps + moreSteps ≤ fuel) :
    evalWithAnswerFn hash (execute fuel image s) = result.charge cycles calls blocks :=
  (pre.then_executes suffix).sound fuel enough

/-- info: 'SigGolfCandidate.Trace.sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Trace.sound

end SigGolfCandidate
