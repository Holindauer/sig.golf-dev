import SigGolfCandidate.Hypertree.KeygenTrace
namespace SigGolfCandidate
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64

/-- A trace with explicit region evidence at every fetched instruction; final state is unrestricted. -/
inductive RegionTrace (region : MachineState → Prop) (hash : Hash) (image : Image) :
    MachineState → Nat → Nat → Nat → Nat → MachineState → Prop where
  | refl (state : MachineState) : RegionTrace region hash image state 0 0 0 0 state
  | ordinary (state next final : MachineState) (instruction : Instruction)
      (steps cycles calls blocks : Nat) (inside : region state)
      (hf : fetch image state = some instruction)
      (hs : ordinaryStep state instruction = some next)
      (tail : RegionTrace region hash image next steps cycles calls blocks final) :
      RegionTrace region hash image state (steps + 1) (cycles + instructionCycles instruction) calls blocks final
  | hash (state final : MachineState) (steps cycles calls blocks : Nat) (inside : region state)
      (hf : fetch image state = some (.base .ECALL))
      (hs : state.getReg .x5 = 1) (hv : hashArgumentsValid state = true)
      (tail : RegionTrace region hash image (writeHash state (hash (hashInput state)))
        steps cycles calls blocks final) :
      RegionTrace region hash image state (steps + 1)
        (cycles + 8 * compressions (hashInput state).1)
        (calls + 1) (blocks + compressions (hashInput state).1) final

/-- Fetch agreement transports all four counters without any change in machine states. -/
theorem RegionTrace.transport {region : MachineState → Prop} {hash : Hash}
    {source target : Image} {s t : MachineState} {n c q b : Nat}
    (run : RegionTrace region hash source s n c q b t)
    (agreement : ∀ state, region state → fetch target state = fetch source state) :
    Trace hash target s n c q b t := by
  induction run with
  | refl state => exact Trace.refl state
  | ordinary state next final instruction steps cycles calls blocks inside hf hs tail ih =>
    exact Trace.ordinary state next final instruction steps cycles calls blocks
      ((agreement state inside).trans hf) hs ih
  | hash state final steps cycles calls blocks inside hf hs hv tail ih =>
    exact Trace.hash state final steps cycles calls blocks
      ((agreement state inside).trans hf) hs hv ih

/-- info: 'SigGolfCandidate.RegionTrace.transport' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms RegionTrace.transport
end SigGolfCandidate
