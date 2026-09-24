import SigGolf

namespace SigGolfCandidate
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 OracleComp

/-- A finite execution derivation for the organizer's exact raw-bytecode interpreter. -/
inductive Executes (hash : Hash) (image : Image) : MachineState → Nat → Execution → Prop where
  | halt (state : MachineState) (hf : fetch image state = some (.base .ECALL))
      (hs : state.getReg .x5 = 0) :
      Executes hash image state 1
        ⟨if state.getReg .x10 = 1 then .success else .failure, state, 1, 0, 0⟩
  | ordinary (state next : MachineState) (instruction : Instruction) (steps : Nat) (result : Execution)
      (hf : fetch image state = some instruction) (he : instruction ≠ .base .ECALL)
      (hs : ordinaryStep state instruction = some next)
      (tail : Executes hash image next steps result) :
      Executes hash image state (steps + 1) (result.charge 1 0 0)
  | hash (state : MachineState) (steps : Nat) (result : Execution)
      (hf : fetch image state = some (.base .ECALL))
      (hs : state.getReg .x5 = 1) (hv : hashArgumentsValid state = true)
      (tail : Executes hash image (writeHash state (hash (hashInput state))) steps result) :
      Executes hash image state (steps + 1)
        (result.charge (8 * compressions (hashInput state).1) 1 (compressions (hashInput state).1))

/-- More observation fuel does not change a certified finite execution. -/
theorem Executes.sound {hash : Hash} {image : Image} {state : MachineState} {steps : Nat}
    {result : Execution} (derivation : Executes hash image state steps result) :
    ∀ fuel, steps ≤ fuel → evalWithAnswerFn hash (execute fuel image state) = result := by
  induction derivation with
  | halt state hf hs =>
    intro fuel h
    cases fuel with
    | zero => omega
    | succ fuel => simp [execute, hf, hs]
  | ordinary state next instruction steps result hf he hs tail ih =>
    intro fuel h
    cases fuel with
    | zero => omega
    | succ fuel =>
      have hstep : steps ≤ fuel := by omega
      cases instruction with
      | base instruction =>
        cases instruction <;> simp_all [execute]
      | word op rd rs1 rs2 => simp [execute, hf, hs, ih fuel hstep]
      | sraiw rd rs shift => simp [execute, hf, hs, ih fuel hstep]
  | hash state steps result hf hs hv tail ih =>
    intro fuel h
    cases fuel with
    | zero => omega
    | succ fuel =>
      have hstep : steps ≤ fuel := by omega
      have answer : evalWithAnswerFn hash (liftM (HashSpec.query (hashInput state))) =
          hash (hashInput state) := by simp [evalWithAnswerFn]
      simp [execute, hf, hs, hv, answer, ih fuel hstep]

/-- A block of ordinary instructions, with each fetch and memory check certified. -/
inductive OrdinarySteps (image : Image) : MachineState → Nat → MachineState → Prop where
  | refl (state : MachineState) : OrdinarySteps image state 0 state
  | step (state next final : MachineState) (instruction : Instruction) (steps : Nat)
      (hf : fetch image state = some instruction)
      (hs : ordinaryStep state instruction = some next)
      (tail : OrdinarySteps image next steps final) :
      OrdinarySteps image state (steps + 1) final

theorem OrdinarySteps.then_executes {hash : Hash} {image : Image} {state next : MachineState}
    {count steps : Nat} {result : Execution} (block : OrdinarySteps image state count next)
    (tail : Executes hash image next steps result) :
    Executes hash image state (steps + count) (result.charge count 0 0) := by
  induction block with
  | refl => simpa [Execution.charge] using tail
  | step state next final instruction count hf hs block ih =>
    have he : instruction ≠ .base .ECALL := by
      intro h
      simp [h, ordinaryStep] at hs
    have trace := Executes.ordinary state next instruction _ _ hf he hs (ih tail)
    simpa [Execution.charge, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using trace

private theorem load_buffers_pc (buffers : List (Nat × List Byte)) (state : MachineState) :
    (buffers.foldl (fun state buffer => state.writeBytesAsWords (BitVec.ofNat 64 buffer.1) buffer.2) state).pc = state.pc := by
  induction buffers generalizing state with
  | nil => rfl
  | cons head tail ih => simp only [List.foldl_cons, ih, MachineState.pc_writeBytesAsWords]

/-- Every admitted input starts at the entry point, independently of its contents. -/
theorem initialState_exists (submission : Submission) (admitted : submission.Admissible)
    (phase : Phase) (input : Input submission.sizes phase) :
    ∃ state, initialState submission phase input = some state ∧ state.pc = 0x1000 := by
  unfold initialState
  rw [if_pos (admitted.2 phase)]
  refine ⟨_, rfl, ?_⟩
  simp only [MachineState.pc_setReg, load_buffers_pc, MachineState.pc_writeBytesAsWords]

/-- Lift an execution derivation through the organizer's loader and output convention. -/
theorem runWith_of_executes (submission : Submission) (hash : Hash) (phase : Phase)
    (input : Input submission.sizes phase) (state : MachineState) (steps : Nat) (result : Execution)
    (loaded : initialState submission phase input = some state)
    (derivation : Executes hash (submission.image phase) state steps result)
    (limit : steps ≤ CYCLE_LIMIT) :
    submission.runWith hash phase input =
      ⟨if result.exit = .success then some (readOutput submission.sizes submission.layout phase result.state) else none,
        result.exit != .unfinished, result.cycles, result.hashCalls, result.hashCompressions⟩ := by
  simp [Submission.runWith, Submission.run, loaded, derivation.sound CYCLE_LIMIT limit]

/-- info: 'SigGolfCandidate.Executes.sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Executes.sound

end SigGolfCandidate
