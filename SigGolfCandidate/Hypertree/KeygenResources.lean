import SigGolfCandidate.Hypertree.KeygenResourceCheckpoints
import SigGolfCandidate.Hypertree.KeygenResourceInitial

namespace SigGolfCandidate.Hypertree.KeygenResource
open SigGolfCandidate.Resources SigGolf SigGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096

/-- Every concrete state satisfying the entry abstraction follows the complete exact image.
All seed and oracle-dependent words are universally quantified. -/
theorem executes (hash : Hash) (s : MachineState) (model : initialAbstract.Models s) :
    ∃ final, Executes hash keygen s 75993 ⟨.success, final, 81342, 739, 761⟩ := by
  have initial : state0.Models s := model
  obtain ⟨final, trace, hf⟩ := certifiedPrefix hash s initial
  have pc : final.pc = 0x1044 := hf.pc
  have service : final.getReg .x5 = 0 := hf.regs .x5 0 (by decide)
  have status : final.getReg .x10 = 1 := hf.regs .x10 1 (by decide)
  have code : fetch keygen final = some (.base .ECALL) := by
    simp only [fetch, pc, keygen]
    decide
  refine ⟨final, ?_⟩
  simpa [status, Execution.charge] using trace.then_executes (Executes.halt (hash := hash) final code service)

/-- Exact key-generation resource counts for every seed and every fixed oracle,
through the organizer's loader, protected interpreter, and output decoder. -/
theorem run_bound (hash : Hash) (seed : Seed) :
    let result := submission.runWith hash .keygen seed
    result.finished = true ∧ result.value.isSome = true ∧ result.cycles = 81342 ∧
      result.hashCalls = 739 ∧ result.hashCompressions = 761 := by
  obtain ⟨final, trace⟩ := executes hash (seedState seed) (seed_models seed)
  have run := runWith_of_executes submission hash .keygen seed (seedState seed) 75993
    ⟨.success, final, 81342, 739, 761⟩ (seed_loaded seed) trace (by decide)
  simp [run]

/-- The exact keygen image satisfies the competition's universal strict termination limit. -/
theorem terminates (hash : Hash) (seed : Seed) :
    (submission.runWith hash .keygen seed).finished = true ∧
      (submission.runWith hash .keygen seed).cycles < CYCLE_LIMIT := by
  have bound := run_bound hash seed
  exact ⟨bound.1, by rw [bound.2.2.1]; decide⟩

/-- info: 'SigGolfCandidate.Hypertree.KeygenResource.run_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms run_bound

end SigGolfCandidate.Hypertree.KeygenResource
