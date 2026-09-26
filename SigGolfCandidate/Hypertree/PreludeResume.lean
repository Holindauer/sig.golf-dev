import SigGolfCandidate.Hypertree.SignResume
import SigGolfCandidate.Hypertree.SignPreludeFetch
namespace SigGolfCandidate.Hypertree.Signing.Prelude
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 Keygen
set_option maxRecDepth 4096

theorem resumed_initialization (s : MachineState) (pc : s.pc = 0x1004)
    (ready : s.getReg .x6 = 1) :
    OrdinarySteps signPrelude s 12 (initializeState (s.setPC 0x1000)) := by
  have block := initializeTail_block signPrelude (fun p low high =>
    prelude_body_fetch { regs := fun _ => 0, mem := fun _ => 0, pc := p }
      low (by dsimp; omega)) s pc
  rw [initializeTail_equiv s ready, pc] at block
  exact block

/-- info: 'SigGolfCandidate.Hypertree.Signing.Prelude.resumed_initialization' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms resumed_initialization
end SigGolfCandidate.Hypertree.Signing.Prelude
