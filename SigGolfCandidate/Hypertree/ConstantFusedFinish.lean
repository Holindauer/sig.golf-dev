import SigGolfCandidate.Hypertree.Copy6
import SigGolfCandidate.Hypertree.ChainLoopControl
namespace SigGolfCandidate.Hypertree.ConstantFusedFinish
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 Keygen
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
def state (s : MachineState) : MachineState :=
  let s := execInstrBr s (.LUI .x28 128)
  let s := execInstrBr s (.LD .x11 .x28 768)
  let s := execInstrBr s (.SD .x28 .x11 1296)
  let s := execInstrBr s (.LD .x11 .x28 776)
  let s := execInstrBr s (.SD .x28 .x11 1304)
  let s := execInstrBr s (.ADDI .x28 .x28 1080)
  let s := execInstrBr s (.LD .x6 .x28 0)
  let s := execInstrBr s (.ADDI .x6 .x6 1)
  let s := execInstrBr s (.SD .x28 .x6 0)
  execInstrBr s (.JAL .x0 (-148))
theorem state_equiv (s : MachineState) :
    state s = ChainLoopControl.increment (Copy6.optimized s 0x300 0x510) (-184) := by
  cases s
  simp [state, Copy6.optimized, ChainLoopControl.increment, execInstrBr, MachineState.getReg, MachineState.setReg,
    MachineState.getMem, MachineState.setMem, MachineState.setPC, signExtend12, signExtend21, BitVec.add_assoc]
  funext r
  cases r <;> rfl
end SigGolfCandidate.Hypertree.ConstantFusedFinish
