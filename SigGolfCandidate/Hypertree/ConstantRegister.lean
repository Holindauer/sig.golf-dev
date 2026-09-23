import SigGolfCandidate.Hypertree.ConstantInvariant
namespace SigGolfCandidate.Hypertree.ConstantRegister
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 Keygen
theorem ConstantPrepare_preserves (s : MachineState) : (ConstantPrepare.state s).getReg .x13 = s.getReg .x13 := by
  simp [ConstantPrepare.state, execInstrBr, MachineState.getReg_setReg_ne]
theorem ConstantFinish_preserves (s : MachineState) : (ConstantFinish.finish s).getReg .x13 = s.getReg .x13 := by
  simp [ConstantFinish.finish, execInstrBr, MachineState.getReg_setReg_ne]
theorem ConstantCheck_preserves (s : MachineState) : (ConstantCheck.shortCheck s).getReg .x13 = s.getReg .x13 := by
  simp [ConstantCheck.shortCheck, execInstrBr, MachineState.getReg_setReg_ne]
end SigGolfCandidate.Hypertree.ConstantRegister
