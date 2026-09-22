import SigGolfCandidate.Hypertree.SignSiblingRun
import SigGolfCandidate.Hypertree.VerifyNode

namespace SigGolfCandidate.Hypertree.Verifying
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 Expansion Keygen Signing
set_option maxRecDepth 4096

/-- Verification copies the sibling from the witness into the other public-child slot. -/
def siblingLoadState (s : MachineState) : MachineState :=
  let s := execInstrBr s (.LD .x11 .x10 0)
  let s := execInstrBr s (.LD .x12 .x10 8)
  let s := execInstrBr s (.SD .x7 .x11 0)
  execInstrBr s (.SD .x7 .x12 8)

theorem siblingLoad_block (s : MachineState) (pc : s.pc = 0x135c)
    (src : accessValid (s.getReg .x10) 8 = true)
    (srcNext : accessValid (s.getReg .x10 + 8) 8 = true)
    (dst : accessValid (s.getReg .x7) 8 = true)
    (dstNext : accessValid (s.getReg .x7 + 8) 8 = true) :
    OrdinarySteps verify s 4 (siblingLoadState s) := by
  let s1 := execInstrBr s (.LD .x11 .x10 0)
  let s2 := execInstrBr s1 (.LD .x12 .x10 8)
  let s3 := execInstrBr s2 (.SD .x7 .x11 0)
  let s4 := execInstrBr s3 (.SD .x7 .x12 8)
  apply OrdinarySteps.step s s1 _ (.base (.LD .x11 .x10 0)) 3
  · have hp : s.pc = 0x135c := by exact pc
    rw [fetch_at, hp]
    decide
  · simp [s1, ordinaryStep, memoryArgumentsValid, execInstrBr, signExtend12, src]
  apply OrdinarySteps.step s1 s2 _ (.base (.LD .x12 .x10 8)) 2
  · have hp : s1.pc = 0x1360 := by simp [s1, execInstrBr, pc]
    rw [fetch_at, hp]
    decide
  · simpa [s1, s2, ordinaryStep, memoryArgumentsValid, execInstrBr, signExtend12, src, srcNext, dst, dstNext, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s2 s3 _ (.base (.SD .x7 .x11 0)) 1
  · have hp : s2.pc = 0x1364 := by simp [s1, s2, execInstrBr, pc]
    rw [fetch_at, hp]
    decide
  · simp [s1, s2, s3, ordinaryStep, memoryArgumentsValid, execInstrBr, signExtend12, dst, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s3 s4 _ (.base (.SD .x7 .x12 8)) 0
  · have hp : s3.pc = 0x1368 := by simp [s1, s2, s3, execInstrBr, pc]
    rw [fetch_at, hp]
    decide
  · simpa [s1, s2, s3, s4, ordinaryStep, memoryArgumentsValid, execInstrBr, signExtend12, src, srcNext, dst, dstNext, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  exact OrdinarySteps.refl _

theorem siblingLoad_pc (s : MachineState) : (siblingLoadState s).pc = s.pc + 16 := by
  simp [siblingLoadState, execInstrBr, BitVec.add_assoc]

theorem siblingLoad_mem (s : MachineState) (a : Word) :
    (siblingLoadState s).getMem a =
      if a = s.getReg .x7 + 8 then s.getMem (s.getReg .x10 + 8) else
      if a = s.getReg .x7 then s.getMem (s.getReg .x10) else s.getMem a := by
  simp [siblingLoadState, execInstrBr, signExtend12, mem_setMem,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]

theorem siblingLoad_sp (s : MachineState) :
    (siblingLoadState s).getReg .x2 = s.getReg .x2 := by
  simp [siblingLoadState, execInstrBr, MachineState.getReg_setReg_ne]

def siblingLoaded (s : MachineState) : MachineState := siblingLoadState (siblingPrepared s)

theorem load_sibling (s : MachineState) (pc : s.pc = 0x1314)
    (src : accessValid (siblingDestination s) 8 = true)
    (srcNext : accessValid (siblingDestination s + 8) 8 = true)
    (dst : accessValid (siblingSource s) 8 = true)
    (dstNext : accessValid (siblingSource s + 8) 8 = true) :
    OrdinarySteps verify s (if s.getMem 0x80400 = 0 then 20 else 21) (siblingLoaded s) := by
  have pre := siblingPrepared_block verify 0x1314 verify_sibling_prepare_code s pc
  have copy := siblingLoad_block (siblingPrepared s)
    (by simpa using siblingPrepared_pc s 0x1314 pc)
    (by simpa only [siblingPrepared_regs] using src)
    (by simpa only [siblingPrepared_regs] using srcNext)
    (by simpa only [siblingPrepared_regs] using dst)
    (by simpa only [siblingPrepared_regs] using dstNext)
  have all := ordinary_trans verify s _ _ _ 4 pre copy
  have count : 4 + (if s.getMem 0x80400 = 0 then 16 else 17) =
      (if s.getMem 0x80400 = 0 then 20 else 21) := by split <;> rfl
  rw [count] at all
  exact all

theorem siblingLoaded_pc (s : MachineState) (pc : s.pc = 0x1314) :
    (siblingLoaded s).pc = 0x136c := by
  rw [siblingLoaded, siblingLoad_pc, siblingPrepared_pc s 0x1314 pc]
  rfl

theorem siblingLoaded_mem (s : MachineState) (a : Word) :
    (siblingLoaded s).getMem a =
      if a = siblingSource s + 8 then s.getMem (siblingDestination s + 8) else
      if a = siblingSource s then s.getMem (siblingDestination s) else s.getMem a := by
  simp only [siblingLoaded, siblingLoad_mem, siblingPrepared_regs, siblingPrepared_mem]

theorem siblingLoaded_sp (s : MachineState) :
    (siblingLoaded s).getReg .x2 = s.getReg .x2 := by
  rw [siblingLoaded, siblingLoad_sp, siblingPrepared_sp]

/-- info: 'SigGolfCandidate.Hypertree.Verifying.load_sibling' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms load_sibling

end SigGolfCandidate.Hypertree.Verifying
