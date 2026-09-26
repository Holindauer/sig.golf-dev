import SigGolfCandidate.Hypertree.KeygenControl
import SigGolfCandidate.Hypertree.TraceTransport
namespace SigGolfCandidate.Hypertree.Keygen
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
set_option maxRecDepth 4096

theorem enter_region (region : Word → Prop) (hash : Hash) (image : Image) (p : Word) (code : EnterCode image p)
    (inside : ∀ i : Fin 2, region (p + BitVec.ofNat 64 (4 * i.val)))
    (s : MachineState) (pc : s.pc = p)
    (stack : accessValid (s.getReg .x2 - 16) 8 = true) :
    RegionTrace (fun st => region st.pc) hash image s 2 2 0 0 (enterState s) := by
  apply RegionTrace.step s (execInstrBr s (.ADDI .x2 .x2 (-16))) _
    (.base (.ADDI .x2 .x2 (-16))) 1
  · simpa [execInstrBr, pc, BitVec.add_assoc] using inside 0
  · simpa only [fetch_at, pc] using code.1
  · rfl
  apply RegionTrace.step _ (enterState s) _ (.base (.SD .x2 .x1 0)) 0
  · simpa [execInstrBr, pc, BitVec.add_assoc] using inside 1
  · simpa only [fetch_at, execInstrBr, MachineState.setPC, pc] using code.2
  · simpa [enterState, ordinaryStep, memoryArgumentsValid, execInstrBr,
      signExtend12, MachineState.getReg_setReg_eq, BitVec.sub_eq_add_neg] using stack
  exact RegionTrace.refl _

theorem return_region (region : Word → Prop) (hash : Hash) (image : Image) (p : Word) (code : ReturnCode image p)
    (inside : ∀ i : Fin 3, region (p + BitVec.ofNat 64 (4 * i.val)))
    (s : MachineState) (pc : s.pc = p)
    (stack : accessValid (s.getReg .x2) 8 = true) :
    RegionTrace (fun st => region st.pc) hash image s 3 3 0 0 (returnState s) := by
  let s1 := execInstrBr s (.LD .x1 .x2 0)
  let s2 := execInstrBr s1 (.ADDI .x2 .x2 16)
  apply RegionTrace.step s s1 _ (.base (.LD .x1 .x2 0)) 2
  · simpa [execInstrBr, pc, BitVec.add_assoc] using inside 0
  · simpa only [fetch_at, pc] using code.1
  · simp [s1, ordinaryStep, memoryArgumentsValid, signExtend12, stack]
  apply RegionTrace.step s1 s2 _ (.base (.ADDI .x2 .x2 16)) 1
  · simpa [s1, execInstrBr, pc, BitVec.add_assoc] using inside 1
  · simpa only [fetch_at, s1, execInstrBr, MachineState.setPC, pc] using code.2.1
  · rfl
  apply RegionTrace.step s2 (returnState s) _ (.base (.JALR .x0 .x1 0)) 0
  · simpa [s1, s2, execInstrBr, pc, BitVec.add_assoc] using inside 2
  · simpa [fetch_at, s1, s2, execInstrBr, MachineState.setPC, pc, BitVec.add_assoc] using code.2.2
  · rfl
  exact RegionTrace.refl _

/-- info: 'SigGolfCandidate.Hypertree.Keygen.enter_region' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms enter_region
/-- info: 'SigGolfCandidate.Hypertree.Keygen.return_region' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms return_region
end SigGolfCandidate.Hypertree.Keygen
