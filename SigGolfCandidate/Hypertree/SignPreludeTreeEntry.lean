import SigGolfCandidate.Hypertree.SignPreludeEncode
namespace SigGolfCandidate.Hypertree.Signing
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 OracleComp Keygen

/-- The encoder's low-word frame preserves all tree metadata and secret words. -/
theorem encode_tree_context (s final : MachineState) (secretKey : SecretKey)
    (data : TreeContext s secretKey 159 0)
    (frame : ∀ a : Nat, a % 8 = 0 → a + 8 ≤ 0x80600 →
      final.getMem (BitVec.ofNat 64 a) = s.getMem (BitVec.ofNat 64 a)) :
    TreeContext final secretKey 159 0 := by
  constructor
  · change final.getMem (BitVec.ofNat 64 0x80400) = _
    rw [frame 0x80400 (by decide) (by decide)]; exact data.levelEq
  · intro i
    change final.getMem (BitVec.ofNat 64 (0x80408 + 8 * i.val)) = _
    rw [frame _ (by fin_cases i <;> decide) (by fin_cases i <;> decide)]
    exact data.indexEq i
  · intro i
    change final.getMem (BitVec.ofNat 64 (0x20 + 8 * i.val)) = _
    rw [frame _ (by fin_cases i <;> decide) (by fin_cases i <;> decide)]
    exact data.secretKeyEq i

def deriveTreeCall (s : MachineState) : MachineState :=
  execInstrBr s (.JAL .x1 (-2272))

theorem deriveTreeCall_block (image : Image)
    (code : instructionAt image 0x1ca8 = some (.base (.JAL .x1 (-2272))))
    (s : MachineState) (pc : s.pc = 0x1ca8) :
    OrdinarySteps image s 1 (deriveTreeCall s) := by
  apply OrdinarySteps.step s (deriveTreeCall s) _ (.base (.JAL .x1 (-2272))) 0
  · rw [fetch_at, pc]; exact code
  · rfl
  exact OrdinarySteps.refl _

theorem deriveTreeCall_pc (s : MachineState) (pc : s.pc = 0x1ca8) :
    (deriveTreeCall s).pc = 0x13c8 := by
  simp [deriveTreeCall, execInstrBr, pc, signExtend21]

theorem deriveTreeCall_return (s : MachineState) (pc : s.pc = 0x1ca8) :
    (deriveTreeCall s).getReg .x1 = 0x1cac := by
  simp [deriveTreeCall, execInstrBr, pc, MachineState.getReg_setReg_eq]

theorem deriveTreeCall_mem (s : MachineState) (a : Word) :
    (deriveTreeCall s).getMem a = s.getMem a := by
  simp [deriveTreeCall, execInstrBr]

theorem deriveTreeCall_byte (s : MachineState) (a : Word) :
    (deriveTreeCall s).getByte a = s.getByte a := by
  simp [deriveTreeCall, execInstrBr, MachineState.getByte, MachineState.getMem, MachineState.setReg, MachineState.setPC]

theorem deriveTreeCall_stack (s : MachineState) :
    (deriveTreeCall s).getReg .x2 = s.getReg .x2 := by
  simp [deriveTreeCall, execInstrBr, MachineState.getReg_setReg_ne]

theorem deriveTreeCall_context (s : MachineState) (secretKey : SecretKey)
    (data : TreeContext s secretKey 159 0) :
    TreeContext (deriveTreeCall s) secretKey 159 0 := by
  constructor
  · rw [deriveTreeCall_mem]; exact data.levelEq
  · intro i; rw [deriveTreeCall_mem]; exact data.indexEq i
  · intro i; rw [deriveTreeCall_mem]; exact data.secretKeyEq i

/-- info: 'SigGolfCandidate.Hypertree.Signing.encode_tree_context' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms encode_tree_context
/-- info: 'SigGolfCandidate.Hypertree.Signing.deriveTreeCall_block' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms deriveTreeCall_block
end SigGolfCandidate.Hypertree.Signing
