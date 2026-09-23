import SigGolfCandidate.Hypertree.KeygenCopyFrame

namespace SigGolfCandidate.Hypertree.KeygenSecretKey
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 OracleComp Keygen

def Code (image : Image) (p : Word) : Prop :=
  instructionAt image p = some (.base (.ADDI .x6 .x0 0x20)) ∧
  instructionAt image (p+4) = some (.base (.LUI .x7 128)) ∧
  instructionAt image (p+8) = some (.base (.ADDI .x7 .x7 0x20)) ∧
  instructionAt image (p+12) = some (.base (.ADDI .x10 .x0 4)) ∧
  CopyCode image (p+16)

instance (image : Image) (p : Word) : Decidable (Code image p) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _))

def setup (s : MachineState) : MachineState :=
  let s := execInstrBr s (.ADDI .x6 .x0 0x20)
  let s := execInstrBr s (.LUI .x7 128)
  let s := execInstrBr s (.ADDI .x7 .x7 0x20)
  execInstrBr s (.ADDI .x10 .x0 4)

theorem setup_block (image : Image) (p : Word) (code : Code image p)
    (s : MachineState) (pc : s.pc = p) : OrdinarySteps image s 4 (setup s) := by
  let s1 := execInstrBr s (.ADDI .x6 .x0 0x20)
  let s2 := execInstrBr s1 (.LUI .x7 128)
  let s3 := execInstrBr s2 (.ADDI .x7 .x7 0x20)
  apply OrdinarySteps.step s s1 _ (.base (.ADDI .x6 .x0 0x20)) 3
  · simpa only [fetch_at,pc] using code.1
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.LUI .x7 128)) 2
  · simpa only [fetch_at,s1,execInstrBr,MachineState.setPC,pc] using code.2.1
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.ADDI .x7 .x7 0x20)) 1
  · have hp : s2.pc = p+8 := by simp [s1,s2,execInstrBr,pc,BitVec.add_assoc]
    simpa only [fetch_at,hp] using code.2.2.1
  · rfl
  apply OrdinarySteps.step s3 (setup s) _ (.base (.ADDI .x10 .x0 4)) 0
  · have hp : s3.pc = p+12 := by simp [s1,s2,s3,execInstrBr,pc,BitVec.add_assoc]
    simpa only [fetch_at,hp] using code.2.2.2.1
  · rfl
  exact OrdinarySteps.refl _

theorem setup_pc (s : MachineState) : (setup s).pc = s.pc+16 := by
  simp [setup,execInstrBr,BitVec.add_assoc]

theorem setup_regs (s : MachineState) :
    (setup s).getReg .x6 = 0x20 ∧ (setup s).getReg .x7 = 0x80020 ∧ (setup s).getReg .x10 = 4 := by
  simp [setup,execInstrBr,signExtend12,MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]

theorem setup_mem (s : MachineState) (a : Word) : (setup s).getMem a = s.getMem a := by
  simp [setup,execInstrBr]

theorem setup_stack (s : MachineState) :
    (setup s).getReg .x1 = s.getReg .x1 ∧ (setup s).getReg .x2 = s.getReg .x2 := by
  simp [setup,execInstrBr,MachineState.getReg_setReg_ne]

/-- The exact secret key copy makes both 64-bit words available to the secret HASH. -/
theorem copy (image : Image) (p : Word) (code : Code image p)
    (s : MachineState) (pc : s.pc = p) :
    ∃ final, OrdinarySteps image s 28 final ∧ final.pc = p+40 ∧
      (∀ i : Fin 4, final.getMem (Signing.wordAddress 0x80020 i.val) =
        s.getMem (Signing.wordAddress 0x20 i.val)) ∧
      final.getReg .x1 = s.getReg .x1 ∧ final.getReg .x2 = s.getReg .x2 ∧
      (∀ a, (∀ i : Fin 4, a ≠ Signing.wordAddress 0x80020 i.val) → final.getMem a = s.getMem a) := by
  have inv : CopyInvariant (p+16) 0x20 0x80020 4 4 (setup s) := by
    have regs := setup_regs s
    simp [CopyInvariant,setup_pc,pc,regs.1,regs.2.1,regs.2.2]
  obtain ⟨final,trace,done,content,frame,ra,sp⟩ :=
    copy_all_frame image (p+16) code.2.2.2.2 0x20 0x80020 4 (setup s) inv
      (by decide) (by decide) (by decide) (by decide) (by decide)
  refine ⟨final,ordinary_trans image _ _ _ 4 24 (setup_block image p code s pc) trace,?_,?_,
    ra.trans (setup_stack s).1,sp.trans (setup_stack s).2,?_⟩
  · simpa [BitVec.add_assoc] using done.2.2.1
  · intro i
    rw [content i.val i.isLt,setup_mem]
  · intro a outside
    rw [frame a (fun i hi => outside ⟨i,hi⟩),setup_mem]

theorem keygen_code : Code keygen 0x1204 := by decide

end SigGolfCandidate.Hypertree.KeygenSecretKey
