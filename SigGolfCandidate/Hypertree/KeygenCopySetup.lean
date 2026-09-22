import SigGolfCandidate.Hypertree.KeygenCopyFrame

namespace SigGolfCandidate.Hypertree.Keygen
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 OracleComp

/-- Common five-instruction setup for copies between scratch buffers. -/
def CopySetupCode (image : Image) (p : Word) (source destination count : BitVec 12) : Prop :=
  instructionAt image p = some (.base (.LUI .x6 128)) ∧
  instructionAt image (p + 4) = some (.base (.ADDI .x6 .x6 source)) ∧
  instructionAt image (p + 8) = some (.base (.LUI .x7 128)) ∧
  instructionAt image (p + 12) = some (.base (.ADDI .x7 .x7 destination)) ∧
  instructionAt image (p + 16) = some (.base (.ADDI .x10 .x0 count))

instance (image : Image) (p : Word) (source destination count : BitVec 12) :
    Decidable (CopySetupCode image p source destination count) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _))

def copySetup (s : MachineState) (source destination count : BitVec 12) : MachineState :=
  let s := execInstrBr s (.LUI .x6 128)
  let s := execInstrBr s (.ADDI .x6 .x6 source)
  let s := execInstrBr s (.LUI .x7 128)
  let s := execInstrBr s (.ADDI .x7 .x7 destination)
  execInstrBr s (.ADDI .x10 .x0 count)

theorem copy_setup_block (image : Image) (p : Word) (source destination count : BitVec 12)
    (code : CopySetupCode image p source destination count) (s : MachineState) (pc : s.pc = p) :
    OrdinarySteps image s 5 (copySetup s source destination count) := by
  obtain ⟨c0,c1,c2,c3,c4⟩ := code
  let s1 := execInstrBr s (.LUI .x6 128)
  let s2 := execInstrBr s1 (.ADDI .x6 .x6 source)
  let s3 := execInstrBr s2 (.LUI .x7 128)
  let s4 := execInstrBr s3 (.ADDI .x7 .x7 destination)
  apply OrdinarySteps.step s s1 _ (.base (.LUI .x6 128)) 4
  · simpa only [fetch_at, pc] using c0
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.ADDI .x6 .x6 source)) 3
  · simpa only [fetch_at, s1, execInstrBr, MachineState.setPC, pc] using c1
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.LUI .x7 128)) 2
  · have hp : s2.pc = p + 8 := by simp [s1,s2,execInstrBr,pc,BitVec.add_assoc]
    simpa only [fetch_at,hp] using c2
  · rfl
  apply OrdinarySteps.step s3 s4 _ (.base (.ADDI .x7 .x7 destination)) 1
  · have hp : s3.pc = p + 12 := by simp [s1,s2,s3,execInstrBr,pc,BitVec.add_assoc]
    simpa only [fetch_at,hp] using c3
  · rfl
  apply OrdinarySteps.step s4 (copySetup s source destination count) _ (.base (.ADDI .x10 .x0 count)) 0
  · have hp : s4.pc = p + 16 := by simp [s1,s2,s3,s4,execInstrBr,pc,BitVec.add_assoc]
    simpa only [fetch_at,hp] using c4
  · rfl
  exact OrdinarySteps.refl _

theorem copy_setup_pc (s : MachineState) (source destination count : BitVec 12) :
    (copySetup s source destination count).pc = s.pc + 20 := by
  simp [copySetup,execInstrBr,BitVec.add_assoc]

theorem copy_setup_regs (s : MachineState) (source destination count : BitVec 12) :
    (copySetup s source destination count).getReg .x6 = 0x80000 + signExtend12 source ∧
    (copySetup s source destination count).getReg .x7 = 0x80000 + signExtend12 destination ∧
    (copySetup s source destination count).getReg .x10 = signExtend12 count := by
  simp [copySetup,execInstrBr,MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]

theorem copy_setup_mem (s : MachineState) (source destination count : BitVec 12) (a : Word) :
    (copySetup s source destination count).getMem a = s.getMem a := by
  simp [copySetup,execInstrBr]

theorem copy_setup_stack (s : MachineState) (source destination count : BitVec 12) :
    (copySetup s source destination count).getReg .x1 = s.getReg .x1 ∧
    (copySetup s source destination count).getReg .x2 = s.getReg .x2 := by
  simp [copySetup,execInstrBr,MachineState.getReg_setReg_ne]

/-- A complete two-word scratch copy, parameterized by its encoded addresses. -/
theorem copy_two (image : Image) (p : Word) (source destination : BitVec 12)
    (src dst : Nat) (setupCode : CopySetupCode image p source destination 2)
    (copyCode : CopyCode image (p+20))
    (sourceValue : 0x80000 + signExtend12 source = BitVec.ofNat 64 src)
    (destinationValue : 0x80000 + signExtend12 destination = BitVec.ofNat 64 dst)
    (srcbound : src + 16 ≤ MEMORY_BYTES) (dstbound : dst + 16 ≤ MEMORY_BYTES)
    (srcalign : src % 8 = 0) (dstalign : dst % 8 = 0)
    (separate : src + 16 ≤ dst ∨ dst + 16 ≤ src)
    (s : MachineState) (pc : s.pc = p) :
    ∃ final, OrdinarySteps image s 17 final ∧ final.pc = p + 44 ∧
      (∀ i : Fin 2, final.getMem (Signing.wordAddress dst i.val) =
        s.getMem (Signing.wordAddress src i.val)) ∧
      final.getReg .x1 = s.getReg .x1 ∧ final.getReg .x2 = s.getReg .x2 ∧
      (∀ a, (∀ i : Fin 2, a ≠ Signing.wordAddress dst i.val) → final.getMem a = s.getMem a) := by
  let setup := copySetup s source destination 2
  have setupTrace := copy_setup_block image p source destination 2 setupCode s pc
  have inv : CopyInvariant (p+20) src dst 2 2 setup := by
    have regs := copy_setup_regs s source destination 2
    simp only [CopyInvariant,setup,copy_setup_pc,pc,regs.1,regs.2.1,regs.2.2,
      sourceValue,destinationValue]
    simp [signExtend12]
  obtain ⟨copied,trace,done,content,frame,ra,sp⟩ :=
    copy_all_frame image (p+20) copyCode src dst 2 setup inv
      srcbound dstbound srcalign dstalign separate
  refine ⟨copied,ordinary_trans image _ _ _ 5 12 setupTrace trace,?_,?_,
    ra.trans (copy_setup_stack s _ _ _).1,sp.trans (copy_setup_stack s _ _ _).2,?_⟩
  · simpa [BitVec.add_assoc] using done.2.2.1
  · intro i
    rw [content i.val i.isLt]
    exact copy_setup_mem s _ _ _ _
  · intro a outside
    rw [frame a (fun i hi => outside ⟨i,hi⟩)]
    exact copy_setup_mem s _ _ _ _

end SigGolfCandidate.Hypertree.Keygen
