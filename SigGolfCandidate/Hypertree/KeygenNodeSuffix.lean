import SigGolfCandidate.Hypertree.KeygenCopySetup
import SigGolfCandidate.Hypertree.KeygenControl

namespace SigGolfCandidate.Hypertree.KeygenNode
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 OracleComp Keygen

/-- Copy the truncated node answer into CURRENT. -/
def SuffixCode (image : Image) (p : Word) : Prop :=
  CopySetupCode image p 0x300 0x500 2 ∧ CopyCode image (p + 20)

instance (image : Image) (p : Word) : Decidable (SuffixCode image p) :=
  inferInstanceAs (Decidable (_ ∧ _))

theorem copy_answer (image : Image) (p : Word) (code : SuffixCode image p)
    (s : MachineState) (pc : s.pc = p) :
    ∃ final, OrdinarySteps image s 17 final ∧ final.pc = p + 44 ∧
      (∀ i : Fin 2, final.getMem (Signing.wordAddress 0x80500 i.val) =
        s.getMem (Signing.wordAddress 0x80300 i.val)) ∧
      final.getReg .x1 = s.getReg .x1 ∧ final.getReg .x2 = s.getReg .x2 ∧
      (∀ a, (∀ i : Fin 2, a ≠ Signing.wordAddress 0x80500 i.val) → final.getMem a = s.getMem a) := by
  let setup := copySetup s 0x300 0x500 2
  have setupTrace := copy_setup_block image p 0x300 0x500 2 code.1 s pc
  have inv : CopyInvariant (p + 20) 0x80300 0x80500 2 2 setup := by
    have regs := copy_setup_regs s 0x300 0x500 2
    simp only [CopyInvariant,setup,copy_setup_pc,pc,regs.1,regs.2.1,regs.2.2]
    simp [signExtend12]
  obtain ⟨copied,trace,done,content,frame,ra,sp⟩ :=
    copy_all_frame image (p + 20) code.2 0x80300 0x80500 2 setup inv
      (by decide) (by decide) (by decide) (by decide) (by decide)
  refine ⟨copied,ordinary_trans image _ _ _ 5 12 setupTrace trace,?_,?_,
    ra.trans (copy_setup_stack s _ _ _).1,sp.trans (copy_setup_stack s _ _ _).2,?_⟩
  · simpa [BitVec.add_assoc] using done.2.2.1
  · intro i
    rw [content i.val i.isLt]
    exact copy_setup_mem s _ _ _ _
  · intro a outside
    rw [frame a (fun i hi => outside ⟨i,hi⟩)]
    exact copy_setup_mem s _ _ _ _

theorem keygen_suffix_code : SuffixCode keygen 0x1194 := by decide

end SigGolfCandidate.Hypertree.KeygenNode
