import SigGolfCandidate.Hypertree.KeygenNodePrepare
import SigGolfCandidate.Hypertree.KeygenCopySetup

namespace SigGolfCandidate.Hypertree.KeygenNode
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 OracleComp Keygen
set_option maxRecDepth 4096

/-- The common node-hash prefix, including the child-pair copy loop. -/
def PrefixCode (image : Image) (p : Word) : Prop :=
  CopySetupCode image p 0x520 0x20 4 ∧
  CopyCode image (p + 20) ∧ HeaderCode image (p + 44)

instance (image : Image) (p : Word) : Decidable (PrefixCode image p) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- Its 62 executed instructions produce the exact node query and preserve the stack. -/
theorem prepare (image : Image) (p : Word) (code : PrefixCode image p)
    (s : MachineState) (pc : s.pc = p) (level tree : Nat) (left right : Reference.Digest)
    (hlevel : s.getMem 0x80400 = BitVec.ofNat 64 level)
    (hindex : ∀ i : Fin 3, s.getMem (Signing.wordAddress 0x80408 i.val) =
      (BitVec.ofNat 192 tree).extractLsb' (64 * i.val) 64)
    (hchildren : ∀ i : Fin 4, s.getMem (Signing.wordAddress 0x80520 i.val) =
      if i.val < 2 then left.extractLsb' (64 * i.val) 64
      else right.extractLsb' (64 * (i.val - 2)) 64) :
    ∃ final, OrdinarySteps image s 62 final ∧ final.pc = p + 176 ∧
      final.getReg .x5 = 1 ∧ final.getReg .x10 = 0x80000 ∧
      final.getReg .x11 = 512 ∧ final.getReg .x12 = 0x80300 ∧
      (∀ i : Fin 8, final.getMem (Signing.wordAddress 0x80000 i.val) =
        inputWord level tree left right i) ∧
      final.getReg .x1 = s.getReg .x1 ∧ final.getReg .x2 = s.getReg .x2 ∧
      (∀ a, (∀ i : Fin 8, a ≠ Signing.wordAddress 0x80000 i.val) →
        final.getMem a = s.getMem a) := by
  let setup := copySetup s 0x520 0x20 4
  have setupTrace := copy_setup_block image p 0x520 0x20 4 code.1 s pc
  have inv : CopyInvariant (p + 20) 0x80520 0x80020 4 4 setup := by
    have regs := copy_setup_regs s 0x520 0x20 4
    simp only [CopyInvariant, setup, copy_setup_pc, pc, regs.1, regs.2.1, regs.2.2]
    simp [signExtend12]
  obtain ⟨copied, copyTrace, done, content, frame, ra, sp⟩ :=
    copy_all_frame image (p + 20) code.2.1 0x80520 0x80020 4 setup inv
      (by decide) (by decide) (by decide) (by decide) (by decide)
  have copiedPC : copied.pc = p + 44 := by
    simpa [BitVec.add_assoc] using done.2.2.1
  have frameWord (a : Word) (outside : ∀ i, i < 4 → a ≠ Signing.wordAddress 0x80020 i) :
      copied.getMem a = s.getMem a := by
    rw [frame a outside]
    exact copy_setup_mem s _ _ _ a
  have copiedLevel : copied.getMem 0x80400 = BitVec.ofNat 64 level := by
    rw [frameWord 0x80400 (by intro i hi; interval_cases i <;> decide)]
    exact hlevel
  have copiedIndex : ∀ i : Fin 3, copied.getMem (Signing.wordAddress 0x80408 i.val) =
      (BitVec.ofNat 192 tree).extractLsb' (64 * i.val) 64 := by
    intro i
    rw [frameWord _ (by intro j hj; fin_cases i <;> interval_cases j <;> decide)]
    exact hindex i
  have children : ∀ i : Fin 4, copied.getMem (Signing.wordAddress 0x80020 i.val) =
      if i.val < 2 then left.extractLsb' (64 * i.val) 64
      else right.extractLsb' (64 * (i.val - 2)) 64 := by
    intro i
    rw [content i.val i.isLt, copy_setup_mem]
    exact hchildren i
  have block := header_block image (p + 44) code.2.2 copied copiedPC
  refine ⟨headerState copied, ?_, ?_, (header_regs copied).1,
    (header_regs copied).2.1, (header_regs copied).2.2.1,
    (header_regs copied).2.2.2, header_words copied level tree left right copiedLevel copiedIndex children,
    (header_stack copied).1.trans (ra.trans (copy_setup_stack s _ _ _).1),
    (header_stack copied).2.trans (sp.trans (copy_setup_stack s _ _ _).2), ?_⟩
  · exact ordinary_trans image _ _ _ 29 33
      (ordinary_trans image _ _ _ 5 24 setupTrace copyTrace) block
  · rw [header_pc, copiedPC]
    simp [BitVec.add_assoc]
  · intro a outside
    have h0 : a ≠ (0x80000 : Word) := outside 0
    have h1 : a ≠ (0x80008 : Word) := outside 1
    have h2 : a ≠ (0x80010 : Word) := outside 2
    have h3 : a ≠ (0x80018 : Word) := outside 3
    rw [header_mem]
    simp only [h0,h1,h2,h3, ↓reduceIte]
    apply frameWord
    intro i hi
    have out := outside ⟨i+4, by omega⟩
    simpa [Signing.wordAddress, Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using out

theorem keygen_prefix_code : PrefixCode keygen 0x10e0 := by decide

end SigGolfCandidate.Hypertree.KeygenNode
