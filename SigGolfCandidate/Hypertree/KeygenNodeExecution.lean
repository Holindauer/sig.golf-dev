import SigGolfCandidate.Hypertree.KeygenNodePrefix
import SigGolfCandidate.Hypertree.KeygenNodeSuffix

namespace SigGolfCandidate.Hypertree.KeygenNode
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 OracleComp Keygen
set_option maxRecDepth 4096

/-- Complete node computation, ending just before the common return epilogue. -/
def BodyCode (image : Image) (p : Word) : Prop :=
  PrefixCode image p ∧ instructionAt image (p + 176) = some (.base .ECALL) ∧
    SuffixCode image (p + 180)

instance (image : Image) (p : Word) : Decidable (BodyCode image p) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- The actual node body computes the functional node in 80 instructions and 87 cycles. -/
theorem compute (image : Image) (hash : Hash) (p : Word) (code : BodyCode image p)
    (s : MachineState) (pc : s.pc = p) (level tree : Nat) (left right : Reference.Digest)
    (hlevel : s.getMem 0x80400 = BitVec.ofNat 64 level)
    (hindex : ∀ i : Fin 3, s.getMem (Signing.wordAddress 0x80408 i.val) =
      (BitVec.ofNat 192 tree).extractLsb' (64 * i.val) 64)
    (hchildren : ∀ i : Fin 4, s.getMem (Signing.wordAddress 0x80520 i.val) =
      if i.val < 2 then left.extractLsb' (64 * i.val) 64
      else right.extractLsb' (64 * (i.val - 2)) 64) :
    ∃ final, Trace hash image s 80 87 1 1 final ∧ final.pc = p + 224 ∧
      (∀ i : Fin 2, final.getMem (Signing.wordAddress 0x80500 i.val) =
        (Reference.node hash level tree left right).extractLsb' (64 * i.val) 64) ∧
      final.getReg .x1 = s.getReg .x1 ∧ final.getReg .x2 = s.getReg .x2 ∧
      (∀ a, (∀ i : Fin 8, a ≠ Signing.wordAddress 0x80000 i.val) →
        (∀ i : Fin 4, a ≠ Signing.wordAddress 0x80300 i.val) →
        (∀ i : Fin 2, a ≠ Signing.wordAddress 0x80500 i.val) →
        final.getMem a = s.getMem a) := by
  obtain ⟨prepared,pre,hpc,service,source,bits,destination,words,pra,psp,pframe⟩ :=
    prepare image p code.1 s pc level tree left right hlevel hindex hchildren
  let hashed := writeHash prepared (hash (hashInput prepared))
  have hashTrace : Trace hash image prepared 1 8 1 1 hashed := by
    have valid := hash_arguments prepared 512 source bits destination (by decide)
    have len : (hashInput prepared).1 = 512 := by simp [hashInput,bits]
    have hf : fetch image prepared = some (.base .ECALL) := by
      simpa only [fetch_at,hpc] using code.2.1
    simpa [len,compressions] using
      Trace.hash prepared hashed 0 0 0 0 hf service valid (Trace.refl _)
  have hashedPC : hashed.pc = p + 180 := by
    simp only [hashed,hash_pc,hpc]
    simp [BitVec.add_assoc]
  obtain ⟨final,post,fpc,content,ra,sp,frame⟩ := copy_answer image (p+180) code.2.2 hashed hashedPC
  refine ⟨final,pre.trace.trans (hashTrace.trans post.trace),?_,?_,?_,?_,?_⟩
  · simpa [BitVec.add_assoc] using fpc
  · intro i
    rw [content i]
    exact node_answer hash prepared level tree left right source bits destination words i
  · exact ra.trans ((hash_registers _ _ _).trans pra)
  · exact sp.trans ((hash_registers _ _ _).trans psp)
  · intro a inputOutside answerOutside currentOutside
    rw [frame a currentOutside,Signing.hash_answer_frame prepared _ destination a answerOutside]
    exact pframe a inputOutside

theorem keygen_body_code : BodyCode keygen 0x10e0 := by decide

/-- The node body and actual protected return refine the functional node operation. -/
theorem compute_return (image : Image) (hash : Hash) (p : Word) (code : BodyCode image p)
    (returnCode : ReturnCode image (p + 224))
    (s : MachineState) (pc : s.pc = p) (level tree : Nat) (left right : Reference.Digest)
    (hlevel : s.getMem 0x80400 = BitVec.ofNat 64 level)
    (hindex : ∀ i : Fin 3, s.getMem (Signing.wordAddress 0x80408 i.val) =
      (BitVec.ofNat 192 tree).extractLsb' (64 * i.val) 64)
    (hchildren : ∀ i : Fin 4, s.getMem (Signing.wordAddress 0x80520 i.val) =
      if i.val < 2 then left.extractLsb' (64 * i.val) 64
      else right.extractLsb' (64 * (i.val - 2)) 64)
    (stack : accessValid (s.getReg .x2) 8 = true)
    (stackInput : ∀ i : Fin 8, s.getReg .x2 ≠ Signing.wordAddress 0x80000 i.val)
    (stackAnswer : ∀ i : Fin 4, s.getReg .x2 ≠ Signing.wordAddress 0x80300 i.val)
    (stackCurrent : ∀ i : Fin 2, s.getReg .x2 ≠ Signing.wordAddress 0x80500 i.val) :
    ∃ final, Trace hash image s 83 90 1 1 final ∧
      final.pc = s.getMem (s.getReg .x2) &&& ~~~1#64 ∧
      final.getReg .x2 = s.getReg .x2 + 16 ∧
      (∀ i : Fin 2, final.getMem (Signing.wordAddress 0x80500 i.val) =
        (Reference.node hash level tree left right).extractLsb' (64 * i.val) 64) ∧
      (∀ a, (∀ i : Fin 8, a ≠ Signing.wordAddress 0x80000 i.val) →
        (∀ i : Fin 4, a ≠ Signing.wordAddress 0x80300 i.val) →
        (∀ i : Fin 2, a ≠ Signing.wordAddress 0x80500 i.val) →
        final.getMem a = s.getMem a) := by
  obtain ⟨body,trace,bpc,content,ra,sp,frame⟩ :=
    compute image hash p code s pc level tree left right hlevel hindex hchildren
  have ret := return_block image (p+224) returnCode body bpc (by rw [sp]; exact stack)
  refine ⟨returnState body,trace.trans ret.trace,?_,?_,?_,?_⟩
  · rw [return_pc,sp,frame _ stackInput stackAnswer stackCurrent]
  · rw [return_sp,sp]
  · intro i
    rw [return_mem]
    exact content i
  · intro a hi ha hc
    rw [return_mem]
    exact frame a hi ha hc

/-- info: 'SigGolfCandidate.Hypertree.KeygenNode.compute_return' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms compute_return

end SigGolfCandidate.Hypertree.KeygenNode
