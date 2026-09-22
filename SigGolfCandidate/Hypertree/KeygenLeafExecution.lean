import SigGolfCandidate.Hypertree.KeygenLeafHeader
import SigGolfCandidate.Hypertree.KeygenEndpointCopy
import SigGolfCandidate.Hypertree.KeygenSavePublic
import SigGolfCandidate.Hypertree.KeygenControl

namespace SigGolfCandidate.Hypertree.KeygenLeaf
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 OracleComp Keygen
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

def Code (image : Image) (p : Word) : Prop :=
  KeygenEndpointCopy.CopySetupCode image p 2048 32 92 ∧ CopyCode image (p+20) ∧
  KeygenLeafHeader.Code image (p+44) ∧ instructionAt image (p+200) = some (.base .ECALL) ∧
  KeygenSavePublic.Code image (p+204)

instance (image : Image) (p : Word) : Decidable (Code image p) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _))

/-- The full leaf-compression suffix writes the reference root into its selected public slot. -/
theorem compute (image : Image) (hash : Hash) (p : Word) (code : Code image p)
    (s : MachineState) (pc : s.pc = p) (level tree : Nat) (side : Bool)
    (values : Reference.Chain → Reference.Digest)
    (hlevel : s.getMem 0x80400 = BitVec.ofNat 64 level)
    (hleaf : s.getMem 0x80428 = BitVec.ofNat 64 (Reference.sideNumber side))
    (hindex : ∀ i : Fin 3, s.getMem (Signing.wordAddress 0x80408 i.val) =
      (BitVec.ofNat 192 tree).extractLsb' (64*i.val) 64)
    (hvalues : ∀ i : Fin 92, s.getMem (Signing.wordAddress 0x80800 i.val) =
      KeygenLeafHeader.endpointWord values i) :
    ∃ final, Trace hash image s 612 707 1 12 final ∧ final.pc = p+264 ∧
      (∀ i : Fin 2, final.getMem (KeygenSavePublic.wordAddress side i.val) =
        (Reference.compressLeaf hash level tree side values).extractLsb' (64*i.val) 64) ∧
      final.getReg .x1 = s.getReg .x1 ∧ final.getReg .x2 = s.getReg .x2 ∧
      (∀ a, (∀ i : Fin 96, a ≠ Signing.wordAddress 0x80000 i.val) →
        (∀ i : Fin 4, a ≠ Signing.wordAddress 0x80300 i.val) →
        (∀ i : Fin 2, a ≠ KeygenSavePublic.wordAddress side i.val) →
        final.getMem a = s.getMem a) := by
  obtain ⟨copied,pre,cpc,content,cra,csp,cframe⟩ :=
    KeygenEndpointCopy.copy image p code.1 code.2.1 s pc
  have levelEq : copied.getMem 0x80400 = BitVec.ofNat 64 level := by
    rw [cframe _ (by intro i; fin_cases i <;> decide)]; exact hlevel
  have leafEq : copied.getMem 0x80428 = BitVec.ofNat 64 (Reference.sideNumber side) := by
    rw [cframe _ (by intro i; fin_cases i <;> decide)]; exact hleaf
  have indexEq : ∀ i : Fin 3, copied.getMem (Signing.wordAddress 0x80408 i.val) =
      (BitVec.ofNat 192 tree).extractLsb' (64*i.val) 64 := by
    intro i
    rw [cframe _ (by intro j; fin_cases i <;> fin_cases j <;> decide)]
    exact hindex i
  have valuesEq : ∀ i : Fin 92, copied.getMem (Signing.wordAddress 0x80020 i.val) =
      KeygenLeafHeader.endpointWord values i := by intro i; rw [content i]; exact hvalues i
  let ready := KeygenLeafHeader.state copied
  have headTrace := KeygenLeafHeader.block image (p+44) code.2.2.1 copied cpc
  have hpc : ready.pc = p+200 := by
    simp only [ready,KeygenLeafHeader.pc,cpc]; simp [BitVec.add_assoc]
  obtain ⟨service,source,bits,destination⟩ := KeygenLeafHeader.regs copied
  have words := KeygenLeafHeader.words copied level tree (Reference.sideNumber side) values levelEq leafEq indexEq valuesEq
  have hf : fetch image ready = some (.base .ECALL) := by simpa only [fetch_at,hpc] using code.2.2.2.1
  let hashed := writeHash ready (hash (hashInput ready))
  have hashTrace := hash_trace image hash ready hf service source bits destination
  have hashPC : hashed.pc = p+204 := by simp only [hashed,hash_pc,hpc]; simp [BitVec.add_assoc]
  have hashLeaf : hashed.getMem 0x80428 = BitVec.ofNat 64 (Reference.sideNumber side) := by
    rw [Signing.hash_answer_frame ready _ destination _ (by intro i; fin_cases i <;> decide),
      KeygenLeafHeader.frame copied _ (by intro i; fin_cases i <;> decide)]
    exact leafEq
  have safe := KeygenSavePublic.safe hashed side hashLeaf
  have post := KeygenSavePublic.block image (p+204) code.2.2.2.2 hashed hashPC safe.1 safe.2
  refine ⟨KeygenSavePublic.state hashed,pre.trace.trans (headTrace.trace.trans (hashTrace.trans post.trace)),?_,?_,?_,?_,?_⟩
  · rw [KeygenSavePublic.pc,hashPC]; simp [BitVec.add_assoc]
  · intro i
    rw [KeygenSavePublic.content hashed side hashLeaf i]
    exact answer_words hash ready level tree side values source bits destination words i
  · exact (KeygenSavePublic.stack hashed).1.trans ((hash_registers _ _ _).trans ((KeygenLeafHeader.stack copied).1.trans cra))
  · exact (KeygenSavePublic.stack hashed).2.trans ((hash_registers _ _ _).trans ((KeygenLeafHeader.stack copied).2.trans csp))
  · intro a inputOutside answerOutside publicOutside
    rw [KeygenSavePublic.frame hashed side hashLeaf a publicOutside,
      Signing.hash_answer_frame ready _ destination a answerOutside,
      KeygenLeafHeader.frame copied a (fun i => inputOutside ⟨i.val,by have := i.isLt; omega⟩)]
    apply cframe
    intro i
    have outside := inputOutside ⟨i.val+4,by have := i.isLt; omega⟩
    simpa [Signing.wordAddress,Nat.mul_add,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using outside

theorem keygen_code : Code keygen 0x1548 := by decide

/-- The leaf-compression suffix including the protected return through the saved stack word. -/
theorem compute_return (image : Image) (hash : Hash) (p : Word) (code : Code image p)
    (returnCode : ReturnCode image (p+264))
    (s : MachineState) (pc : s.pc=p) (level tree : Nat) (side : Bool)
    (values : Reference.Chain → Reference.Digest)
    (hlevel : s.getMem 0x80400 = BitVec.ofNat 64 level)
    (hleaf : s.getMem 0x80428 = BitVec.ofNat 64 (Reference.sideNumber side))
    (hindex : ∀ i : Fin 3, s.getMem (Signing.wordAddress 0x80408 i.val) =
      (BitVec.ofNat 192 tree).extractLsb' (64*i.val) 64)
    (hvalues : ∀ i : Fin 92, s.getMem (Signing.wordAddress 0x80800 i.val) =
      KeygenLeafHeader.endpointWord values i)
    (stack : accessValid (s.getReg .x2) 8 = true)
    (stackInput : ∀ i : Fin 96, s.getReg .x2 ≠ Signing.wordAddress 0x80000 i.val)
    (stackAnswer : ∀ i : Fin 4, s.getReg .x2 ≠ Signing.wordAddress 0x80300 i.val)
    (stackPublic : ∀ i : Fin 2, s.getReg .x2 ≠ KeygenSavePublic.wordAddress side i.val) :
    ∃ final, Trace hash image s 615 710 1 12 final ∧
      final.pc = s.getMem (s.getReg .x2) &&& ~~~1#64 ∧ final.getReg .x2=s.getReg .x2+16 ∧
      (∀ i : Fin 2, final.getMem (KeygenSavePublic.wordAddress side i.val) =
        (Reference.compressLeaf hash level tree side values).extractLsb' (64*i.val) 64) ∧
      (∀ a, (∀ i : Fin 96, a ≠ Signing.wordAddress 0x80000 i.val) →
        (∀ i : Fin 4, a ≠ Signing.wordAddress 0x80300 i.val) →
        (∀ i : Fin 2, a ≠ KeygenSavePublic.wordAddress side i.val) → final.getMem a=s.getMem a) := by
  obtain ⟨body,trace,bpc,content,ra,sp,frame⟩ := compute image hash p code s pc level tree side values hlevel hleaf hindex hvalues
  have ret := return_block image (p+264) returnCode body bpc (by rw [sp]; exact stack)
  refine ⟨returnState body,trace.trans ret.trace,?_,?_,?_,?_⟩
  · rw [return_pc,sp,frame _ stackInput stackAnswer stackPublic]
  · rw [return_sp,sp]
  · intro i; rw [return_mem]; exact content i
  · intro a hi ha hp; rw [return_mem]; exact frame a hi ha hp

/-- info: 'SigGolfCandidate.Hypertree.KeygenLeaf.compute_return' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms compute_return

end SigGolfCandidate.Hypertree.KeygenLeaf
