import SigGolfCandidate.Hypertree.SignLeafFinish

namespace SigGolfCandidate.Hypertree.SignBottomHash
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 OracleComp Keygen
set_option maxRecDepth 4096

def Code (image : Image) (p : Word) : Prop :=
  CopySetupCode image p 0x510 0x20 2 ∧ CopyCode image (p+20) ∧
  KeygenChainHeader.Code image (p+44) ∧
  instructionAt image (p+236) = some (.base .ECALL) ∧
  KeygenSavePublic.Code image (p+240)

instance (image : Image) (p : Word) : Decidable (Code image p) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _))

/-- One complete chain HASH core, shared by generation, signing, and verification. -/
theorem compute (image : Image) (hash : Hash) (p : Word) (code : Code image p)
    (s : MachineState) (pc : s.pc = p) (level tree step : Nat)
    (side : Bool) (chain : Reference.Chain) (value : Reference.Digest)
    (hlevel : s.getMem 0x80400 = BitVec.ofNat 64 level)
    (hleaf : s.getMem 0x80428 = BitVec.ofNat 64 (Reference.sideNumber side))
    (hchain : s.getMem 0x80430 = BitVec.ofNat 64 chain.val)
    (hstep : s.getMem 0x80438 = BitVec.ofNat 64 step)
    (hindex : ∀ i : Fin 3, s.getMem (Signing.wordAddress 0x80408 i.val) =
      (BitVec.ofNat 192 tree).extractLsb' (64*i.val) 64)
    (hvalue : ∀ i : Fin 2, s.getMem (Signing.wordAddress 0x80510 i.val) =
      value.extractLsb' (64*i.val) 64) :
    ∃ final, Trace hash image s 81 88 1 1 final ∧ final.pc = p+300 ∧
      (∀ i : Fin 2, final.getMem (KeygenSavePublic.wordAddress side i.val) =
        (Reference.chainHash hash level tree side chain step value).extractLsb' (64*i.val) 64) ∧
      final.getReg .x1 = s.getReg .x1 ∧ final.getReg .x2 = s.getReg .x2 ∧
      (∀ a, (∀ i : Fin 6, a ≠ Signing.wordAddress 0x80000 i.val) →
        (∀ i : Fin 4, a ≠ Signing.wordAddress 0x80300 i.val) →
        (∀ i : Fin 2, a ≠ KeygenSavePublic.wordAddress side i.val) →
        final.getMem a = s.getMem a) := by
  obtain ⟨copied,pre,cpc,content,cra,csp,cframe⟩ :=
    copy_two image p 0x510 0x20 0x80510 0x80020 code.1 code.2.1
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) s pc
  have levelEq : copied.getMem 0x80400 = BitVec.ofNat 64 level := by
    rw [cframe _ (by intro i; fin_cases i <;> decide)]; exact hlevel
  have leafEq : copied.getMem 0x80428 = BitVec.ofNat 64 (Reference.sideNumber side) := by
    rw [cframe _ (by intro i; fin_cases i <;> decide)]; exact hleaf
  have chainEq : copied.getMem 0x80430 = BitVec.ofNat 64 chain.val := by
    rw [cframe _ (by intro i; fin_cases i <;> decide)]; exact hchain
  have stepEq : copied.getMem 0x80438 = BitVec.ofNat 64 step := by
    rw [cframe _ (by intro i; fin_cases i <;> decide)]; exact hstep
  have indexEq : ∀ i : Fin 3, copied.getMem (Signing.wordAddress 0x80408 i.val) =
      (BitVec.ofNat 192 tree).extractLsb' (64*i.val) 64 := by
    intro i
    rw [cframe _ (by intro j; fin_cases i <;> fin_cases j <;> decide)]
    exact hindex i
  have valueEq : ∀ i : Fin 2, copied.getMem (Signing.wordAddress 0x80020 i.val) =
      value.extractLsb' (64*i.val) 64 := by intro i; rw [content i]; exact hvalue i
  let prepared := KeygenChainHeader.state copied
  have headTrace := KeygenChainHeader.block image (p+44) code.2.2.1 copied cpc
  have hpc : prepared.pc = p+236 := by
    simp only [prepared,KeygenChainHeader.pc,cpc]; simp [BitVec.add_assoc]
  obtain ⟨service,source,bits,destination⟩ := KeygenChainHeader.regs copied
  have words := KeygenChainHeader.words copied level tree (Reference.sideNumber side) chain.val step value
    levelEq leafEq chainEq stepEq indexEq valueEq
  have hf : fetch image prepared = some (.base .ECALL) := by
    simpa only [fetch_at,hpc] using code.2.2.2.1
  let hashed := writeHash prepared (hash (hashInput prepared))
  have hashTrace := KeygenDomain.hash_trace image hash prepared hf service source bits destination
  have hashPC : hashed.pc = p+240 := by simp only [hashed,hash_pc,hpc]; simp [BitVec.add_assoc]
  have hashLeaf : hashed.getMem 0x80428 = BitVec.ofNat 64 (Reference.sideNumber side) := by
    rw [Signing.hash_answer_frame prepared _ destination _ (by intro i; fin_cases i <;> decide),
      KeygenChainHeader.frame copied _ (by intro i; fin_cases i <;> decide)]
    exact leafEq
  have safe := KeygenSavePublic.safe hashed side hashLeaf
  have post := KeygenSavePublic.block image (p+240) code.2.2.2.2 hashed hashPC safe.1 safe.2
  refine ⟨KeygenSavePublic.state hashed,pre.trace.trans (headTrace.trace.trans (hashTrace.trans post.trace)),?_,?_,?_,?_,?_⟩
  · rw [KeygenSavePublic.pc, hashPC]; simp [BitVec.add_assoc]
  · intro i
    rw [KeygenSavePublic.content hashed side hashLeaf i]
    exact KeygenDomain.answer_words hash prepared 2 level tree (Reference.sideNumber side) chain.val step value
      source bits destination words i
  · exact (KeygenSavePublic.stack hashed).1.trans ((hash_registers _ _ _).trans ((KeygenChainHeader.stack copied).1.trans cra))
  · exact (KeygenSavePublic.stack hashed).2.trans ((hash_registers _ _ _).trans ((KeygenChainHeader.stack copied).2.trans csp))
  · intro a inputOutside answerOutside valueOutside
    rw [KeygenSavePublic.frame hashed side hashLeaf a valueOutside,Signing.hash_answer_frame prepared _ destination a answerOutside]
    rw [KeygenChainHeader.frame copied a (fun i => inputOutside ⟨i.val,by have := i.isLt; omega⟩)]
    apply cframe
    intro i
    have h := inputOutside ⟨i.val+4,by have := i.isLt; omega⟩
    simpa [Signing.wordAddress,Nat.mul_add,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h

theorem sign_code : Code sign 0x1b38 := by decide

end SigGolfCandidate.Hypertree.SignBottomHash
