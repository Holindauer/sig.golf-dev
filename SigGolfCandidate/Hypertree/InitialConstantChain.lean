import SigGolfCandidate.Hypertree.ConstantRegister
import SigGolfCandidate.Hypertree.ConstantInitialPrepare
import SigGolfCandidate.Hypertree.ConstantInvariant
import SigGolfCandidate.Hypertree.Copy6
import SigGolfCandidate.Hypertree.FusedPrepare
import SigGolfCandidate.Hypertree.FusedFinish
import SigGolfCandidate.Hypertree.ReusePrepare
import SigGolfCandidate.Hypertree.ReuseFinish

namespace SigGolfCandidate.Hypertree.InitialConstantChain
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 Keygen
set_option maxRecDepth 50000

def ChainCode (image : Image) (p : Word) : Prop :=
  ConstantInitialPrepare.Code image p ∧
  instructionAt image (p+236) = some (.base .ECALL) ∧ ConstantFinish.Code image (p+240)

theorem chain_compute (image : Image) (hash : Hash) (p : Word) (code : ChainCode image p)
    (s : MachineState) (pc : s.pc = p) (base : s.getReg .x28 = 0x80438) (level tree step : Nat)
    (side : Bool) (chain : Reference.Chain) (value : Reference.Digest)
    (hlevel : s.getMem 0x80400 = BitVec.ofNat 64 level)
    (hleaf : s.getMem 0x80428 = BitVec.ofNat 64 (Reference.sideNumber side))
    (hchain : s.getMem 0x80430 = BitVec.ofNat 64 chain.val)
    (hstep : s.getMem 0x80438 = BitVec.ofNat 64 step)
    (hindex : ∀ i : Fin 3, s.getMem (Signing.wordAddress 0x80408 i.val) =
      (BitVec.ofNat 192 tree).extractLsb' (64*i.val) 64)
    (hvalue : ∀ i : Fin 2, s.getMem (Signing.wordAddress 0x80510 i.val) =
      value.extractLsb' (64*i.val) 64) :
    ∃ final, Trace hash image s 42 49 1 1 (ChainLoopControl.increment final (-184)) ∧ final.pc = p+284 ∧
      (∀ i : Fin 2, final.getMem (Signing.wordAddress 0x80510 i.val) =
        (Reference.chainHash hash level tree side chain step value).extractLsb' (64*i.val) 64) ∧
      final.getReg .x1 = s.getReg .x1 ∧ final.getReg .x2 = s.getReg .x2 ∧
      (∀ a, (∀ i : Fin 6, a ≠ Signing.wordAddress 0x80000 i.val) →
        (∀ i : Fin 4, a ≠ Signing.wordAddress 0x80300 i.val) →
        (∀ i : Fin 2, a ≠ Signing.wordAddress 0x80510 i.val) →
        final.getMem a = s.getMem a) ∧
      CachedPrepare.Ready (ChainLoopControl.increment final (-184)) ∧
      (ChainLoopControl.increment final (-184)).getReg .x13 = 4294967296 := by
  let copied := Copy6.optimized s 0x510 0x20
  obtain ⟨hp,cra,csp,content,frame⟩ := Copy6.input_spec s
  have cpc : copied.pc = p+44 := by simpa only [copied, pc] using hp
  have cframe (a : Word) (outside : ∀ i : Fin 2, a ≠ Signing.wordAddress 0x80020 i.val) :
      copied.getMem a = s.getMem a := by
    exact frame a (by simpa [Signing.wordAddress] using outside 0)
      (by simpa [Signing.wordAddress] using outside 1)
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
  let prepared := (KeygenChainHeader.state copied).setReg .x13 4294967296
  have headTrace : OrdinarySteps image s 32 prepared := by
    have h := ConstantInitialPrepare.block image p code.1 s pc base
    rw [ConstantInitialPrepare.state_equiv s base] at h
    exact h
  have hpc : prepared.pc = p+236 := by
    simp only [prepared,MachineState.setReg,KeygenChainHeader.pc,cpc]; simp [BitVec.add_assoc]
  have pr : prepared.getReg .x5 = 1 ∧ prepared.getReg .x10 = 0x80000 ∧
      prepared.getReg .x11 = 48 ∧ prepared.getReg .x12 = 0x80300 := by
    simpa [prepared, MachineState.getReg_setReg_ne] using KeygenChainHeader.regs copied
  obtain ⟨service,source,bits,destination⟩ := pr
  have oldwords := KeygenChainHeader.words copied level tree (Reference.sideNumber side) chain.val step value
    levelEq leafEq chainEq stepEq indexEq valueEq
  have words (i : Fin 6) : prepared.getMem (Signing.wordAddress 0x80000 i.val) =
      KeygenDomain.inputWord (KeygenDomain.header 2 level (Reference.sideNumber side) chain.val step) tree value i := by
    simpa only [prepared, MachineState.getMem_setReg] using oldwords i
  have hf : fetch image prepared = some (.base .ECALL) := by
    simpa only [fetch_at,hpc] using code.2.1
  let hashed := writeHash prepared (hash (hashInput prepared))
  have hashTrace := KeygenDomain.hash_trace image hash prepared hf service source bits destination
  have hashPC : hashed.pc = p+240 := by simp only [hashed,hash_pc,hpc]; simp [BitVec.add_assoc]
  -- `final` is the semantic copy result; the actual trace also performs its increment.
  let final := Copy6.optimized hashed 0x300 0x510
  obtain ⟨outpc,fra,fsp,result,outframe⟩ := Copy6.output_spec hashed
  have fpc : final.pc = p+240+44 := by simpa only [final,hashPC] using outpc
  have fframe (a : Word) (outside : ∀ i : Fin 2, a ≠ Signing.wordAddress 0x80510 i.val) :
      final.getMem a = hashed.getMem a := by
    exact outframe a (by simpa [Signing.wordAddress] using outside 0)
      (by simpa [Signing.wordAddress] using outside 1)
  have hashBase : hashed.getReg .x28 = 0x80018 := by
    rw [show hashed.getReg .x28 = prepared.getReg .x28 from hash_registers _ _ _]
    simpa [prepared, MachineState.getReg_setReg_ne] using ReusePrepare.header_base copied
  have preparedRA : prepared.getReg .x1 = copied.getReg .x1 := by
    simpa [prepared, MachineState.getReg_setReg_ne] using (KeygenChainHeader.stack copied).1
  have preparedSP : prepared.getReg .x2 = copied.getReg .x2 := by
    simpa [prepared, MachineState.getReg_setReg_ne] using (KeygenChainHeader.stack copied).2
  have post := ConstantFinish.block image (p+240) code.2.2 hashed hashPC hashBase
  refine ⟨final,headTrace.trace.trans (hashTrace.trans post.trace),?_,?_,?_,?_,?_,?_,?_⟩
  · simpa [BitVec.add_assoc] using fpc
  · intro i
    rw [result i]
    exact KeygenDomain.answer_words hash prepared 2 level tree (Reference.sideNumber side) chain.val step value
      source bits destination words i
  · exact fra.trans ((hash_registers _ _ _).trans (preparedRA.trans cra))
  · exact fsp.trans ((hash_registers _ _ _).trans (preparedSP.trans csp))
  · intro a inputOutside answerOutside valueOutside
    rw [fframe a valueOutside,Signing.hash_answer_frame prepared _ destination a answerOutside]
    rw [show prepared.getMem a = (KeygenChainHeader.state copied).getMem a from MachineState.getMem_setReg, KeygenChainHeader.frame copied a (fun i => inputOutside ⟨i.val,by have := i.isLt; omega⟩)]
    apply cframe
    intro i
    have h := inputOutside ⟨i.val+4,by have := i.isLt; omega⟩
    simpa [Signing.wordAddress,Nat.mul_add,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h




  · change CachedPrepare.Ready (ChainLoopControl.increment (Copy6.optimized hashed 0x300 0x510) (-184))
    rw [← ConstantFusedFinish.state_equiv, ← ConstantFinish.finish_equiv hashed hashBase]
    apply ConstantInvariant.finish_ready hashed hashBase
    apply ConstantInvariant.hash_current prepared _ destination
    simpa only [ConstantInvariant.Current, prepared, MachineState.getMem_setReg] using ConstantInvariant.full_prepare_current copied

  · change (ChainLoopControl.increment (Copy6.optimized hashed 0x300 0x510) (-184)).getReg .x13 = _
    rw [← ConstantFusedFinish.state_equiv, ← ConstantFinish.finish_equiv hashed hashBase]
    rw [ConstantRegister.ConstantFinish_preserves, hash_registers]
    simp [prepared, MachineState.getReg_setReg_eq]

/-- info: 'SigGolfCandidate.Hypertree.InitialConstantChain.chain_compute' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms chain_compute
end SigGolfCandidate.Hypertree.InitialConstantChain
