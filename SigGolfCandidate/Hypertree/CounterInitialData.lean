import SigGolfCandidate.Hypertree.CounterData
import SigGolfCandidate.Hypertree.InplaceInitialPrepare
namespace SigGolfCandidate.Hypertree.CounterInitialData
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 Keygen Signing Verifying InplaceData
set_option maxRecDepth 8192

theorem compute (image : Image) (hash : Hash) (p : Word)
    (prepareCode : InplaceInitialPrepare.Code image p) (coreCode : CounterCore.Code image (p+236))
    (s : MachineState) (level tree step : Nat) (side : Bool) (chain : Reference.Chain) (value : Reference.Digest)
    (pc : s.pc = p) (base : s.getReg .x28 = 0x80438)
    (counter : s.getReg .x6 = s.getMem 0x80438) (data : ChainData s level tree side chain step value) :
    ∃ final, Trace hash image s 37 44 1 1 final ∧ final.pc = p+128 ∧
      Buffered final level tree side chain (step+1) (Reference.chainHash hash level tree side chain step value) ∧
      CachedPrepare.Ready final ∧ final.getReg .x28 = 0x80438 ∧ final.getReg .x13 = 4294967296 ∧
      (final.getReg .x11 = 384 ∧ final.getReg .x12 = 0x80020 ∧ final.getReg .x5 = 1) ∧
      final.getReg .x6 = final.getMem 0x80438 ∧
      final.getReg .x1 = s.getReg .x1 ∧ final.getReg .x2 = s.getReg .x2 ∧
      (∀ a, OutsideChainWork a → final.getMem a = s.getMem a) := by
  let copied := Copy6.optimized s 0x510 0x20
  obtain ⟨hp,cra,csp,content,frame⟩ := Copy6.input_spec s
  have cpc : copied.pc = p+44 := by simpa only [copied, pc] using hp
  have cframe (a : Word) (outside : ∀ i : Fin 2, a ≠ Signing.wordAddress 0x80020 i.val) :
      copied.getMem a = s.getMem a := by
    exact frame a (by simpa [Signing.wordAddress] using outside 0)
      (by simpa [Signing.wordAddress] using outside 1)
  have levelEq : copied.getMem 0x80400 = BitVec.ofNat 64 level := by
    rw [cframe _ (by intro i; fin_cases i <;> decide)]; exact data.levelEq
  have leafEq : copied.getMem 0x80428 = BitVec.ofNat 64 (Reference.sideNumber side) := by
    rw [cframe _ (by intro i; fin_cases i <;> decide)]; exact data.leafEq
  have chainEq : copied.getMem 0x80430 = BitVec.ofNat 64 chain.val := by
    rw [cframe _ (by intro i; fin_cases i <;> decide)]; exact data.chainEq
  have stepEq : copied.getMem 0x80438 = BitVec.ofNat 64 step := by
    rw [cframe _ (by intro i; fin_cases i <;> decide)]; exact data.stepEq
  have indexEq : ∀ i : Fin 3, copied.getMem (Signing.wordAddress 0x80408 i.val) =
      (BitVec.ofNat 192 tree).extractLsb' (64*i.val) 64 := by
    intro i
    rw [cframe _ (by intro j; fin_cases i <;> fin_cases j <;> decide)]
    exact data.indexEq i
  have valueEq : ∀ i : Fin 2, copied.getMem (Signing.wordAddress 0x80020 i.val) =
      value.extractLsb' (64*i.val) 64 := by intro i; rw [content i]; exact data.valueEq i

  let prepared := ((KeygenChainHeader.state copied).setReg .x13 4294967296).setReg .x12 0x80020
  have prepTrace : OrdinarySteps image s 32 prepared := by
    have h := InplaceInitialPrepare.block image p prepareCode s pc base
    rw [InplaceInitialPrepare.state_equiv s base] at h
    exact h
  have prepPC : prepared.pc = p+236 := by
    simp only [prepared,MachineState.setReg,KeygenChainHeader.pc,cpc]
    simp [BitVec.add_assoc]
  have prepBase : prepared.getReg .x28 = 0x80018 := by
    simpa [prepared,MachineState.getReg_setReg_ne] using ReusePrepare.header_base copied
  have prepConstant : prepared.getReg .x13 = 4294967296 := by
    simp [prepared,MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  have source : prepared.getReg .x10 = 0x80000 := by
    simpa [prepared,MachineState.getReg_setReg_ne] using (KeygenChainHeader.regs copied).2.1
  have bits : prepared.getReg .x11 = 384 := by
    simpa [prepared,MachineState.getReg_setReg_ne] using (KeygenChainHeader.regs copied).2.2.1
  have service : prepared.getReg .x5 = 1 := by
    simpa [prepared,MachineState.getReg_setReg_ne] using (KeygenChainHeader.regs copied).1
  have destination : prepared.getReg .x12 = 0x80020 := by
    simp [prepared,MachineState.getReg_setReg_eq]
  have current : InplaceInvariant.Current prepared := by
    simpa only [InplaceInvariant.Current,prepared,MachineState.getMem_setReg] using InplaceInvariant.full_prepare_current copied
  have oldwords := KeygenChainHeader.words copied level tree (Reference.sideNumber side) chain.val step value
    levelEq leafEq chainEq stepEq indexEq valueEq
  have words (i : Fin 6) : prepared.getMem (wordAddress 0x80000 i.val) =
      KeygenDomain.inputWord (KeygenDomain.header 2 level (Reference.sideNumber side) chain.val step) tree value i := by
    simpa only [prepared,MachineState.getMem_setReg] using oldwords i
  have prepCounter : prepared.getReg .x6 = prepared.getMem 0x80438 := by
    have h := RegisterCounter.initial_counter s base counter
    rw [InplaceInitialPrepare.state_equiv s base] at h
    exact h
  obtain ⟨final,core,finalPC,valueOut,finalReady,finalBase,finalConstant,finalArgs,stepOut,finalCounter,ra,sp,frame⟩ :=
    CounterCore.compute image hash (p+236) coreCode prepared prepPC prepBase prepConstant current
      service source bits destination prepCounter level tree step side chain value words
  have prepFrame (a : Word) (outside : ∀ i : Fin 8, a ≠ wordAddress 0x80000 i.val) :
      prepared.getMem a = s.getMem a := by
    simp only [prepared,MachineState.getMem_setReg]
    rw [KeygenChainHeader.frame copied a (fun i => outside ⟨i.val,by omega⟩)]
    apply cframe
    intro i
    have h := outside ⟨i.val+4,by have := i.isLt; omega⟩
    simpa [wordAddress,Nat.mul_add,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h
  have keep (a : Word) (outside : OutsideChainWork a) : final.getMem a = s.getMem a := by
    rw [frame a _ outside.2.2.2,prepFrame a outside.1]
    intro i
    have h := outside.1 ⟨i.val+4,by have := i.isLt; omega⟩
    simpa [wordAddress,Nat.mul_add,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h
  have prepRA : prepared.getReg .x1 = s.getReg .x1 := by
    have h := (KeygenChainHeader.stack copied).1.trans cra
    simpa [prepared,MachineState.getReg_setReg_ne] using h
  have prepSP : prepared.getReg .x2 = s.getReg .x2 := by
    have h := (KeygenChainHeader.stack copied).2.trans csp
    simpa [prepared,MachineState.getReg_setReg_ne] using h
  refine ⟨final,prepTrace.trace.trans core,?_,?_,finalReady,finalBase,finalConstant,finalArgs,finalCounter,
    ra.trans prepRA,sp.trans prepSP,keep⟩
  · simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using finalPC
  · constructor
    · rw [keep _ (by unfold OutsideChainWork; decide)]; exact data.levelEq
    · rw [keep _ (by unfold OutsideChainWork; decide)]; exact data.leafEq
    · rw [keep _ (by unfold OutsideChainWork; decide)]; exact data.chainEq
    · rw [stepOut,prepFrame _ (by decide),data.stepEq,BitVec.ofNat_add]; rfl
    · intro i
      rw [keep _ (by unfold OutsideChainWork; fin_cases i <;> decide)]
      exact data.indexEq i
    · exact valueOut

/-- info: 'SigGolfCandidate.Hypertree.CounterInitialData.compute' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms compute
end SigGolfCandidate.Hypertree.CounterInitialData
