import SigGolfCandidate.Hypertree.InplaceData
import SigGolfCandidate.Hypertree.CounterCore
import SigGolfCandidate.Hypertree.CounterArgs
namespace SigGolfCandidate.Hypertree.CounterData
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 Keygen Signing Verifying InplaceData
set_option maxRecDepth 8192
set_option maxHeartbeats 800000
theorem recurrent (image : Image) (hash : Hash) (p : Word)
    (prepareCode : CounterArgs.Code image p) (coreCode : CounterCore.Code image (p+100))
    (s : MachineState) (level tree step : Nat) (side : Bool) (chain : Reference.Chain) (value : Reference.Digest)
    (pc : s.pc = p) (base : s.getReg .x28 = 0x80438) (constant : s.getReg .x13 = 4294967296)
    (ready : CachedPrepare.Ready s)
    (args : s.getReg .x11 = 384 ∧ s.getReg .x12 = 0x80020 ∧ s.getReg .x5 = 1) (counter : s.getReg .x6 = s.getMem 0x80438) (data : Buffered s level tree side chain step value) :
    ∃ final, Trace hash image s 11 18 1 1 final ∧ final.pc = p-8 ∧
      Buffered final level tree side chain (step+1) (Reference.chainHash hash level tree side chain step value) ∧
      CachedPrepare.Ready final ∧ final.getReg .x28 = 0x80438 ∧ final.getReg .x13 = 4294967296 ∧
      (final.getReg .x11 = 384 ∧ final.getReg .x12 = 0x80020 ∧ final.getReg .x5 = 1) ∧
      final.getReg .x6 = final.getMem 0x80438 ∧
      final.getReg .x1 = s.getReg .x1 ∧ final.getReg .x2 = s.getReg .x2 ∧
      (∀ a, OutsideChainWork a → final.getMem a = s.getMem a) := by
  let prepared := (InplacePrepare.state s).setPC (s.pc+100)
  have prepPC : prepared.pc = p+100 := by simp only [prepared,MachineState.setPC,pc]
  obtain ⟨prepBase,source,bits,destination,service⟩ := InplacePrepare.regs s base
  have prepConstant : prepared.getReg .x13 = 4294967296 := by
    simpa only [prepared, MachineState.getReg_setPC] using (InplacePrepare.preserved s).2.2.trans constant
  have current : InplaceInvariant.Current prepared := by
    simpa only [InplaceInvariant.Current, prepared, MachineState.getMem_setPC] using InplaceInvariant.prepare_current s base constant ready
  have oldwords := KeygenChainHeader.words s level tree (Reference.sideNumber side) chain.val step value
    data.levelEq data.leafEq data.chainEq data.stepEq data.indexEq data.valueEq
  have words (i : Fin 6) : prepared.getMem (wordAddress 0x80000 i.val) =
      KeygenDomain.inputWord (KeygenDomain.header 2 level (Reference.sideNumber side) chain.val step) tree value i := by
    simpa only [prepared,MachineState.getMem_setPC] using (InplacePrepare.header_memory_equiv s base constant ready _).trans (oldwords i)
  have prepCounter : prepared.getReg .x6 = prepared.getMem 0x80438 := by
    simpa only [prepared, MachineState.getReg_setPC, MachineState.getMem_setPC] using RegisterCounter.prepare_counter s base counter
  obtain ⟨final,core,finalPC,valueEq,finalReady,finalBase,finalConstant,finalArgs,stepEq,finalCounter,ra,sp,frame⟩ :=
    CounterCore.compute image hash (p+100) coreCode prepared prepPC
      (by simpa only [prepared,MachineState.getReg_setPC] using prepBase) prepConstant current
      (by simpa only [prepared,MachineState.getReg_setPC] using service)
      (by simpa only [prepared,MachineState.getReg_setPC] using source)
      (by simpa only [prepared,MachineState.getReg_setPC] using bits)
      (by simpa only [prepared,MachineState.getReg_setPC] using destination)
      prepCounter level tree step side chain value words
  simp only [prepared,MachineState.getReg_setPC,MachineState.getMem_setPC] at frame ra sp stepEq
  have keep (a : Word) (outside : ∀ i : Fin 4, a ≠ wordAddress 0x80020 i.val)
      (notStep : a ≠ 0x80438) (notHeader : a ≠ 0x80000) : final.getMem a = s.getMem a := by
    rw [frame a outside notStep, InplacePrepare.mem s base,if_neg notHeader]
  have prepTrace := CounterArgs.block image p prepareCode s pc base
  rw [CounterArgs.equiv s base args.1 args.2.1 args.2.2] at prepTrace
  refine ⟨final,prepTrace.trace.trans core,?_,?_,finalReady,
    finalBase,finalConstant,finalArgs,finalCounter,ra.trans (InplacePrepare.preserved s).1,sp.trans (InplacePrepare.preserved s).2.1,?_⟩
  · simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using finalPC
  · constructor
    · rw [keep _ (by intro i; fin_cases i <;> decide) (by decide) (by decide)]; exact data.levelEq
    · rw [keep _ (by intro i; fin_cases i <;> decide) (by decide) (by decide)]; exact data.leafEq
    · rw [keep _ (by intro i; fin_cases i <;> decide) (by decide) (by decide)]; exact data.chainEq
    · rw [stepEq,InplacePrepare.mem s base,if_neg (by decide),data.stepEq,BitVec.ofNat_add]; rfl
    · intro i
      rw [keep _ (by intro j; fin_cases i <;> fin_cases j <;> decide)
        (by fin_cases i <;> decide) (by fin_cases i <;> decide)]
      exact data.indexEq i
    · exact valueEq
  · intro a outside
    apply keep a _ outside.2.2.2 (outside.1 0)
    intro i
    have h := outside.1 ⟨i.val+4,by have := i.isLt; omega⟩
    simpa [wordAddress,Nat.mul_add,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h

/-- info: 'SigGolfCandidate.Hypertree.CounterData.recurrent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms recurrent
end SigGolfCandidate.Hypertree.CounterData
