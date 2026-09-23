import SigGolfCandidate.Hypertree.PersistentHashArgs
import SigGolfCandidate.Hypertree.InplaceCore
import SigGolfCandidate.Hypertree.VerifyChainStep
namespace SigGolfCandidate.Hypertree.InplaceData
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 Keygen Signing Verifying
set_option maxRecDepth 8192

structure Buffered (s : MachineState) (level tree : Nat) (side : Bool) (chain : Reference.Chain)
    (step : Nat) (value : Reference.Digest) : Prop where
  levelEq : s.getMem 0x80400 = BitVec.ofNat 64 level
  leafEq : s.getMem 0x80428 = BitVec.ofNat 64 (Reference.sideNumber side)
  chainEq : s.getMem 0x80430 = BitVec.ofNat 64 chain.val
  stepEq : s.getMem 0x80438 = BitVec.ofNat 64 step
  indexEq : ∀ i : Fin 3, s.getMem (wordAddress 0x80408 i.val) = (BitVec.ofNat 192 tree).extractLsb' (64*i.val) 64
  valueEq : ∀ i : Fin 2, s.getMem (wordAddress 0x80020 i.val) = value.extractLsb' (64*i.val) 64

theorem Buffered.check (s : MachineState) (level tree : Nat) (side : Bool) (chain : Reference.Chain)
    (step : Nat) (value : Reference.Digest) (data : Buffered s level tree side chain step value) :
    Buffered (InplaceCheck.shortCheck s) level tree side chain step value := by
  constructor
  · simpa only [InplaceCheck.short_mem] using data.levelEq
  · simpa only [InplaceCheck.short_mem] using data.leafEq
  · simpa only [InplaceCheck.short_mem] using data.chainEq
  · simpa only [InplaceCheck.short_mem] using data.stepEq
  · simpa only [InplaceCheck.short_mem] using data.indexEq
  · simpa only [InplaceCheck.short_mem] using data.valueEq

theorem Buffered.prepare (s : MachineState) (level tree : Nat) (side : Bool) (chain : Reference.Chain)
    (step : Nat) (value : Reference.Digest) (base : s.getReg .x28 = 0x80438)
    (data : Buffered s level tree side chain step value) :
    Buffered (InplacePrepare.state s) level tree side chain step value := by
  constructor
  · rw [InplacePrepare.mem s base, if_neg (by decide)]; exact data.levelEq
  · rw [InplacePrepare.mem s base, if_neg (by decide)]; exact data.leafEq
  · rw [InplacePrepare.mem s base, if_neg (by decide)]; exact data.chainEq
  · rw [InplacePrepare.mem s base, if_neg (by decide)]; exact data.stepEq
  · intro i; rw [InplacePrepare.mem s base, if_neg (by fin_cases i <;> decide)]; exact data.indexEq i
  · intro i; rw [InplacePrepare.mem s base, if_neg (by fin_cases i <;> decide)]; exact data.valueEq i

theorem Buffered.restore (s : MachineState) (level tree : Nat) (side : Bool) (chain : Reference.Chain)
    (step : Nat) (value : Reference.Digest) (base : s.getReg .x28 = 0x80438)
    (data : Buffered s level tree side chain step value) :
    ChainData (InplaceRestore.state s) level tree side chain step value := by
  constructor
  · rw [InplaceRestore.mem s base,if_neg (by decide),if_neg (by decide)]; exact data.levelEq
  · rw [InplaceRestore.mem s base,if_neg (by decide),if_neg (by decide)]; exact data.leafEq
  · rw [InplaceRestore.mem s base,if_neg (by decide),if_neg (by decide)]; exact data.chainEq
  · rw [InplaceRestore.mem s base,if_neg (by decide),if_neg (by decide)]; exact data.stepEq
  · intro i
    rw [InplaceRestore.mem s base,if_neg (by fin_cases i <;> decide),if_neg (by fin_cases i <;> decide)]
    exact data.indexEq i
  · intro i; rw [InplaceInvariant.restore_words s base]; exact data.valueEq i

theorem recurrent (image : Image) (hash : Hash) (p : Word)
    (prepareCode : PersistentHashArgs.Code image p) (coreCode : InplaceCore.Code image (p+96))
    (s : MachineState) (level tree step : Nat) (side : Bool) (chain : Reference.Chain) (value : Reference.Digest)
    (pc : s.pc = p) (base : s.getReg .x28 = 0x80438) (constant : s.getReg .x13 = 4294967296)
    (ready : CachedPrepare.Ready s)
    (args : s.getReg .x11 = 384 ∧ s.getReg .x12 = 0x80020 ∧ s.getReg .x5 = 1) (data : Buffered s level tree side chain step value) :
    ∃ final, Trace hash image s 12 19 1 1 final ∧ final.pc = p-12 ∧
      Buffered final level tree side chain (step+1) (Reference.chainHash hash level tree side chain step value) ∧
      CachedPrepare.Ready final ∧ final.getReg .x28 = 0x80438 ∧ final.getReg .x13 = 4294967296 ∧
      (final.getReg .x11 = 384 ∧ final.getReg .x12 = 0x80020 ∧ final.getReg .x5 = 1) ∧
      final.getReg .x1 = s.getReg .x1 ∧ final.getReg .x2 = s.getReg .x2 ∧
      (∀ a, OutsideChainWork a → final.getMem a = s.getMem a) := by
  let prepared := InplacePrepare.state s
  have prepPC : prepared.pc = p+96 := by rw [InplacePrepare.pc, pc]
  obtain ⟨prepBase,source,bits,destination,service⟩ := InplacePrepare.regs s base
  have prepConstant : prepared.getReg .x13 = 4294967296 := (InplacePrepare.preserved s).2.2.trans constant
  have current := InplaceInvariant.prepare_current s base constant ready
  have oldwords := KeygenChainHeader.words s level tree (Reference.sideNumber side) chain.val step value
    data.levelEq data.leafEq data.chainEq data.stepEq data.indexEq data.valueEq
  have words (i : Fin 6) := (InplacePrepare.header_memory_equiv s base constant ready _).trans (oldwords i)
  obtain ⟨final,core,finalPC,valueEq,finalReady,finalBase,finalConstant,finalArgs,stepEq,ra,sp,frame⟩ :=
    InplaceCore.compute image hash (p+96) coreCode prepared prepPC prepBase prepConstant current
      service source bits destination level tree step side chain value words
  have keep (a : Word) (outside : ∀ i : Fin 4, a ≠ wordAddress 0x80020 i.val)
      (notStep : a ≠ 0x80438) (notHeader : a ≠ 0x80000) : final.getMem a = s.getMem a := by
    rw [frame a outside notStep, InplacePrepare.mem s base,if_neg notHeader]
  have prepTrace := PersistentHashArgs.block image p prepareCode s pc base
  rw [PersistentHashArgs.equiv s base args.1 args.2.1 args.2.2] at prepTrace
  refine ⟨final,prepTrace.trace.trans core,?_,?_,finalReady,
    finalBase,finalConstant,finalArgs,ra.trans (InplacePrepare.preserved s).1,sp.trans (InplacePrepare.preserved s).2.1,?_⟩
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

/-- info: 'SigGolfCandidate.Hypertree.InplaceData.recurrent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms recurrent
end SigGolfCandidate.Hypertree.InplaceData
