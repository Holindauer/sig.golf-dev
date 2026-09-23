import SigGolfCandidate.Hypertree.InplaceInitialData
namespace SigGolfCandidate.Hypertree.InplaceSteps
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 Keygen Signing Verifying InplaceData
set_option maxRecDepth 8192

def InitialCode (image : Image) (p : Word) : Prop :=
  InplaceInitialPrepare.Code image p ∧ InplaceCore.Code image (p+236)
def RecurrentCode (image : Image) (p : Word) : Prop :=
  InplacePrepare.Code image p ∧ InplaceCore.Code image (p+96)

theorem check_constant (s : MachineState) :
    (InplaceCheck.shortCheck s).getReg .x13 = s.getReg .x13 := by
  simp [InplaceCheck.shortCheck,execInstrBr,MachineState.getReg_setReg_ne]

theorem initial (image : Image) (hash : Hash)
    (checkCode : CheckReuse.Code image 0x14f4)
    (prepareCode : InplaceInitialPrepare.Code image 0x1500) (coreCode : InplaceCore.Code image 0x15ec)
    (s : MachineState) (level tree step : Nat) (side : Bool) (chain : Reference.Chain) (value : Reference.Digest)
    (pc : s.pc = 0x14f4) (base : s.getReg .x28 = 0x80438)
    (bound : step < 7) (data : ChainData s level tree side chain step value) :
    ∃ final, Trace hash image s 41 48 1 1 final ∧ final.pc = 0x1580 ∧
      Buffered final level tree side chain (step+1) (Reference.chainHash hash level tree side chain step value) ∧
      CachedPrepare.Ready final ∧ final.getReg .x28 = 0x80438 ∧ final.getReg .x13 = 4294967296 ∧
      final.getReg .x1 = s.getReg .x1 ∧ final.getReg .x2 = s.getReg .x2 ∧
      (∀ a, OutsideChainWork a → final.getMem a = s.getMem a) := by
  have ne : s.getMem 0x80438 ≠ 7 := by
    rw [data.stepEq]
    intro eq
    have h := congrArg BitVec.toNat eq
    change step % 2^64 = 7 at h
    omega
  have checkedPC : (CheckReuse.shortCheck s).pc = 0x1500 := by
    rw [CheckReuse.short_pc s base,pc,if_neg ne]; rfl
  obtain ⟨final,run,finalPC,finalData,finalReady,finalBase,finalConstant,ra,sp,frame⟩ :=
    InplaceInitialData.compute image hash 0x1500 prepareCode coreCode (CheckReuse.shortCheck s)
      level tree step side chain value checkedPC (by rw [CheckReuse.short_base]; exact base)
      data.shortCheck
  refine ⟨final,(CheckReuse.block image 0x14f4 checkCode s pc base).trace.trans run,finalPC,
    finalData,finalReady,finalBase,finalConstant,ra.trans (CheckReuse.short_stack s).1,
    sp.trans (CheckReuse.short_stack s).2,?_⟩
  intro a outside
  rw [frame a outside,CheckReuse.short_mem]

/-- info: 'SigGolfCandidate.Hypertree.InplaceSteps.initial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms initial
theorem recurrent (image : Image) (hash : Hash)
    (checkCode : InplaceCheck.Code image 0x1580)
    (prepareCode : InplacePrepare.Code image 0x158c) (coreCode : InplaceCore.Code image 0x15ec)
    (s : MachineState) (level tree step : Nat) (side : Bool) (chain : Reference.Chain) (value : Reference.Digest)
    (pc : s.pc = 0x1580) (base : s.getReg .x28 = 0x80438)
    (constant : s.getReg .x13 = 4294967296) (ready : CachedPrepare.Ready s)
    (bound : step < 7) (data : Buffered s level tree side chain step value) :
    ∃ final, Trace hash image s 18 25 1 1 final ∧ final.pc = 0x1580 ∧
      Buffered final level tree side chain (step+1) (Reference.chainHash hash level tree side chain step value) ∧
      CachedPrepare.Ready final ∧ final.getReg .x28 = 0x80438 ∧ final.getReg .x13 = 4294967296 ∧
      final.getReg .x1 = s.getReg .x1 ∧ final.getReg .x2 = s.getReg .x2 ∧
      (∀ a, OutsideChainWork a → final.getMem a = s.getMem a) := by
  have ne : s.getMem 0x80438 ≠ 7 := by
    rw [data.stepEq]
    intro eq
    have h := congrArg BitVec.toNat eq
    change step % 2^64 = 7 at h
    omega
  have checkedPC : (InplaceCheck.shortCheck s).pc = 0x158c := by
    rw [InplaceCheck.short_pc s base,pc,if_neg ne]; rfl
  obtain ⟨final,run,finalPC,finalData,finalReady,finalBase,finalConstant,ra,sp,frame⟩ :=
    InplaceData.recurrent image hash 0x158c prepareCode coreCode (InplaceCheck.shortCheck s)
      level tree step side chain value checkedPC (by rw [InplaceCheck.short_base]; exact base)
      ((check_constant s).trans constant) (InplaceInvariant.check_ready s ready)
      data.check
  refine ⟨final,(InplaceCheck.block image 0x1580 checkCode s pc base).trace.trans run,finalPC,
    finalData,finalReady,finalBase,finalConstant,ra.trans (InplaceCheck.short_stack s).1,
    sp.trans (InplaceCheck.short_stack s).2,?_⟩
  intro a outside
  rw [frame a outside,InplaceCheck.short_mem]

/-- info: 'SigGolfCandidate.Hypertree.InplaceSteps.recurrent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms recurrent
end SigGolfCandidate.Hypertree.InplaceSteps
