import SigGolfCandidate.Hypertree.StepBaseInitialData
import SigGolfCandidate.Hypertree.CounterCheck
namespace SigGolfCandidate.Hypertree.StepBaseSteps
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 Keygen Signing Verifying InplaceData
set_option maxRecDepth 8192

def InitialCode (image : Image) (p : Word) : Prop :=
  StepBaseBlocks.InitialCode image p ∧ StepBaseCore.Code image (p+236)
def RecurrentCode (image : Image) (p : Word) : Prop :=
  StepBaseBlocks.PrepareCode image p ∧ StepBaseCore.Code image (p+104)

theorem check_constant (s : MachineState) :
    (CounterCheck.shortCheck s).getReg .x13 = s.getReg .x13 := by
  exact CounterCheck.reg s .x13 (by decide)

theorem initial (image : Image) (hash : Hash)
    (checkCode : CheckReuse.Code image 0x14f4)
    (prepareCode : StepBaseBlocks.InitialCode image 0x1500) (coreCode : StepBaseCore.Code image 0x15ec)
    (s : MachineState) (level tree step : Nat) (side : Bool) (chain : Reference.Chain) (value : Reference.Digest)
    (pc : s.pc = 0x14f4) (base : s.getReg .x28 = 0x80438)
    (bound : step < 7) (data : ChainData s level tree side chain step value) :
    ∃ final, Trace hash image s 38 45 1 1 final ∧ final.pc = 0x1580 ∧
      Buffered final level tree side chain (step+1) (Reference.chainHash hash level tree side chain step value) ∧
      CachedPrepare.Ready final ∧ final.getReg .x28 = 0x80438 ∧ final.getReg .x13 = 4294967296 ∧
      (final.getReg .x11 = 48 ∧ final.getReg .x12 = 0x80020 ∧ final.getReg .x5 = 1) ∧
      final.getReg .x6 = final.getMem 0x80438 ∧
      final.getReg .x7 = 7 ∧
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
  obtain ⟨final,run,finalPC,finalData,finalReady,finalBase,finalConstant,finalArgs,finalCounter,finalLimit,ra,sp,frame⟩ :=
    StepBaseInitialData.compute image hash 0x1500 prepareCode coreCode (CheckReuse.shortCheck s)
      level tree step side chain value checkedPC (by rw [CheckReuse.short_base]; exact base)
      (RegisterCounter.initial_check_counter s base) data.shortCheck
  refine ⟨final,(CheckReuse.block image 0x14f4 checkCode s pc base).trace.trans run,finalPC,
    finalData,finalReady,finalBase,finalConstant,finalArgs,finalCounter,finalLimit.trans (PersistentLimit.initial_installs s),ra.trans (CheckReuse.short_stack s).1,
    sp.trans (CheckReuse.short_stack s).2,?_⟩
  intro a outside
  rw [frame a outside,CheckReuse.short_mem]

/-- info: 'SigGolfCandidate.Hypertree.StepBaseSteps.initial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms initial
theorem recurrent (image : Image) (hash : Hash)
    (checkCode : CounterCheck.Code image 0x1580)
    (prepareCode : StepBaseBlocks.PrepareCode image 0x1584) (coreCode : StepBaseCore.Code image 0x15ec)
    (s : MachineState) (level tree step : Nat) (side : Bool) (chain : Reference.Chain) (value : Reference.Digest)
    (pc : s.pc = 0x1580) (base : s.getReg .x28 = 0x80438)
    (constant : s.getReg .x13 = 4294967296) (ready : CachedPrepare.Ready s)
    (args : s.getReg .x11 = 48 ∧ s.getReg .x12 = 0x80020 ∧ s.getReg .x5 = 1)
    (counter : s.getReg .x6 = s.getMem 0x80438) (limit : s.getReg .x7 = 7)
    (bound : step < 7) (data : Buffered s level tree side chain step value) :
    ∃ final, Trace hash image s 10 17 1 1 final ∧ final.pc = 0x1580 ∧
      Buffered final level tree side chain (step+1) (Reference.chainHash hash level tree side chain step value) ∧
      CachedPrepare.Ready final ∧ final.getReg .x28 = 0x80438 ∧ final.getReg .x13 = 4294967296 ∧
      (final.getReg .x11 = 48 ∧ final.getReg .x12 = 0x80020 ∧ final.getReg .x5 = 1) ∧
      final.getReg .x6 = final.getMem 0x80438 ∧
      final.getReg .x7 = 7 ∧
      final.getReg .x1 = s.getReg .x1 ∧ final.getReg .x2 = s.getReg .x2 ∧
      (∀ a, OutsideChainWork a → final.getMem a = s.getMem a) := by
  have ne : s.getMem 0x80438 ≠ 7 := by
    rw [data.stepEq]
    intro eq
    have h := congrArg BitVec.toNat eq
    change step % 2^64 = 7 at h
    omega
  have checkedPC : (CounterCheck.shortCheck s).pc = 0x1584 := by
    rw [CounterCheck.pc s counter limit,pc,if_neg ne]; rfl
  have checkedData : Buffered (CounterCheck.state s) level tree side chain step value := by
    constructor
    · simpa only [CounterCheck.mem] using data.levelEq
    · simpa only [CounterCheck.mem] using data.leafEq
    · simpa only [CounterCheck.mem] using data.chainEq
    · simpa only [CounterCheck.mem] using data.stepEq
    · simpa only [CounterCheck.mem] using data.indexEq
    · simpa only [CounterCheck.mem] using data.valueEq
  obtain ⟨final,run,finalPC,finalData,finalReady,finalBase,finalConstant,finalArgs,finalCounter,finalLimit,ra,sp,frame⟩ :=
    StepBaseData.recurrent image hash 0x1584 prepareCode coreCode (CounterCheck.shortCheck s)
      level tree step side chain value checkedPC (by rw [CounterCheck.short_base]; exact base)
      ((check_constant s).trans constant) (CounterCheck.ready s ready)
      ⟨(CounterCheck.reg s .x11 (by decide)).trans args.1,
       (CounterCheck.reg s .x12 (by decide)).trans args.2.1,
       (CounterCheck.reg s .x5 (by decide)).trans args.2.2⟩ (CounterCheck.counter s counter) checkedData
  refine ⟨final,(CounterCheck.block image 0x1580 checkCode s pc).trace.trans run,finalPC,
    finalData,finalReady,finalBase,finalConstant,finalArgs,finalCounter,finalLimit.trans ((PersistentLimit.check_preserves s .x7).trans limit),ra.trans (CounterCheck.short_stack s).1,
    sp.trans (CounterCheck.short_stack s).2,?_⟩
  intro a outside
  rw [frame a outside,CounterCheck.short_mem]

/-- info: 'SigGolfCandidate.Hypertree.StepBaseSteps.recurrent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms recurrent
end SigGolfCandidate.Hypertree.StepBaseSteps
