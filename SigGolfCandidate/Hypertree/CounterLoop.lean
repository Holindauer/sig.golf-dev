import SigGolfCandidate.Hypertree.CounterSteps
namespace SigGolfCandidate.Hypertree.Verifying
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 Keygen Signing ChainLoopControl
open InplaceData
set_option maxRecDepth 8192
theorem counter_loop_recurrent (image : Image)
    (checkCode : CounterCheck.Code image 0x1580)
    (chainCode : CounterSteps.RecurrentCode image 0x1588)
    (restoreCode : InplaceRestore.Code image 0x1604) (hash : Hash) (s : MachineState) (level tree start remaining : Nat)
    (side : Bool) (chain : Reference.Chain) (value : Reference.Digest)
    (pc : s.pc = 0x1580) (base : s.getReg .x28 = 0x80438) (constant : s.getReg .x13 = 4294967296) (ready : CachedPrepare.Ready s)
    (args : s.getReg .x11 = 384 ∧ s.getReg .x12 = 0x80020 ∧ s.getReg .x5 = 1) (counter : s.getReg .x6 = s.getMem 0x80438) (length : start + remaining = 7)
    (data : Buffered s level tree side chain start value) :
    ∃ final, Trace hash image s (13*remaining+7) (20*remaining+7) remaining remaining final ∧
      final.pc = 0x163c ∧
      ChainData final level tree side chain 7 (walk (Reference.chainHash hash level tree side chain) start remaining value) ∧
      final.getReg .x1 = s.getReg .x1 ∧ final.getReg .x2 = s.getReg .x2 ∧
      (∀ a, OutsideChainWork a → final.getMem a = s.getMem a) := by
  induction remaining generalizing s start value with
  | zero =>
    have startEq : start = 7 := by omega
    subst start
    let checked := CounterCheck.shortCheck s
    have checkedPC : checked.pc = 0x1604 := by
      rw [CounterCheck.pc s counter,pc,data.stepEq]; decide
    have checkedBase : checked.getReg .x28 = 0x80438 := (CounterCheck.short_base s).trans base
    have checkedData : Buffered checked level tree side chain 7 value := by
      constructor
      · simpa only [checked,CounterCheck.short_mem] using data.levelEq
      · simpa only [checked,CounterCheck.short_mem] using data.leafEq
      · simpa only [checked,CounterCheck.short_mem] using data.chainEq
      · simpa only [checked,CounterCheck.short_mem] using data.stepEq
      · simpa only [checked,CounterCheck.short_mem] using data.indexEq
      · simpa only [checked,CounterCheck.short_mem] using data.valueEq
    refine ⟨InplaceRestore.state checked,
      (CounterCheck.block image 0x1580 checkCode s pc).trace.trans
        (InplaceRestore.block image 0x1604 restoreCode checked checkedPC checkedBase).trace,?_,?_,?_,?_,?_⟩
    · rw [InplaceRestore.pc,checkedPC]; rfl
    · simpa only [walk] using Buffered.restore checked level tree side chain 7 value checkedBase checkedData
    · exact (InplaceRestore.preserved checked).1.trans (CounterCheck.short_stack s).1
    · exact (InplaceRestore.preserved checked).2.1.trans (CounterCheck.short_stack s).2
    · intro a outside
      rw [InplaceRestore.mem checked checkedBase,
        if_neg (by simpa [wordAddress] using outside.2.2.1 1),if_neg (by simpa [wordAddress] using outside.2.2.1 0),CounterCheck.short_mem]
  | succ remaining ih =>
    obtain ⟨next, pre, nextPC, nextData, nextReady, nextBase, nextConstant, nextArgs, nextCounter, nextRA, nextSP, nextFrame⟩ := CounterSteps.recurrent image hash checkCode chainCode.1 chainCode.2 s level tree start
      side chain value pc base constant ready args counter (by omega) data
    obtain ⟨final, tail, finalPC, finalData, finalRA, finalSP, finalFrame⟩ := ih next (start+1)
      (Reference.chainHash hash level tree side chain start value) nextPC nextBase nextConstant nextReady nextArgs nextCounter (by omega) nextData
    refine ⟨final, ?_, finalPC, ?_, finalRA.trans nextRA, finalSP.trans nextSP, ?_⟩
    · convert pre.trans tail using 1 <;> omega
    · simpa only [walk] using finalData
    · intro a outside
      exact (finalFrame a outside).trans (nextFrame a outside)


/-- Setup costs five instructions for an empty chain and thirty-six otherwise. -/
def counterOverhead (remaining : Nat) : Nat := if remaining = 0 then 5 else 36

theorem counter_loop (image : Image)
    (setupCode : CheckCode image 0x14ec)
    (initialCheck : CheckReuse.Code image 0x14f4)
    (initialCode : CounterSteps.InitialCode image 0x1500)
    (checkCode : CounterCheck.Code image 0x1580)
    (chainCode : CounterSteps.RecurrentCode image 0x1588)
    (restoreCode : InplaceRestore.Code image 0x1604)
    (hash : Hash) (s : MachineState) (level tree start remaining : Nat)
    (side : Bool) (chain : Reference.Chain) (value : Reference.Digest)
    (pc : s.pc = 0x14ec) (length : start + remaining = 7)
    (data : ChainData s level tree side chain start value) :
    ∃ final, Trace hash image s (13*remaining+counterOverhead remaining)
      (20*remaining+counterOverhead remaining) remaining remaining final ∧
      final.pc = 0x163c ∧
      ChainData final level tree side chain 7 (walk (Reference.chainHash hash level tree side chain) start remaining value) ∧
      final.getReg .x1 = s.getReg .x1 ∧ final.getReg .x2 = s.getReg .x2 ∧
      (∀ a, OutsideChainWork a → final.getMem a = s.getMem a) := by
  let prepared := CheckReuse.setup s
  have preparedPC : prepared.pc = 0x14f4 := by rw [CheckReuse.setup_pc, pc]; rfl
  have preparedBase : prepared.getReg .x28 = 0x80438 := CheckReuse.setup_base s
  have preparedData : ChainData prepared level tree side chain start value := by
    constructor
    · simpa only [prepared, CheckReuse.setup_mem] using data.levelEq
    · simpa only [prepared, CheckReuse.setup_mem] using data.leafEq
    · simpa only [prepared, CheckReuse.setup_mem] using data.chainEq
    · simpa only [prepared, CheckReuse.setup_mem] using data.stepEq
    · simpa only [prepared, CheckReuse.setup_mem] using data.indexEq
    · simpa only [prepared, CheckReuse.setup_mem] using data.valueEq
  have setupTrace := (CheckReuse.setup_block image 0x14ec setupCode s pc).trace (hash := hash)
  cases remaining with
  | zero =>
    have startEq : start = 7 := by omega
    subst start
    refine ⟨CheckReuse.shortCheck prepared, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa [counterOverhead] using setupTrace.trans (CheckReuse.block image 0x14f4 initialCheck prepared preparedPC preparedBase).trace
    · rw [CheckReuse.short_pc prepared preparedBase, preparedPC, preparedData.stepEq]; decide
    · simpa only [walk] using preparedData.shortCheck
    · exact (CheckReuse.short_stack prepared).1.trans (CheckReuse.setup_stack s).1
    · exact (CheckReuse.short_stack prepared).2.trans (CheckReuse.setup_stack s).2
    · intro a _; rw [CheckReuse.short_mem, CheckReuse.setup_mem]
  | succ remaining =>
    obtain ⟨next, pre, nextPC, nextData, nextReady, nextBase, nextConstant, nextArgs, nextCounter, nextRA, nextSP, nextFrame⟩ :=
      CounterSteps.initial image hash initialCheck initialCode.1 initialCode.2 prepared level tree start side chain value
        preparedPC preparedBase (by omega) preparedData
    obtain ⟨final, tail, finalPC, finalData, finalRA, finalSP, finalFrame⟩ :=
      counter_loop_recurrent image checkCode chainCode restoreCode hash next level tree (start+1) remaining side chain
        (Reference.chainHash hash level tree side chain start value) nextPC nextBase nextConstant nextReady nextArgs nextCounter (by omega) nextData
    refine ⟨final, ?_, finalPC, ?_, ?_, ?_, ?_⟩
    · convert setupTrace.trans (pre.trans tail) using 1 <;> simp [counterOverhead] <;> omega
    · simpa only [walk] using finalData
    · exact finalRA.trans (nextRA.trans (CheckReuse.setup_stack s).1)
    · exact finalSP.trans (nextSP.trans (CheckReuse.setup_stack s).2)
    · intro a outside
      rw [finalFrame a outside, nextFrame a outside, CheckReuse.setup_mem]

theorem counterOverhead_le (n : Nat) : counterOverhead n ≤ 36 := by
  unfold counterOverhead; split <;> omega

/-- info: 'SigGolfCandidate.Hypertree.Verifying.counter_loop_recurrent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms counter_loop_recurrent
/-- info: 'SigGolfCandidate.Hypertree.Verifying.counter_loop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms counter_loop
end SigGolfCandidate.Hypertree.Verifying
