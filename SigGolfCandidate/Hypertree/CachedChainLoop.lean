import SigGolfCandidate.Hypertree.CachedChainStep
namespace SigGolfCandidate.Hypertree.Verifying
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 Keygen Signing ChainLoopControl
set_option maxRecDepth 8192
theorem cached_loop_recurrent (image : Image)
    (checkCode : CachedCheck.Code image 0x1578)
    (chainCode : CachedChain.ChainCode image 0x1584) (hash : Hash) (s : MachineState) (level tree start remaining : Nat)
    (side : Bool) (chain : Reference.Chain) (value : Reference.Digest)
    (pc : s.pc = 0x1578) (base : s.getReg .x28 = 0x80438) (ready : CachedPrepare.Ready s) (length : start + remaining = 7)
    (data : ChainData s level tree side chain start value) :
    ∃ final, Trace hash image s (28*remaining+3) (35*remaining+3) remaining remaining final ∧
      final.pc = 0x163c ∧
      ChainData final level tree side chain 7 (walk (Reference.chainHash hash level tree side chain) start remaining value) ∧
      final.getReg .x1 = s.getReg .x1 ∧ final.getReg .x2 = s.getReg .x2 ∧
      (∀ a, OutsideChainWork a → final.getMem a = s.getMem a) := by
  induction remaining generalizing s start value with
  | zero =>
    have startEq : start = 7 := by omega
    subst start
    refine ⟨CachedCheck.shortCheck s, (CachedCheck.block image 0x1578 checkCode s pc base).trace, ?_, ?_,
      (CachedCheck.short_stack s).1, (CachedCheck.short_stack s).2, ?_⟩
    · rw [CachedCheck.short_pc s base, pc, data.stepEq]; decide
    · simpa only [walk] using data.cachedCheck
    · intro a _; exact CachedCheck.short_mem s a
  | succ remaining ih =>
    obtain ⟨next, pre, nextPC, nextData, nextBase, nextRA, nextSP, nextFrame, nextReady⟩ := recurrent_cached_step image checkCode chainCode hash s level tree start
      side chain value pc base ready (by omega) data
    obtain ⟨final, tail, finalPC, finalData, finalRA, finalSP, finalFrame⟩ := ih next (start+1)
      (Reference.chainHash hash level tree side chain start value) nextPC nextBase nextReady (by omega) nextData
    refine ⟨final, ?_, finalPC, ?_, finalRA.trans nextRA, finalSP.trans nextSP, ?_⟩
    · convert pre.trans tail using 1 <;> omega
    · simpa only [walk] using finalData
    · intro a outside
      exact (finalFrame a outside).trans (nextFrame a outside)


/-- Setup costs five instructions for an empty chain and twenty otherwise. -/
def cachedOverhead (remaining : Nat) : Nat := if remaining = 0 then 5 else 20

theorem cached_loop (image : Image)
    (setupCode : CheckCode image 0x14ec)
    (initialCheck : CheckReuse.Code image 0x14f4)
    (initialCode : InitialCachedChain.ChainCode image 0x1500)
    (checkCode : CachedCheck.Code image 0x1578)
    (chainCode : CachedChain.ChainCode image 0x1584)
    (hash : Hash) (s : MachineState) (level tree start remaining : Nat)
    (side : Bool) (chain : Reference.Chain) (value : Reference.Digest)
    (pc : s.pc = 0x14ec) (length : start + remaining = 7)
    (data : ChainData s level tree side chain start value) :
    ∃ final, Trace hash image s (28*remaining+cachedOverhead remaining)
      (35*remaining+cachedOverhead remaining) remaining remaining final ∧
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
    · simpa [cachedOverhead] using setupTrace.trans (CheckReuse.block image 0x14f4 initialCheck prepared preparedPC preparedBase).trace
    · rw [CheckReuse.short_pc prepared preparedBase, preparedPC, preparedData.stepEq]; decide
    · simpa only [walk] using preparedData.shortCheck
    · exact (CheckReuse.short_stack prepared).1.trans (CheckReuse.setup_stack s).1
    · exact (CheckReuse.short_stack prepared).2.trans (CheckReuse.setup_stack s).2
    · intro a _; rw [CheckReuse.short_mem, CheckReuse.setup_mem]
  | succ remaining =>
    obtain ⟨next, pre, nextPC, nextData, nextBase, nextRA, nextSP, nextFrame, nextReady⟩ :=
      initial_cached_step image initialCheck initialCode hash prepared level tree start side chain value
        preparedPC preparedBase (by omega) preparedData
    obtain ⟨final, tail, finalPC, finalData, finalRA, finalSP, finalFrame⟩ :=
      cached_loop_recurrent image checkCode chainCode hash next level tree (start+1) remaining side chain
        (Reference.chainHash hash level tree side chain start value) nextPC nextBase nextReady (by omega) nextData
    refine ⟨final, ?_, finalPC, ?_, ?_, ?_, ?_⟩
    · convert setupTrace.trans (pre.trans tail) using 1 <;> simp [cachedOverhead] <;> omega
    · simpa only [walk] using finalData
    · exact finalRA.trans (nextRA.trans (CheckReuse.setup_stack s).1)
    · exact finalSP.trans (nextSP.trans (CheckReuse.setup_stack s).2)
    · intro a outside
      rw [finalFrame a outside, nextFrame a outside, CheckReuse.setup_mem]

theorem cachedOverhead_le (n : Nat) : cachedOverhead n ≤ 20 := by
  unfold cachedOverhead; split <;> omega

/-- info: 'SigGolfCandidate.Hypertree.Verifying.cached_loop_recurrent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cached_loop_recurrent
/-- info: 'SigGolfCandidate.Hypertree.Verifying.cached_loop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cached_loop
end SigGolfCandidate.Hypertree.Verifying
