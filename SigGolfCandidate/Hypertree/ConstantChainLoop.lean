import SigGolfCandidate.Hypertree.ConstantChainStep
namespace SigGolfCandidate.Hypertree.Verifying
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 Keygen Signing ChainLoopControl
set_option maxRecDepth 8192
theorem constant_loop_recurrent (image : Image)
    (checkCode : ConstantCheck.Code image 0x1580)
    (chainCode : ConstantChain.ChainCode image 0x158c) (hash : Hash) (s : MachineState) (level tree start remaining : Nat)
    (side : Bool) (chain : Reference.Chain) (value : Reference.Digest)
    (pc : s.pc = 0x1580) (base : s.getReg .x28 = 0x80438) (constant : s.getReg .x13 = 4294967296) (ready : CachedPrepare.Ready s) (length : start + remaining = 7)
    (data : ChainData s level tree side chain start value) :
    ∃ final, Trace hash image s (26*remaining+3) (33*remaining+3) remaining remaining final ∧
      final.pc = 0x163c ∧
      ChainData final level tree side chain 7 (walk (Reference.chainHash hash level tree side chain) start remaining value) ∧
      final.getReg .x1 = s.getReg .x1 ∧ final.getReg .x2 = s.getReg .x2 ∧
      (∀ a, OutsideChainWork a → final.getMem a = s.getMem a) := by
  induction remaining generalizing s start value with
  | zero =>
    have startEq : start = 7 := by omega
    subst start
    refine ⟨ConstantCheck.shortCheck s, (ConstantCheck.block image 0x1580 checkCode s pc base).trace, ?_, ?_,
      (ConstantCheck.short_stack s).1, (ConstantCheck.short_stack s).2, ?_⟩
    · rw [ConstantCheck.short_pc s base, pc, data.stepEq]; decide
    · simpa only [walk] using data.constantCheck
    · intro a _; exact ConstantCheck.short_mem s a
  | succ remaining ih =>
    obtain ⟨next, pre, nextPC, nextData, nextBase, nextRA, nextSP, nextFrame, nextReady, nextConstant⟩ := recurrent_constant_step image checkCode chainCode hash s level tree start
      side chain value pc base constant ready (by omega) data
    obtain ⟨final, tail, finalPC, finalData, finalRA, finalSP, finalFrame⟩ := ih next (start+1)
      (Reference.chainHash hash level tree side chain start value) nextPC nextBase nextConstant nextReady (by omega) nextData
    refine ⟨final, ?_, finalPC, ?_, finalRA.trans nextRA, finalSP.trans nextSP, ?_⟩
    · convert pre.trans tail using 1 <;> omega
    · simpa only [walk] using finalData
    · intro a outside
      exact (finalFrame a outside).trans (nextFrame a outside)


/-- Setup costs five instructions for an empty chain and twenty-four otherwise. -/
def constantOverhead (remaining : Nat) : Nat := if remaining = 0 then 5 else 24

theorem constant_loop (image : Image)
    (setupCode : CheckCode image 0x14ec)
    (initialCheck : CheckReuse.Code image 0x14f4)
    (initialCode : InitialConstantChain.ChainCode image 0x1500)
    (checkCode : ConstantCheck.Code image 0x1580)
    (chainCode : ConstantChain.ChainCode image 0x158c)
    (hash : Hash) (s : MachineState) (level tree start remaining : Nat)
    (side : Bool) (chain : Reference.Chain) (value : Reference.Digest)
    (pc : s.pc = 0x14ec) (length : start + remaining = 7)
    (data : ChainData s level tree side chain start value) :
    ∃ final, Trace hash image s (26*remaining+constantOverhead remaining)
      (33*remaining+constantOverhead remaining) remaining remaining final ∧
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
    · simpa [constantOverhead] using setupTrace.trans (CheckReuse.block image 0x14f4 initialCheck prepared preparedPC preparedBase).trace
    · rw [CheckReuse.short_pc prepared preparedBase, preparedPC, preparedData.stepEq]; decide
    · simpa only [walk] using preparedData.shortCheck
    · exact (CheckReuse.short_stack prepared).1.trans (CheckReuse.setup_stack s).1
    · exact (CheckReuse.short_stack prepared).2.trans (CheckReuse.setup_stack s).2
    · intro a _; rw [CheckReuse.short_mem, CheckReuse.setup_mem]
  | succ remaining =>
    obtain ⟨next, pre, nextPC, nextData, nextBase, nextRA, nextSP, nextFrame, nextReady, nextConstant⟩ :=
      initial_constant_step image initialCheck initialCode hash prepared level tree start side chain value
        preparedPC preparedBase (by omega) preparedData
    obtain ⟨final, tail, finalPC, finalData, finalRA, finalSP, finalFrame⟩ :=
      constant_loop_recurrent image checkCode chainCode hash next level tree (start+1) remaining side chain
        (Reference.chainHash hash level tree side chain start value) nextPC nextBase nextConstant nextReady (by omega) nextData
    refine ⟨final, ?_, finalPC, ?_, ?_, ?_, ?_⟩
    · convert setupTrace.trans (pre.trans tail) using 1 <;> simp [constantOverhead] <;> omega
    · simpa only [walk] using finalData
    · exact finalRA.trans (nextRA.trans (CheckReuse.setup_stack s).1)
    · exact finalSP.trans (nextSP.trans (CheckReuse.setup_stack s).2)
    · intro a outside
      rw [finalFrame a outside, nextFrame a outside, CheckReuse.setup_mem]

theorem constantOverhead_le (n : Nat) : constantOverhead n ≤ 24 := by
  unfold constantOverhead; split <;> omega

/-- info: 'SigGolfCandidate.Hypertree.Verifying.constant_loop_recurrent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms constant_loop_recurrent
/-- info: 'SigGolfCandidate.Hypertree.Verifying.constant_loop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms constant_loop
end SigGolfCandidate.Hypertree.Verifying
