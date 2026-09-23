import SigGolfCandidate.Hypertree.VerifyChainStep

namespace SigGolfCandidate.Hypertree.Verifying
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 Keygen Signing ChainLoopControl
set_option maxRecDepth 4096

/-- The verifier executes exactly the remaining Winternitz chain fragment and exits with step seven. -/
theorem chain_loop_reuse (hash : Hash) (s : MachineState) (level tree start remaining : Nat)
    (side : Bool) (chain : Reference.Chain) (value : Reference.Digest)
    (pc : s.pc = 0x14f4) (base : s.getReg .x28 = 0x80438) (length : start + remaining = 7)
    (data : ChainData s level tree side chain start value) :
    ∃ final, Trace hash verify s (45*remaining+3) (52*remaining+3) remaining remaining final ∧
      final.pc = 0x163c ∧
      ChainData final level tree side chain 7 (walk (Reference.chainHash hash level tree side chain) start remaining value) ∧
      final.getReg .x1 = s.getReg .x1 ∧ final.getReg .x2 = s.getReg .x2 ∧
      (∀ a, OutsideChainWork a → final.getMem a = s.getMem a) := by
  induction remaining generalizing s start value with
  | zero =>
    have startEq : start = 7 := by omega
    subst start
    refine ⟨CheckReuse.shortCheck s, (CheckReuse.block verify 0x14f4 verify_short_check s pc base).trace, ?_, ?_,
      (CheckReuse.short_stack s).1, (CheckReuse.short_stack s).2, ?_⟩
    · rw [CheckReuse.short_pc s base, pc, data.stepEq]; decide
    · simpa only [walk] using data.shortCheck
    · intro a _; exact CheckReuse.short_mem s a
  | succ remaining ih =>
    obtain ⟨next, pre, nextPC, nextData, nextBase, nextRA, nextSP, nextFrame⟩ := chain_step hash s level tree start
      side chain value pc base (by omega) data
    obtain ⟨final, tail, finalPC, finalData, finalRA, finalSP, finalFrame⟩ := ih next (start+1)
      (Reference.chainHash hash level tree side chain start value) nextPC nextBase (by omega) nextData
    refine ⟨final, ?_, finalPC, ?_, finalRA.trans nextRA, finalSP.trans nextSP, ?_⟩
    · convert pre.trans tail using 1 <;> omega
    · simpa only [walk] using finalData
    · intro a outside
      exact (finalFrame a outside).trans (nextFrame a outside)

/-- The first address setup is charged once; later checks reuse the address established by the backedge. -/
theorem chain_loop (hash : Hash) (s : MachineState) (level tree start remaining : Nat)
    (side : Bool) (chain : Reference.Chain) (value : Reference.Digest)
    (pc : s.pc = 0x14ec) (length : start + remaining = 7)
    (data : ChainData s level tree side chain start value) :
    ∃ final, Trace hash verify s (45*remaining+5) (52*remaining+5) remaining remaining final ∧
      final.pc = 0x163c ∧
      ChainData final level tree side chain 7 (walk (Reference.chainHash hash level tree side chain) start remaining value) ∧
      final.getReg .x1 = s.getReg .x1 ∧ final.getReg .x2 = s.getReg .x2 ∧
      (∀ a, OutsideChainWork a → final.getMem a = s.getMem a) := by
  have preparedPC : (CheckReuse.setup s).pc = 0x14f4 := by rw [CheckReuse.setup_pc, pc]; rfl
  have preparedData : ChainData (CheckReuse.setup s) level tree side chain start value := by
    constructor
    · simpa only [CheckReuse.setup_mem] using data.levelEq
    · simpa only [CheckReuse.setup_mem] using data.leafEq
    · simpa only [CheckReuse.setup_mem] using data.chainEq
    · simpa only [CheckReuse.setup_mem] using data.stepEq
    · simpa only [CheckReuse.setup_mem] using data.indexEq
    · simpa only [CheckReuse.setup_mem] using data.valueEq
  obtain ⟨final, tail, finalPC, finalData, ra, sp, frame⟩ := chain_loop_reuse hash (CheckReuse.setup s)
    level tree start remaining side chain value preparedPC (CheckReuse.setup_base s) length preparedData
  refine ⟨final, ?_, finalPC, finalData, ra.trans (CheckReuse.setup_stack s).1,
    sp.trans (CheckReuse.setup_stack s).2, ?_⟩
  · convert (CheckReuse.setup_block verify 0x14ec verify_chain_check s pc).trace.trans tail using 1 <;> omega
  · intro a outside
    rw [frame a outside, CheckReuse.setup_mem]

/-- Any valid base-eight digit gives a universally terminating, precisely priced verifier chain fragment. -/
theorem chain_from_digit (hash : Hash) (s : MachineState) (level tree : Nat)
    (side : Bool) (chain : Reference.Chain) (digit : Fin 8) (value : Reference.Digest)
    (pc : s.pc = 0x14ec) (data : ChainData s level tree side chain digit.val value) :
    ∃ final, Trace hash verify s (45*(7-digit.val)+5) (52*(7-digit.val)+5) (7-digit.val) (7-digit.val) final ∧
      final.pc = 0x163c ∧
      ChainData final level tree side chain 7
        (walk (Reference.chainHash hash level tree side chain) digit.val (7-digit.val) value) ∧
      final.getReg .x1 = s.getReg .x1 ∧ final.getReg .x2 = s.getReg .x2 ∧
      (∀ a, OutsideChainWork a → final.getMem a = s.getMem a) :=
  chain_loop hash s level tree digit.val (7-digit.val) side chain value pc (by have := digit.isLt; omega) data

/-- info: 'SigGolfCandidate.Hypertree.Verifying.chain_from_digit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms chain_from_digit

end SigGolfCandidate.Hypertree.Verifying
