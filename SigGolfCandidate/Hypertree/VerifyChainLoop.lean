import SigGolfCandidate.Hypertree.VerifyChainStep

namespace SigGolfCandidate.Hypertree.Verifying
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 Keygen Signing ChainLoopControl
set_option maxRecDepth 4096

/-- The verifier executes exactly the remaining Winternitz chain fragment and exits with step seven. -/
theorem chain_loop (hash : Hash) (s : MachineState) (level tree start remaining : Nat)
    (side : Bool) (chain : Reference.Chain) (value : Reference.Digest)
    (pc : s.pc = 0x14ec) (length : start + remaining = 7)
    (data : ChainData s level tree side chain start value) :
    ∃ final, Trace hash verify s (96*remaining+5) (103*remaining+5) remaining remaining final ∧
      final.pc = 0x163c ∧
      ChainData final level tree side chain 7 (walk (Reference.chainHash hash level tree side chain) start remaining value) ∧
      final.getReg .x1 = s.getReg .x1 ∧ final.getReg .x2 = s.getReg .x2 ∧
      (∀ a, OutsideChainWork a → final.getMem a = s.getMem a) := by
  induction remaining generalizing s start value with
  | zero =>
    have startEq : start = 7 := by omega
    subst start
    refine ⟨check s, (check_block verify 0x14ec verify_chain_check s pc).trace, ?_, ?_,
      (check_stack s).1, (check_stack s).2, ?_⟩
    · rw [check_pc, pc, data.stepEq]; decide
    · simpa only [walk] using data.check
    · intro a _; exact check_mem s a
  | succ remaining ih =>
    obtain ⟨next, pre, nextPC, nextData, nextRA, nextSP, nextFrame⟩ := chain_step hash s level tree start
      side chain value pc (by omega) data
    obtain ⟨final, tail, finalPC, finalData, finalRA, finalSP, finalFrame⟩ := ih next (start+1)
      (Reference.chainHash hash level tree side chain start value) nextPC (by omega) nextData
    refine ⟨final, ?_, finalPC, ?_, finalRA.trans nextRA, finalSP.trans nextSP, ?_⟩
    · convert pre.trans tail using 1 <;> omega
    · simpa only [walk] using finalData
    · intro a outside
      exact (finalFrame a outside).trans (nextFrame a outside)

/-- Any valid base-eight digit gives a universally terminating, precisely priced verifier chain fragment. -/
theorem chain_from_digit (hash : Hash) (s : MachineState) (level tree : Nat)
    (side : Bool) (chain : Reference.Chain) (digit : Fin 8) (value : Reference.Digest)
    (pc : s.pc = 0x14ec) (data : ChainData s level tree side chain digit.val value) :
    ∃ final, Trace hash verify s (96*(7-digit.val)+5) (103*(7-digit.val)+5) (7-digit.val) (7-digit.val) final ∧
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
