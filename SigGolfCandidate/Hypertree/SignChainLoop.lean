import SigGolfCandidate.Hypertree.SignCaptureFrame

namespace SigGolfCandidate.Hypertree.Signing
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 Keygen ChainLoopControl Verifying
set_option maxRecDepth 4096

/-- The signer executes every capture and HASH in a remaining chain fragment. The resource
bound allows the longest capture branch at every step; the HASH count is exact. -/
theorem sign_chain_loop (hash : Hash) (s : MachineState) (pointer level tree start remaining : Nat)
    (side : Bool) (chain : Reference.Chain) (value : Reference.Digest)
    (pc : s.pc = 0x1698) (length : start + remaining = 7)
    (valid : CapturePointerValid pointer) (ptr : s.getMem 0x80448 = BitVec.ofNat 64 pointer)
    (data : ChainData s level tree side chain start value) :
    ∃ final instructions cycles, Trace hash sign s instructions cycles remaining remaining final ∧
      instructions ≤ 131 * remaining + 40 ∧ cycles ≤ 138 * remaining + 40 ∧
      final.pc = 0x1874 ∧
      ChainData final level tree side chain 7
        (walk (Reference.chainHash hash level tree side chain) start remaining value) ∧
      final.getReg .x1 = s.getReg .x1 ∧ final.getReg .x2 = s.getReg .x2 ∧
      (∀ a, OutsideChainWork a →
        (∀ i : Fin 2, a ≠ wordAddress (pointer + 16 * chain.val) i.val) → final.getMem a = s.getMem a) := by
  induction remaining generalizing s start value with
  | zero =>
    have startEq : start = 7 := by omega
    subst start
    have target := capture_target s pointer chain valid ptr data.chainEq
    obtain ⟨safe, safeNext⟩ := capture_access pointer chain valid
    have cap := captureUpper_block sign 0x1698 sign_upper_capture_code s pc
      (capture_digit_access s chain data.chainEq)
      (by rw [target]; exact safe)
      (by rw [target, capture_target_next]; exact safeNext)
    have capPC : (captureUpperState s).pc = 0x1724 := by rw [captureUpper_pc, pc]; rfl
    have capData := captureUpper_chainData s pointer level tree 7 side chain value valid ptr data
    have done := check_block sign 0x1724 sign_chain_check _ capPC
    refine ⟨check (captureUpperState s), captureUpperSteps s + 5, captureUpperSteps s + 5,
      cap.trace.trans done.trace, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · have := captureUpper_steps_le s; omega
    · have := captureUpper_steps_le s; omega
    · rw [check_pc, capPC, capData.stepEq]; rfl
    · simpa only [walk] using capData.check
    · exact (check_stack _).1.trans (captureUpper_ra s)
    · exact (check_stack _).2.trans (captureUpper_sp s)
    · intro a _ outside
      rw [check_mem]
      exact captureUpper_frame s pointer chain valid ptr data.chainEq a outside
  | succ remaining ih =>
    have target := capture_target s pointer chain valid ptr data.chainEq
    obtain ⟨safe, safeNext⟩ := capture_access pointer chain valid
    have cap := captureUpper_block sign 0x1698 sign_upper_capture_code s pc
      (capture_digit_access s chain data.chainEq)
      (by rw [target]; exact safe)
      (by rw [target, capture_target_next]; exact safeNext)
    have capPC : (captureUpperState s).pc = 0x1724 := by rw [captureUpper_pc, pc]; rfl
    have capData := captureUpper_chainData s pointer level tree start side chain value valid ptr data
    obtain ⟨next, core, nextPC, nextData, nextRA, nextSP, nextFrame⟩ := chain_core_step hash
      (captureUpperState s) level tree start side chain value capPC (by omega) capData
    have nextPtr : next.getMem 0x80448 = BitVec.ofNat 64 pointer := by
      rw [nextFrame _ (by unfold OutsideChainWork; decide), captureUpper_high_frame s pointer chain valid ptr data.chainEq _ (by decide)]
      exact ptr
    obtain ⟨final, steps, cycles, tail, stepsBound, cyclesBound, finalPC, finalData,
      finalRA, finalSP, finalFrame⟩ := ih next (start+1)
      (Reference.chainHash hash level tree side chain start value) nextPC (by omega) nextPtr nextData
    refine ⟨final, captureUpperSteps s + 96 + steps, captureUpperSteps s + 103 + cycles,
      ?_, ?_, ?_, finalPC, ?_, ?_, ?_, ?_⟩
    · convert (cap.trace.trans core).trans tail using 1 <;> omega
    · have := captureUpper_steps_le s; omega
    · have := captureUpper_steps_le s; omega
    · simpa only [walk] using finalData
    · exact finalRA.trans (nextRA.trans (captureUpper_ra s))
    · exact finalSP.trans (nextSP.trans (captureUpper_sp s))
    · intro a workOutside captureOutside
      rw [finalFrame a workOutside captureOutside, nextFrame a workOutside]
      exact captureUpper_frame s pointer chain valid ptr data.chainEq a captureOutside

/-- A complete signer chain computes exactly the reference endpoint, including the final
step-seven capture, with seven compression calls and a uniform cycle bound. -/
theorem sign_chain_endpoint (hash : Hash) (s : MachineState) (secretKey : SecretKey) (pointer level tree : Nat)
    (side : Bool) (chain : Reference.Chain) (pc : s.pc = 0x1698)
    (valid : CapturePointerValid pointer) (ptr : s.getMem 0x80448 = BitVec.ofNat 64 pointer)
    (data : ChainData s level tree side chain 0 (Reference.secret hash secretKey level tree side chain)) :
    ∃ final instructions cycles, Trace hash sign s instructions cycles 7 7 final ∧
      instructions ≤ 957 ∧ cycles ≤ 1006 ∧ final.pc = 0x1874 ∧
      ChainData final level tree side chain 7 (Reference.endpoint hash secretKey level tree side chain) ∧
      final.getReg .x1 = s.getReg .x1 ∧ final.getReg .x2 = s.getReg .x2 ∧
      (∀ a, OutsideChainWork a →
        (∀ i : Fin 2, a ≠ wordAddress (pointer + 16 * chain.val) i.val) → final.getMem a = s.getMem a) :=
  sign_chain_loop hash s pointer level tree 0 7 side chain _ pc (by decide) valid ptr data

/-- info: 'SigGolfCandidate.Hypertree.Signing.sign_chain_endpoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sign_chain_endpoint

end SigGolfCandidate.Hypertree.Signing
