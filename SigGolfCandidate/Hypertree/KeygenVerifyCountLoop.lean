import SigGolfCandidate.Hypertree.KeygenVerifyCount

namespace SigGolfCandidate.Hypertree.KeygenVerifyCount
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 Keygen Signing Verifying
set_option maxRecDepth 4096

theorem leaf_loop_exact (hash : Hash) (s : MachineState) (level tree : Nat) (side : Bool) (base : Nat)
    (message : Reference.Digest) (values : Reference.Chain → Reference.Digest) (start remaining : Nat)
    (length : start+remaining = 46) (pc : s.pc = if start = 46 then 0x1690 else 0x1490)
    (data : LeafData s level tree side base message values) (counter : s.getMem 0x80430 = BitVec.ofNat 64 start)
    (completed : EndpointPrefix s (recoveredEndpoint hash level tree side message values) start)
    (aligned : base % 8 = 0) (bound : base+736 ≤ 0x80000) :
    ∃ final steps cycles calls, Trace hash verify s steps cycles calls calls final ∧
      steps ≤ 721*remaining ∧ cycles ≤ 770*remaining ∧ calls ≤ 7*remaining ∧ final.pc = 0x1690 ∧
      final.getMem 0x80430 = 46 ∧ LeafData final level tree side base message values ∧
      EndpointPrefix final (recoveredEndpoint hash level tree side message values) 46 ∧
      final.getReg .x1 = s.getReg .x1 ∧ final.getReg .x2 = s.getReg .x2 ∧
      (∀ a, OutsideLeafWork a → final.getMem a = s.getMem a) ∧
      calls + chainPrefix message start = chainPrefix message 46 := by
  induction remaining generalizing s start with
  | zero =>
    have startEq : start = 46 := by omega
    subst start
    refine ⟨s, 0, 0, 0, Trace.refl s, by omega, by omega, by omega, ?_, ?_, data, completed, rfl, rfl, ?_, by simp⟩
    · simpa using pc
    · exact counter
    · intro _ _; rfl
  | succ remaining ih =>
    have startLt : start < 46 := by omega
    let chain : Reference.Chain := ⟨start, startLt⟩
    have atLoop : s.pc = 0x1490 := by simpa only [if_neg (by omega : start ≠ 46)] using pc
    obtain ⟨next, pre, nextPC, nextCounter, nextData, output, nextRA, nextSP, nextFrame⟩ :=
      leaf_step hash s level tree side base message values chain atLoop data counter aligned bound
    have nextPrefix : EndpointPrefix next (recoveredEndpoint hash level tree side message values) (start+1) := by
      intro c hc i
      by_cases same : c.val = start
      · have eq : c = chain := Fin.ext same
        subst c
        exact output i
      · have before : c.val < start := by omega
        have neCounter : KeygenEndpoint.endpointAddress c.val i.val ≠ 0x80430 := by
          intro eq
          have h := congrArg BitVec.toNat eq
          have hc := c.isLt
          have hi := i.isLt
          change (0x80800+16*c.val+8*i.val) % 2^64 = 0x80430 at h
          omega
        rw [nextFrame _ (endpoint_outside_chain c i) neCounter]
        · exact completed c before i
        · intro j
          exact endpointAddress_ne c chain i j (fun eq => same (congrArg Fin.val eq))
    obtain ⟨final, steps, cycles, calls, run, hsteps, hcycles, hcalls, finalPC, finalCounter,
      finalData, finalPrefix, finalRA, finalSP, finalFrame, exactCalls⟩ :=
      ih next (start+1) (by omega) nextPC nextData nextCounter nextPrefix
    refine ⟨final, (96*(7-(Reference.digit message chain).val)+49)+steps,
      (103*(7-(Reference.digit message chain).val)+49)+cycles,
      (7-(Reference.digit message chain).val)+calls, pre.trans run, ?_, ?_, ?_,
      finalPC, finalCounter, finalData, finalPrefix, finalRA.trans nextRA, finalSP.trans nextSP, ?_, ?_⟩
    · omega
    · omega
    · omega
    · intro a outside
      exact (finalFrame a outside).trans (nextFrame a (outside_leaf_chain a outside)
        outside.2.2.2.2.1 (outside_leaf_endpoint a outside chain))

    · rw [chainPrefix_succ message start startLt] at exactCalls
      change (7-(Reference.digit message ⟨start,startLt⟩).val)+calls+chainPrefix message start = _
      omega

theorem recover_all_chains_exact (hash : Hash) (s : MachineState) (level tree : Nat) (side : Bool) (base : Nat)
    (message : Reference.Digest) (values : Reference.Chain → Reference.Digest)
    (pc : s.pc = 0x1490) (data : LeafData s level tree side base message values)
    (counter : s.getMem 0x80430 = 0) (aligned : base % 8 = 0) (bound : base+736 ≤ 0x80000) :
    ∃ final steps cycles calls, Trace hash verify s steps cycles calls calls final ∧
      steps ≤ 33166 ∧ cycles ≤ 35420 ∧ calls ≤ 322 ∧ final.pc = 0x1690 ∧
      final.getMem 0x80430 = 46 ∧ LeafData final level tree side base message values ∧
      (∀ chain : Reference.Chain, ∀ i : Fin 2,
        final.getMem (KeygenEndpoint.endpointAddress chain.val i.val) =
          (recoveredEndpoint hash level tree side message values chain).extractLsb' (64*i.val) 64) ∧
      final.getReg .x1 = s.getReg .x1 ∧ final.getReg .x2 = s.getReg .x2 ∧
      (∀ a, OutsideLeafWork a → final.getMem a = s.getMem a) ∧ calls = chainCalls message := by
  obtain ⟨final, steps, cycles, calls, run, hsteps, hcycles, hcalls, finalPC, finalCounter,
    finalData, endpoints, finalRA, finalSP, frame, exactCalls⟩ := leaf_loop_exact hash s level tree side base message values 0 46 rfl pc
      data counter (by intro c hc; omega) aligned bound
  refine ⟨final, steps, cycles, calls, run, hsteps, hcycles, hcalls, finalPC, finalCounter,
    finalData, fun c => endpoints c c.isLt, finalRA, finalSP, frame, ?_⟩

  simpa only [chainPrefix_zero,Nat.add_zero,chainPrefix_full] using exactCalls

end SigGolfCandidate.Hypertree.KeygenVerifyCount
