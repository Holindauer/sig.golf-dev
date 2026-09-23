import SigGolfCandidate.Hypertree.SignLeafLoop

namespace SigGolfCandidate.Hypertree.Signing
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 Keygen Verifying
set_option maxRecDepth 4096

/-- The unselected leaf computes every chain endpoint without changing the signature. -/
theorem sign_unselected_leaf_loop (hash : Hash) (s : MachineState) (secretKey : SecretKey) (pointer level tree start remaining : Nat)
    (side : Bool)
    (pc : s.pc = if start = 46 then 0x18c8 else 0x1584) (length : start + remaining = 46)
    (valid : CapturePointerValid pointer)
    (data : LeafData s secretKey level tree side start)
    (ptr : s.getMem 0x80448 = BitVec.ofNat 64 pointer)
    (unselected : s.getMem 0x80428 ≠ s.getMem 0x80420)
    (endpoints : EndpointsBefore s hash secretKey level tree side start) :
    ∃ final instructions cycles, Trace hash sign s instructions cycles (8*remaining) (8*remaining) final ∧
      instructions ≤ 1071 * remaining ∧ cycles ≤ 1127 * remaining ∧ final.pc = 0x18c8 ∧
      LeafData final secretKey level tree side 46 ∧
      EndpointsBefore final hash secretKey level tree side 46 ∧
      final.getReg .x1 = s.getReg .x1 ∧ final.getReg .x2 = s.getReg .x2 ∧
      (∀ a, OutsideLeafWork a → final.getMem a = s.getMem a) := by
  induction remaining generalizing s start with
  | zero =>
    have eq : start = 46 := by omega
    subst start
    refine ⟨s, 0, 0, Trace.refl s, by omega, by omega, ?_, data, endpoints, rfl, rfl, ?_⟩
    · simpa using pc
    · intro a _; rfl
  | succ remaining ih =>
    have bound : start < 46 := by omega
    let chain : Reference.Chain := ⟨start, bound⟩
    have prePC : s.pc = 0x1584 := by rw [pc, if_neg (by omega)]
    obtain ⟨next, steps, cycles, pre, stepsBound, cyclesBound, nextPC, nextData, endpoint,
      nextRA, nextSP, nextFrame⟩ := sign_unselected_iteration hash s secretKey pointer level tree side chain
        prePC valid ptr data unselected
    have nextPtr : next.getMem 0x80448 = BitVec.ofNat 64 pointer := by
      rw [nextFrame _ (outsideIteration_metadata chain _ (by decide) (by unfold OutsideChainWork; decide) (by decide))]
      exact ptr
    have nextUnselected : next.getMem 0x80428 ≠ next.getMem 0x80420 := by
      rw [nextFrame _ (outsideIteration_metadata chain _ (by decide) (by unfold OutsideChainWork; decide) (by decide)),
        nextFrame _ (outsideIteration_metadata chain _ (by decide) (by unfold OutsideChainWork; decide) (by decide))]
      exact unselected
    have nextEndpoints : EndpointsBefore next hash secretKey level tree side (start+1) := by
      intro other less i
      by_cases same : other = chain
      · subst other; exact endpoint i
      · have prior : other.val < start := by
          have ne : other.val ≠ chain.val := by intro eq; exact same (Fin.ext eq)
          change other.val ≠ start at ne
          omega
        have outside := endpoint_outside_chain other i
        rw [nextFrame _ ⟨outside.1, outside.2, fun j => endpoint_distinct other chain i j same⟩]
        exact endpoints other prior i
    obtain ⟨final, finalSteps, finalCycles, tail, finalStepsBound, finalCyclesBound, finalPC, finalData,
      finalEndpoints, finalRA, finalSP, finalFrame⟩ := ih next (start+1) nextPC (by omega)
        nextData nextPtr nextUnselected nextEndpoints
    refine ⟨final, steps + finalSteps, cycles + finalCycles, ?_, by omega, by omega, finalPC,
      finalData, finalEndpoints, finalRA.trans nextRA, finalSP.trans nextSP, ?_⟩
    · convert pre.trans tail using 1 <;> omega
    · intro a outside
      rw [finalFrame a outside, nextFrame a ⟨outside.1, outside.2.1, outside.2.2 chain⟩]

theorem sign_unselected_leaf_chains (hash : Hash) (s : MachineState) (secretKey : SecretKey) (pointer level tree : Nat)
    (side : Bool) (pc : s.pc = 0x1584)
    (valid : CapturePointerValid pointer) (data : LeafData s secretKey level tree side 0)
    (ptr : s.getMem 0x80448 = BitVec.ofNat 64 pointer)
    (unselected : s.getMem 0x80428 ≠ s.getMem 0x80420) :
    ∃ final instructions cycles, Trace hash sign s instructions cycles 368 368 final ∧
      instructions ≤ 49266 ∧ cycles ≤ 51842 ∧ final.pc = 0x18c8 ∧
      LeafData final secretKey level tree side 46 ∧
      EndpointsBefore final hash secretKey level tree side 46 ∧
      final.getReg .x1 = s.getReg .x1 ∧ final.getReg .x2 = s.getReg .x2 ∧
      (∀ a, OutsideLeafWork a → final.getMem a = s.getMem a) :=
  sign_unselected_leaf_loop hash s secretKey pointer level tree 0 46 side pc (by decide) valid data ptr unselected
    (by intro chain lt; omega)

end SigGolfCandidate.Hypertree.Signing
