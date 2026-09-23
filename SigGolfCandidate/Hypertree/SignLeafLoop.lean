import SigGolfCandidate.Hypertree.SignLeafInvariant

namespace SigGolfCandidate.Hypertree.Signing
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 Keygen Verifying
set_option maxRecDepth 4096

/-- Previously completed endpoint and signature slots survive the next chain iteration. -/
theorem iteration_prefixes (s final : MachineState) (hash : Hash) (secretKey : SecretKey) (pointer level tree : Nat)
    (side : Bool) (message : Reference.Digest) (current : Reference.Chain)
    (valid : CapturePointerValid pointer)
    (oldEndpoints : EndpointsBefore s hash secretKey level tree side current.val)
    (oldSignature : SignatureBefore s hash secretKey pointer level tree side message current.val)
    (endpoint : ∀ i : Fin 2, final.getMem (KeygenEndpoint.endpointAddress current.val i.val) =
      (Reference.endpoint hash secretKey level tree side current).extractLsb' (64*i.val) 64)
    (captured : CapturedValue final pointer current ((Reference.signLayer hash secretKey level tree side message).values current))
    (frame : ∀ a, OutsideIteration current a →
      (∀ i : Fin 2, a ≠ wordAddress (pointer + 16 * current.val) i.val) → final.getMem a = s.getMem a) :
    EndpointsBefore final hash secretKey level tree side (current.val+1) ∧
      SignatureBefore final hash secretKey pointer level tree side message (current.val+1) := by
  constructor
  · intro chain less i
    by_cases same : chain = current
    · subst chain; exact endpoint i
    · have prior : chain.val < current.val := by
        have ne : chain.val ≠ current.val := by intro eq; exact same (Fin.ext eq)
        omega
      have outside := endpoint_outside_chain chain i
      rw [iteration_high_frame s final pointer current valid frame _
        ⟨outside.1, outside.2, fun j => endpoint_distinct chain current i j same⟩]
      · exact oldEndpoints chain prior i
      · have cb := chain.isLt
        have ib := i.isLt
        simp only [KeygenEndpoint.endpointAddress, BitVec.toNat_ofNat]
        omega
  · intro chain less
    by_cases same : chain = current
    · subst chain; exact captured
    · have prior : chain.val < current.val := by
        have ne : chain.val ≠ current.val := by intro eq; exact same (Fin.ext eq)
        omega
      intro i
      rw [frame _ (signature_outside_iteration pointer chain current valid i)
        (fun j => signature_distinct pointer chain current i j valid same)]
      exact oldSignature chain prior i

/-- Complete the remaining upper-leaf chains for the selected leaf, retaining both
endpoint and signature prefixes and counting every compression exactly. -/
theorem sign_selected_leaf_loop (hash : Hash) (s : MachineState) (secretKey : SecretKey) (pointer level tree start remaining : Nat)
    (side : Bool) (message : Reference.Digest)
    (pc : s.pc = if start = 46 then 0x18c8 else 0x1584) (length : start + remaining = 46)
    (upper : level ≠ 0) (valid : CapturePointerValid pointer)
    (data : LeafData s secretKey level tree side start) (settings : LeafSignatureSettings s pointer message)
    (endpoints : EndpointsBefore s hash secretKey level tree side start)
    (signature : SignatureBefore s hash secretKey pointer level tree side message start) :
    ∃ final instructions cycles, Trace hash sign s instructions cycles (8*remaining) (8*remaining) final ∧
      instructions ≤ 1071 * remaining ∧ cycles ≤ 1127 * remaining ∧ final.pc = 0x18c8 ∧
      LeafData final secretKey level tree side 46 ∧
      EndpointsBefore final hash secretKey level tree side 46 ∧
      SignatureBefore final hash secretKey pointer level tree side message 46 ∧
      final.getReg .x1 = s.getReg .x1 ∧ final.getReg .x2 = s.getReg .x2 ∧
      (∀ a, OutsideLeafWork a →
        (∀ chain : Reference.Chain, ∀ i : Fin 2, a ≠ wordAddress (pointer + 16 * chain.val) i.val) → final.getMem a = s.getMem a) := by
  induction remaining generalizing s start with
  | zero =>
    have eq : start = 46 := by omega
    subst start
    refine ⟨s, 0, 0, Trace.refl s, by omega, by omega, ?_, data, endpoints, signature, rfl, rfl, ?_⟩
    · simpa using pc
    · intro a _ _; rfl
  | succ remaining ih =>
    have bound : start < 46 := by omega
    let chain : Reference.Chain := ⟨start, bound⟩
    have prePC : s.pc = 0x1584 := by rw [pc, if_neg (by omega)]
    obtain ⟨next, steps, cycles, pre, stepsBound, cyclesBound, nextPC, nextData, endpoint,
      captured, nextRA, nextSP, nextFrame⟩ := sign_selected_iteration hash s secretKey pointer level tree side chain message
        prePC upper valid data (settings chain)
    have nextSettings := settings.iteration s next pointer chain message valid nextFrame
    obtain ⟨nextEndpoints, nextSignature⟩ := iteration_prefixes s next hash secretKey pointer level tree side message chain
      valid endpoints signature endpoint captured nextFrame
    obtain ⟨final, finalSteps, finalCycles, tail, finalStepsBound, finalCyclesBound, finalPC, finalData,
      finalEndpoints, finalSignature, finalRA, finalSP, finalFrame⟩ := ih next (start+1) nextPC (by omega)
        nextData nextSettings nextEndpoints nextSignature
    refine ⟨final, steps + finalSteps, cycles + finalCycles, ?_, by omega, by omega, finalPC,
      finalData, finalEndpoints, finalSignature, finalRA.trans nextRA, finalSP.trans nextSP, ?_⟩
    · convert pre.trans tail using 1 <;> omega
    · intro a outside signatureOutside
      rw [finalFrame a outside signatureOutside, nextFrame a ⟨outside.1, outside.2.1, outside.2.2 chain⟩ (signatureOutside chain)]

/-- All46selected-chain signatures and endpoints are generated by the actual signer bytecode. -/
theorem sign_selected_leaf_chains (hash : Hash) (s : MachineState) (secretKey : SecretKey) (pointer level tree : Nat)
    (side : Bool) (message : Reference.Digest) (pc : s.pc = 0x1584) (upper : level ≠ 0)
    (valid : CapturePointerValid pointer) (data : LeafData s secretKey level tree side 0)
    (settings : LeafSignatureSettings s pointer message) :
    ∃ final instructions cycles, Trace hash sign s instructions cycles 368 368 final ∧
      instructions ≤ 49266 ∧ cycles ≤ 51842 ∧ final.pc = 0x18c8 ∧
      LeafData final secretKey level tree side 46 ∧
      EndpointsBefore final hash secretKey level tree side 46 ∧
      SignatureBefore final hash secretKey pointer level tree side message 46 ∧
      final.getReg .x1 = s.getReg .x1 ∧ final.getReg .x2 = s.getReg .x2 ∧
      (∀ a, OutsideLeafWork a →
        (∀ chain : Reference.Chain, ∀ i : Fin 2, a ≠ wordAddress (pointer + 16 * chain.val) i.val) → final.getMem a = s.getMem a) :=
  sign_selected_leaf_loop hash s secretKey pointer level tree 0 46 side message pc (by decide) upper valid data settings
    (by intro chain lt; omega) (by intro chain lt; omega)

set_option format.width 200
/-- info: 'SigGolfCandidate.Hypertree.Signing.sign_selected_leaf_chains' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms sign_selected_leaf_chains

end SigGolfCandidate.Hypertree.Signing
