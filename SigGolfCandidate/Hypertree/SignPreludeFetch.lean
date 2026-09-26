import SigGolfCandidate.Hypertree.SignPreludeCode
import SigGolfCandidate.Hypertree.TraceTransport
namespace SigGolfCandidate.Hypertree.Signing
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 Keygen
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

theorem prelude_body_lookup (i : Fin 795) :
    signPrelude.code[i.val + 1]? = sign.code[i.val + 1]? := by
  have h := congrArg (fun xs : List (BitVec 32) => xs[i.val]?) prelude_body_words
  simpa [List.getElem?_take, i.isLt, List.getElem?_drop, Nat.add_comm] using h

/-- Fetch agrees throughout the retained body, including unaligned addresses. -/
theorem prelude_body_fetch (s : MachineState)
    (lower : 0x1004 ≤ s.pc.toNat) (upper : s.pc.toNat < 0x1c70) :
    fetch signPrelude s = fetch sign s := by
  have low : 1 ≤ (s.pc.toNat - 0x1000) / 4 := by omega
  have high : (s.pc.toNat - 0x1000) / 4 < 796 := by omega
  have eq := prelude_body_lookup ⟨(s.pc.toNat - 0x1000) / 4 - 1, by omega⟩
  simp only [Nat.sub_add_cancel low] at eq
  simp only [fetch, eq]

theorem prelude_transport {hash : Hash} {s t : MachineState} {n c q b : Nat}
    (run : RegionTrace (fun state => 0x1004 ≤ state.pc.toNat ∧ state.pc.toNat < 0x1c70)
      hash sign s n c q b t) : Trace hash signPrelude s n c q b t := by
  exact run.transport (fun state h => prelude_body_fetch state h.1 h.2)

/-- info: 'SigGolfCandidate.Hypertree.Signing.prelude_body_fetch' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms prelude_body_fetch
/-- info: 'SigGolfCandidate.Hypertree.Signing.prelude_transport' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms prelude_transport
end SigGolfCandidate.Hypertree.Signing
