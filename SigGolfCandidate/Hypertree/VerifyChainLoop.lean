import SigGolfCandidate.Hypertree.CounterLoop
namespace SigGolfCandidate.Hypertree.Verifying
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 Keygen Signing ChainLoopControl
set_option maxRecDepth 4096

/-- Any valid base-eight digit gives a universally terminating, precisely priced verifier chain fragment. -/
theorem chain_from_digit (hash : Hash) (s : MachineState) (level tree : Nat)
    (side : Bool) (chain : Reference.Chain) (digit : Fin 8) (value : Reference.Digest)
    (pc : s.pc = 0x14ec) (data : ChainData s level tree side chain digit.val value) :
    ∃ final, Trace hash verify s (13*(7-digit.val)+counterOverhead (7-digit.val)) (20*(7-digit.val)+counterOverhead (7-digit.val)) (7-digit.val) (7-digit.val) final ∧
      final.pc = 0x163c ∧
      ChainData final level tree side chain 7
        (walk (Reference.chainHash hash level tree side chain) digit.val (7-digit.val) value) ∧
      final.getReg .x1 = s.getReg .x1 ∧ final.getReg .x2 = s.getReg .x2 ∧
      (∀ a, OutsideChainWork a → final.getMem a = s.getMem a) :=
  counter_loop verify verify_chain_check verify_short_check verify_chain_code verify_cached_check verify_cached_code verify_restore_code hash s level tree digit.val (7-digit.val) side chain value pc (by have := digit.isLt; omega) data

/-- info: 'SigGolfCandidate.Hypertree.Verifying.chain_from_digit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms chain_from_digit

end SigGolfCandidate.Hypertree.Verifying
