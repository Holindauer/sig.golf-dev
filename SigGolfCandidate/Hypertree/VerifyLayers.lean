import SigGolfCandidate.Hypertree.VerifyLayerStep

namespace SigGolfCandidate.Hypertree.Verifying
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 Keygen Signing
set_option maxRecDepth 4096

def wireLayers (witness : Bytes signatureBytes) : Nat → Nat → List Reference.LayerSignature
  | 0, _ => []
  | count+1, level => wireLayer witness level :: wireLayers witness count (level+1)

/-- All remaining verifier layers execute and recover the decoded reference path. -/
theorem verify_layers (hash : Hash) (witness : Bytes signatureBytes) (count level index : Nat)
    (s : MachineState) (current : Reference.Digest)
    (remaining : level+count = 160) (indexSmall : index < 2^192)
    (pc : s.pc = if count = 0 then 0x1220 else 0x1148)
    (data : LoopData s level index current witness) :
    ∃ final steps cycles calls blocks lastIndex, Trace hash verify s steps cycles calls blocks final ∧
      steps ≤ 34415*count ∧ cycles ≤ 36771*count ∧ calls ≤ 324*count ∧ blocks ≤ 335*count ∧
      final.pc = 0x1220 ∧
      LoopData final 160 lastIndex (Reference.recoverLayers hash level index current (wireLayers witness count level)) witness ∧
      LowFrame s final := by
  induction count generalizing level index s current with
  | zero =>
    have levelEq : level = 160 := by omega
    subst level
    exact ⟨s, 0, 0, 0, 0, index, Trace.refl _, by decide, by decide, by decide, by decide, by simpa using pc, data,
      fun _ _ _ => rfl⟩
  | succ count ih =>
    have small : level < 160 := by omega
    obtain ⟨next, steps, cycles, calls, blocks, run, hsteps, hcycles, hcalls, hblocks, nextPC, nextData, frame⟩ :=
      verify_layer hash s level index current witness (by simpa using pc) small indexSmall data
    have nextPC' : next.pc = if count = 0 then 0x1220 else 0x1148 := by
      have eq : level+1 = 160 ↔ count = 0 := by omega
      simpa only [eq] using nextPC
    obtain ⟨final, tailSteps, tailCycles, tailCalls, tailBlocks, lastIndex, tailRun, tsteps, tcycles, tcalls, tblocks,
      finalPC, finalData, tailFrame⟩ := ih (level+1) (index/2) next
        (Reference.recoverLayer hash level (index/2) (index%2 == 1) current (wireLayer witness level))
        (by omega) (by omega) nextPC' nextData
    refine ⟨final, steps+tailSteps, cycles+tailCycles, calls+tailCalls, blocks+tailBlocks, lastIndex,
      run.trans tailRun, ?_, ?_, ?_, ?_, finalPC, finalData, frame.trans s next final tailFrame⟩
    all_goals omega

/-- info: 'SigGolfCandidate.Hypertree.Verifying.verify_layers' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms verify_layers

end SigGolfCandidate.Hypertree.Verifying
