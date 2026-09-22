import SigGolfCandidate.Hypertree.VerifyEntry
import SigGolfCandidate.Hypertree.KeygenCopyFrame
import SigGolfCandidate.TraceDeterminism

namespace SigGolfCandidate.Hypertree.Verifying
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 Keygen Signing
set_option maxRecDepth 4096

private theorem prepare_stack (s : MachineState) (pc : s.pc = 0x1024) :
    ∃ final, OrdinarySteps verify s 89 final ∧ final.getReg .x2 = s.getReg .x2 := by
  obtain ⟨pk, pkLoop, pkInv, _, _, _, pkSP⟩ := copy_all_frame verify 0x1034 (by decide)
    0x40 0x80020 2 (pkCopyState s) (pkCopyState_invariant s pc)
    (by decide) (by decide) (by decide) (by decide) (by decide)
  have pkpc : pk.pc = 0x104c := by simpa [CopyInvariant] using pkInv.2.2.1
  obtain ⟨msg, msgLoop, msgInv, _, _, _, msgSP⟩ := copy_all_frame verify 0x105c (by decide)
    0 0x80030 4 (indexMessageCopyState pk) (indexMessageCopyState_invariant pk pkpc)
    (by decide) (by decide) (by decide) (by decide) (by decide)
  have msgpc : msg.pc = 0x1074 := by simpa [CopyInvariant] using msgInv.2.2.1
  obtain ⟨rand, randLoop, randInv, _, _, _, randSP⟩ := copy_all_frame verify 0x1088 (by decide)
    0x3d3b0 0x80050 4 (inputRandomizerCopyState msg) (inputRandomizerCopyState_invariant msg msgpc)
    (by decide) (by decide) (by decide) (by decide) (by decide)
  have randpc : rand.pc = 0x10a0 := by simpa [CopyInvariant] using randInv.2.2.1
  refine ⟨indexHeaderState rand, ?_, ?_⟩
  · exact ordinary_trans verify s _ _ 16 73
      (ordinary_trans verify s _ _ 4 12 (pkCopyState_block s pc) pkLoop)
      (ordinary_trans verify pk _ _ 28 45
        (ordinary_trans verify pk _ _ 4 24 (indexMessageCopyState_block pk pkpc) msgLoop)
        (ordinary_trans verify msg _ _ 29 16
          (ordinary_trans verify msg _ _ 5 24 (inputRandomizerCopyState_block msg msgpc) randLoop)
          (indexHeaderState_block rand randpc)))
  · have header : (indexHeaderState rand).getReg .x2 = rand.getReg .x2 := by
      simp [indexHeaderState, execInstrBr, MachineState.getReg_setReg_ne]
    have rprep : (inputRandomizerCopyState msg).getReg .x2 = msg.getReg .x2 := by
      simp [inputRandomizerCopyState, execInstrBr, MachineState.getReg_setReg_ne]
    have mprep : (indexMessageCopyState pk).getReg .x2 = pk.getReg .x2 := by
      simp [indexMessageCopyState, execInstrBr, MachineState.getReg_setReg_ne]
    have pprep : (pkCopyState s).getReg .x2 = s.getReg .x2 := by
      simp [pkCopyState, execInstrBr, MachineState.getReg_setReg_ne]
    exact header.trans (randSP.trans (rprep.trans (msgSP.trans (mprep.trans (pkSP.trans pprep)))))

private theorem hash_index_stack (hash : Hash) (s : MachineState) (pc : s.pc = 0x10e0) :
    ∃ final, Trace hash verify s 32 47 1 2 final ∧ final.getReg .x2 = s.getReg .x2 := by
  let hs := indexHashState s
  have hpc : hs.pc = 0x10f8 := by simp [hs, indexHashState_pc, pc]
  obtain ⟨service, src, len, dst⟩ := indexHashState_regs s
  have hf : fetch verify hs = some (.base .ECALL) := by simp only [fetch, hpc]; decide
  have hv : hashArgumentsValid hs = true := hash_arguments hs 896 src len dst (by decide)
  have hlen : (hashInput hs).1 = 896 := by simp [hashInput, hs, len]
  let answer := hash (hashInput hs)
  let out := writeHash hs answer
  have outpc : out.pc = 0x10fc := by simp [out, hash_pc, hpc]
  obtain ⟨copied, loop, inv, _, _, _, copySP⟩ := copy_all_frame verify 0x1110 (by decide)
    0x80300 0x80408 2 (indexCopyState out) (indexCopyState_invariant out outpc)
    (by decide) (by decide) (by decide) (by decide) (by decide)
  have copypc : copied.pc = 0x1128 := by simpa [CopyInvariant] using inv.2.2.1
  have call : Trace hash verify hs 1 16 1 2 out := by
    simpa [out, hlen, compressions] using Trace.hash hs out 0 0 0 0 hf service hv (Trace.refl out)
  refine ⟨indexStoreState copied, ?_, ?_⟩
  · exact ((((indexHashState_block s pc).trace.trans call).trans
      (indexCopyState_block out outpc).trace).trans loop.trace).trans
        (indexStoreState_block copied copypc).trace
  · have store : (indexStoreState copied).getReg .x2 = copied.getReg .x2 := by
      simp [indexStoreState, execInstrBr, MachineState.getReg_setReg_ne]
    have setup : (indexCopyState out).getReg .x2 = out.getReg .x2 := by
      simp [indexCopyState, execInstrBr, MachineState.getReg_setReg_ne]
    rw [store, copySP, setup, hash_registers]
    simp [hs, indexHashState, execInstrBr, MachineState.getReg_setReg_ne]

/-- Stack preservation attaches to any proof of the actual entry trace, by interpreter determinism. -/
theorem entry_stack (hash : Hash) (s final : MachineState) (pc : s.pc = 0x1000)
    (trace : Trace hash verify s 130 145 1 2 final) : final.getReg .x2 = s.getReg .x2 := by
  have initpc : (initializeState s).pc = 0x1024 := by simp [initializeState_pc, pc]
  obtain ⟨ready, prepare, readypc, _, _⟩ := index_prepare (initializeState s) initpc
  obtain ⟨ready', prepare', prepareSP⟩ := prepare_stack (initializeState s) initpc
  have same := ordinary_deterministic prepare prepare'
  subst ready'
  obtain ⟨done, run, doneSP⟩ := hash_index_stack hash ready readypc
  have full : Trace hash verify s 130 145 1 2 done :=
    ((initializeState_block s pc).trace.trans prepare.trace).trans run
  have same := trace.deterministic full
  subst done
  rw [doneSP, prepareSP]
  simp [initializeState, execInstrBr, MachineState.getReg_setReg_ne]

/-- info: 'SigGolfCandidate.Hypertree.Verifying.entry_stack' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms entry_stack

end SigGolfCandidate.Hypertree.Verifying
