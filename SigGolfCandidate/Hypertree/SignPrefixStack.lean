import SigGolfCandidate.Hypertree.SignPrefixFrame
import SigGolfCandidate.TraceDeterminism

namespace SigGolfCandidate.Hypertree.Signing
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 Keygen
set_option maxRecDepth 4096

theorem index_prepare_stack (s : MachineState) (pc : s.pc = 0x10fc) :
    ∃ final, OrdinarySteps sign s 89 final ∧ final.getReg .x2 = s.getReg .x2 := by
  obtain ⟨pk, pkLoop, pkInv, _, _, _, pkSP⟩ := copy_all_frame sign 0x110c (by decide)
    0x40 0x80020 2 (pkCopyState s) (pkCopyState_invariant s pc)
    (by decide) (by decide) (by decide) (by decide) (by decide)
  have pkpc : pk.pc = 0x1124 := by simpa [CopyInvariant] using pkInv.2.2.1
  obtain ⟨msg, msgLoop, msgInv, _, _, _, msgSP⟩ := copy_all_frame sign 0x1134 (by decide)
    0 0x80030 4 (indexMessageCopyState pk) (indexMessageCopyState_invariant pk pkpc)
    (by decide) (by decide) (by decide) (by decide) (by decide)
  have msgpc : msg.pc = 0x114c := by simpa [CopyInvariant] using msgInv.2.2.1
  obtain ⟨rand, randLoop, randInv, _, _, _, randSP⟩ := copy_all_frame sign 0x1160 (by decide)
    0x20060 0x80050 4 (inputRandomizerCopyState msg) (inputRandomizerCopyState_invariant msg msgpc)
    (by decide) (by decide) (by decide) (by decide) (by decide)
  have randpc : rand.pc = 0x1178 := by simpa [CopyInvariant] using randInv.2.2.1
  refine ⟨indexHeaderState rand, ?_, ?_⟩
  · exact ordinary_trans sign s _ _ 16 73
      (ordinary_trans sign s _ _ 4 12 (pkCopyState_block s pc) pkLoop)
      (ordinary_trans sign pk _ _ 28 45
        (ordinary_trans sign pk _ _ 4 24 (indexMessageCopyState_block pk pkpc) msgLoop)
        (ordinary_trans sign msg _ _ 29 16
          (ordinary_trans sign msg _ _ 5 24 (inputRandomizerCopyState_block msg msgpc) randLoop)
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


end SigGolfCandidate.Hypertree.Signing
