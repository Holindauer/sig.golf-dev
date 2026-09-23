import SigGolfCandidate.Hypertree.VerifyChainControl

namespace SigGolfCandidate.Hypertree.Verifying
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 Keygen Signing ChainLoopControl
set_option maxRecDepth 4096

structure ChainData (s : MachineState) (level tree : Nat) (side : Bool) (chain : Reference.Chain)
    (step : Nat) (value : Reference.Digest) : Prop where
  levelEq : s.getMem 0x80400 = BitVec.ofNat 64 level
  leafEq : s.getMem 0x80428 = BitVec.ofNat 64 (Reference.sideNumber side)
  chainEq : s.getMem 0x80430 = BitVec.ofNat 64 chain.val
  stepEq : s.getMem 0x80438 = BitVec.ofNat 64 step
  indexEq : ∀ i : Fin 3, s.getMem (wordAddress 0x80408 i.val) = (BitVec.ofNat 192 tree).extractLsb' (64*i.val) 64
  valueEq : ∀ i : Fin 2, s.getMem (wordAddress 0x80510 i.val) = value.extractLsb' (64*i.val) 64

def OutsideChainWork (a : Word) : Prop :=
  (∀ i : Fin 8, a ≠ wordAddress 0x80000 i.val) ∧
  (∀ i : Fin 4, a ≠ wordAddress 0x80300 i.val) ∧
  (∀ i : Fin 2, a ≠ wordAddress 0x80510 i.val) ∧ a ≠ 0x80438

theorem ChainData.check (s : MachineState) (level tree : Nat) (side : Bool) (chain : Reference.Chain)
    (step : Nat) (value : Reference.Digest) (data : ChainData s level tree side chain step value) :
    ChainData (ChainLoopControl.check s) level tree side chain step value := by
  constructor
  · simpa only [check_mem] using data.levelEq
  · simpa only [check_mem] using data.leafEq
  · simpa only [check_mem] using data.chainEq
  · simpa only [check_mem] using data.stepEq
  · intro i; simpa only [check_mem] using data.indexEq i
  · intro i; simpa only [check_mem] using data.valueEq i

theorem ChainData.shortCheck (s : MachineState) (level tree : Nat) (side : Bool) (chain : Reference.Chain)
    (step : Nat) (value : Reference.Digest) (data : ChainData s level tree side chain step value) :
    ChainData (CheckReuse.shortCheck s) level tree side chain step value := by
  constructor
  · simpa only [CheckReuse.short_mem] using data.levelEq
  · simpa only [CheckReuse.short_mem] using data.leafEq
  · simpa only [CheckReuse.short_mem] using data.chainEq
  · simpa only [CheckReuse.short_mem] using data.stepEq
  · intro i; simpa only [CheckReuse.short_mem] using data.indexEq i
  · intro i; simpa only [CheckReuse.short_mem] using data.valueEq i

end SigGolfCandidate.Hypertree.Verifying
