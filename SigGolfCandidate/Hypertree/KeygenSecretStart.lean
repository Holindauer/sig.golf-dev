import SigGolfCandidate.Hypertree.KeygenSecretExecution
import SigGolfCandidate.Hypertree.KeygenStepZero
import SigGolfCandidate.Hypertree.KeygenChainLoop

namespace SigGolfCandidate.Hypertree.KeygenSecretStart
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 OracleComp Keygen
set_option maxRecDepth 4096

/-- Static inputs preserved throughout the upper-leaf chain generation loop. -/
structure Context (level tree : Nat) (side : Bool) (secretKey : SecretKey) (s : MachineState) : Prop where
  levelWord : s.getMem 0x80400 = BitVec.ofNat 64 level
  leafWord : s.getMem 0x80428 = BitVec.ofNat 64 (Reference.sideNumber side)
  indexWords : ∀ i : Fin 3, s.getMem (Signing.wordAddress 0x80408 i.val) =
    (BitVec.ofNat 192 tree).extractLsb' (64*i.val) 64
  secretKeyWords : ∀ i : Fin 4, s.getMem (Signing.wordAddress 0x20 i.val) = secretKey.extractLsb' (64*i.val) 64
  modeWord : s.getMem 0x80440 = 0

/-- Secret derivation followed by STEP=0 establishes the complete chain-loop invariant. -/
theorem prepare (hash : Hash) (s : MachineState) (pc : s.pc=0x1204)
    (level tree : Nat) (side : Bool) (chain : Reference.Chain) (secretKey : SecretKey)
    (context : Context level tree side secretKey s)
    (counter : s.getMem 0x80430 = BitVec.ofNat 64 chain.val) :
    ∃ final, Trace hash keygen s 93 100 1 1 final ∧ final.pc=0x1318 ∧
      KeygenChainLoop.Invariant level tree 0 side chain (Reference.secret hash secretKey level tree side chain) final ∧
      final.getReg .x1=s.getReg .x1 ∧ final.getReg .x2=s.getReg .x2 ∧
      (∀ a, KeygenChainLoop.Outside a → final.getMem a=s.getMem a) := by
  obtain ⟨secret,trace,spc,words,ra,sp,frame⟩ :=
    KeygenSecret.compute keygen hash 0x1204 KeygenSecret.keygen_code s pc level tree side chain secretKey
      context.levelWord context.leafWord counter context.indexWords context.secretKeyWords
  have reset := KeygenStepZero.block keygen 0x1308 KeygenStepZero.keygen_code secret spc
  have finalFrame (a : Word) (outside : KeygenChainLoop.Outside a) :
      (KeygenStepZero.state secret).getMem a=s.getMem a := by
    rw [KeygenStepZero.mem,if_neg outside.1,frame a outside.2.1 outside.2.2.1 outside.2.2.2]
  refine ⟨KeygenStepZero.state secret,trace.trans reset.trace,?_,?_,
    (KeygenStepZero.stack secret).1.trans ra,(KeygenStepZero.stack secret).2.trans sp,finalFrame⟩
  · rw [KeygenStepZero.pc,spc]; rfl
  · constructor
    · rw [finalFrame _ (by decide)]; exact context.levelWord
    · rw [finalFrame _ (by decide)]; exact context.leafWord
    · rw [finalFrame _ (by decide)]; exact counter
    · rw [KeygenStepZero.mem,if_pos rfl]; rfl
    · intro i
      rw [finalFrame _ (by fin_cases i <;> decide)]
      exact context.indexWords i
    · intro i
      rw [KeygenStepZero.mem,if_neg (by fin_cases i <;> decide)]
      exact words i
    · rw [finalFrame _ (by decide)]; exact context.modeWord

end SigGolfCandidate.Hypertree.KeygenSecretStart
