import SigGolfCandidate.Hypertree.StepBaseFinish
import SigGolfCandidate.Hypertree.PersistentLimit
import SigGolfCandidate.Hypertree.RegisterCounter
namespace SigGolfCandidate.Hypertree.StepBaseCore
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 Keygen Signing
set_option maxRecDepth 8192

def Code (image : Image) (p : Word) : Prop :=
  instructionAt image p = some (.base .ECALL) ∧ StepBaseBlocks.FinishCode image (p+4)

theorem compute (image : Image) (hash : Hash) (p : Word) (code : Code image p)
    (s : MachineState) (pc : s.pc = p) (base : s.getReg .x28 = 0x80438)
    (constant : s.getReg .x13 = 4294967296) (current : InplaceInvariant.Current s)
    (service : s.getReg .x5 = 1) (source : s.getReg .x10 = 0x80000)
    (bits : s.getReg .x11 = 48) (destination : s.getReg .x12 = 0x80020)
    (counter : s.getReg .x6 = s.getMem 0x80438)
    (level tree step : Nat) (side : Bool) (chain : Reference.Chain) (value : Reference.Digest)
    (words : ∀ i : Fin 6, s.getMem (wordAddress 0x80000 i.val) =
      KeygenDomain.inputWord (KeygenDomain.header 2 level (Reference.sideNumber side) chain.val step) tree value i) :
    ∃ final, Trace hash image s 4 11 1 1 final ∧ final.pc = p-108 ∧
      (∀ i : Fin 2, final.getMem (wordAddress 0x80020 i.val) =
        (Reference.chainHash hash level tree side chain step value).extractLsb' (64*i.val) 64) ∧
      CachedPrepare.Ready final ∧ final.getReg .x28 = 0x80438 ∧
      final.getReg .x13 = 4294967296 ∧
      (final.getReg .x11 = 48 ∧ final.getReg .x12 = 0x80020 ∧ final.getReg .x5 = 1) ∧
      final.getMem 0x80438 = s.getMem 0x80438 + 1 ∧
      final.getReg .x6 = final.getMem 0x80438 ∧
      final.getReg .x7 = s.getReg .x7 ∧
      final.getReg .x1 = s.getReg .x1 ∧ final.getReg .x2 = s.getReg .x2 ∧
      (∀ a, (∀ i : Fin 4, a ≠ wordAddress 0x80020 i.val) → a ≠ 0x80438 →
        final.getMem a = s.getMem a) := by
  let hashed := writeHash s (hash (hashInput s))
  have fetchEq : fetch image s = some (.base .ECALL) := by simpa only [fetch_at,pc] using code.1
  have hashTrace := InplaceHash.hash_trace image hash s fetchEq service source bits destination
  have hashBase : hashed.getReg .x28 = 0x80438 := (hash_registers _ _ _).trans base
  have hashPC : hashed.pc = p+4 := by simp only [hashed,hash_pc,pc]
  have hashCounter := RegisterCounter.hash_counter s (hash (hashInput s)) destination counter
  have tail := StepBaseBlocks.finish_block image (p+4) code.2 hashed hashPC hashBase
  refine ⟨StepBaseFinish.state hashed, hashTrace.trans tail.trace, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [StepBaseFinish.pc,hashPC]
    simp [BitVec.sub_eq_add_neg,BitVec.add_assoc]
  · intro i
    rw [StepBaseFinish.mem _ hashBase hashCounter, if_neg (by fin_cases i <;> decide)]
    exact InplaceHash.answer_words hash s 2 level tree (Reference.sideNumber side) chain.val step value
      source bits destination words i
  · exact StepBaseFinish.ready hashed hashBase hashCounter (InplaceInvariant.hash_current s _ destination current)
  · exact (StepBaseFinish.reg hashed .x28 (by decide)).trans hashBase
  · exact (StepBaseFinish.reg hashed .x13 (by decide)).trans ((hash_registers _ _ _).trans constant)
  · simpa [StepBaseFinish.reg, hashed, hash_registers] using And.intro bits (And.intro destination service)
  · rw [StepBaseFinish.mem _ hashBase hashCounter,if_pos rfl]
    rw [InplaceHash.frame s _ destination _ (by intro i; fin_cases i <;> decide)]
  · exact StepBaseFinish.counter hashed hashBase
  · exact (StepBaseFinish.reg hashed .x7 (by decide)).trans (hash_registers _ _ _)
  · exact (StepBaseFinish.reg hashed .x1 (by decide)).trans (hash_registers _ _ _)
  · exact (StepBaseFinish.reg hashed .x2 (by decide)).trans (hash_registers _ _ _)
  · intro a outside notStep
    rw [StepBaseFinish.mem _ hashBase hashCounter,if_neg notStep]
    exact InplaceHash.frame s _ destination a outside

/-- info: 'SigGolfCandidate.Hypertree.StepBaseCore.compute' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms compute
end SigGolfCandidate.Hypertree.StepBaseCore
