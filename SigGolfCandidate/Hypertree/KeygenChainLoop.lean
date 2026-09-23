import SigGolfCandidate.Hypertree.ChainLoopControl
import SigGolfCandidate.Hypertree.SignCapture

namespace SigGolfCandidate.Hypertree.KeygenChainLoop
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 OracleComp Keygen ChainLoopControl
set_option maxRecDepth 4096

structure Invariant (level tree step : Nat) (side : Bool) (chain : Reference.Chain)
    (value : Reference.Digest) (s : MachineState) : Prop where
  levelWord : s.getMem 0x80400 = BitVec.ofNat 64 level
  leafWord : s.getMem 0x80428 = BitVec.ofNat 64 (Reference.sideNumber side)
  chainWord : s.getMem 0x80430 = BitVec.ofNat 64 chain.val
  stepWord : s.getMem 0x80438 = BitVec.ofNat 64 step
  indexWords : ∀ i : Fin 3, s.getMem (Signing.wordAddress 0x80408 i.val) =
    (BitVec.ofNat 192 tree).extractLsb' (64*i.val) 64
  valueWords : ∀ i : Fin 2, s.getMem (Signing.wordAddress 0x80510 i.val) = value.extractLsb' (64*i.val) 64
  modeWord : s.getMem 0x80440 = 0

theorem Invariant.of_mem_eq {level tree step : Nat} {side : Bool} {chain : Reference.Chain}
    {value : Reference.Digest} {s t : MachineState} (h : Invariant level tree step side chain value s)
    (eq : ∀ a, t.getMem a = s.getMem a) : Invariant level tree step side chain value t := by
  constructor
  · rw [eq]; exact h.levelWord
  · rw [eq]; exact h.leafWord
  · rw [eq]; exact h.chainWord
  · rw [eq]; exact h.stepWord
  · intro i; rw [eq]; exact h.indexWords i
  · intro i; rw [eq]; exact h.valueWords i
  · rw [eq]; exact h.modeWord

/-- Addresses outside every word modified by a keygen chain loop. -/
def Outside (a : Word) : Prop :=
  a ≠ 0x80438 ∧ (∀ i : Fin 8, a ≠ Signing.wordAddress 0x80000 i.val) ∧
    (∀ i : Fin 4, a ≠ Signing.wordAddress 0x80300 i.val) ∧
    (∀ i : Fin 2, a ≠ Signing.wordAddress 0x80510 i.val)

instance (a : Word) : Decidable (Outside a) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

theorem check_code : CheckCode keygen 0x13a4 := by decide

theorem increment_code : IncrementCode keygen 0x14d4 (-472) := by decide

def guarded (s : MachineState) : MachineState := check (Signing.captureModeState 128 s)

theorem guard (s : MachineState) (pc : s.pc = 0x1318) (mode : s.getMem 0x80440 = 0) :
    OrdinarySteps keygen s 9 (guarded s) ∧
      (guarded s).pc = (if s.getMem 0x80438 = 7 then 0x14f4 else 0x13b8) ∧
      (∀ a, (guarded s).getMem a = s.getMem a) ∧
      (guarded s).getReg .x1 = s.getReg .x1 ∧ (guarded s).getReg .x2 = s.getReg .x2 := by
  have skip := Signing.captureMode_block keygen 0x1318 128 Signing.keygen_upper_mode_code s pc
  have skipPC : (Signing.captureModeState 128 s).pc = 0x13a4 := by
    rw [Signing.captureMode_pc,if_pos mode,pc]; decide
  have next := check_block keygen 0x13a4 check_code _ skipPC
  refine ⟨ordinary_trans keygen _ _ _ 4 5 skip next,?_,?_,?_,?_⟩
  · simp only [guarded,check_pc,skipPC,Signing.captureMode_mem]
    split <;> decide
  · intro a; rw [guarded,check_mem,Signing.captureMode_mem]
  · rw [guarded,(check_stack _).1]
    simp [Signing.captureModeState,execInstrBr,MachineState.getReg_setReg_ne]
  · rw [guarded,(check_stack _).2,Signing.captureMode_sp]

/-- A nonterminal iteration performs one position-tweaked chain hash. -/
theorem step (hash : Hash) (s : MachineState) (pc : s.pc = 0x1318)
    (level tree n : Nat) (side : Bool) (chain : Reference.Chain) (value : Reference.Digest)
    (bound : n < 7) (inv : Invariant level tree n side chain value s) :
    ∃ final, Trace hash keygen s 100 107 1 1 final ∧ final.pc = 0x1318 ∧
      Invariant level tree (n+1) side chain (Reference.chainHash hash level tree side chain n value) final ∧
      final.getReg .x1 = s.getReg .x1 ∧ final.getReg .x2 = s.getReg .x2 ∧
      (∀ a, Outside a → final.getMem a = s.getMem a) := by
  obtain ⟨pre,gpc,gmem,gra,gsp⟩ := guard s pc inv.modeWord
  have distinct : s.getMem 0x80438 ≠ 7 := by
    rw [inv.stepWord]
    intro eq
    have natEq := congrArg BitVec.toNat eq
    change n % 18446744073709551616 = 7 at natEq
    omega
  rw [if_neg distinct] at gpc
  have gi := inv.of_mem_eq gmem
  obtain ⟨hashed,ht,hpc,words,ra,sp,frame⟩ :=
    KeygenChain.compute keygen hash 0x13b8 KeygenChain.keygen_code (guarded s) gpc
      level tree n side chain value gi.levelWord gi.leafWord gi.chainWord gi.stepWord gi.indexWords gi.valueWords
  have inc := increment_block keygen 0x14d4 (-472) increment_code hashed hpc
  have metadata (a : Word) (outside : Outside a) : hashed.getMem a = s.getMem a := by
    rw [frame a (fun i : Fin 6 => outside.2.1 ⟨i.val, by omega⟩) outside.2.2.1 outside.2.2.2,gmem]
  have stepMem : hashed.getMem 0x80438 = BitVec.ofNat 64 n := by
    rw [frame _ (by intro i; fin_cases i <;> decide) (by intro i; fin_cases i <;> decide)
      (by intro i; fin_cases i <;> decide),gmem]
    exact inv.stepWord
  refine ⟨increment hashed (-472),pre.trace.trans (ht.trans inc.trace),?_,?_,
    (increment_stack _ _).1.trans (ra.trans gra),(increment_stack _ _).2.trans (sp.trans gsp),?_⟩
  · rw [increment_pc,hpc]; decide
  · constructor
    · rw [increment_mem]; simp only [show (0x80400:Word) ≠ 0x80438 by decide,↓reduceIte]
      rw [metadata _ (by decide)]; exact inv.levelWord
    · rw [increment_mem]; simp only [show (0x80428:Word) ≠ 0x80438 by decide,↓reduceIte]
      rw [metadata _ (by decide)]; exact inv.leafWord
    · rw [increment_mem]; simp only [show (0x80430:Word) ≠ 0x80438 by decide,↓reduceIte]
      rw [metadata _ (by decide)]; exact inv.chainWord
    · rw [increment_mem,if_pos rfl,stepMem]
      exact (BitVec.ofNat_add n 1).symm
    · intro i
      have outside : Outside (Signing.wordAddress 0x80408 i.val) := by fin_cases i <;> decide
      rw [increment_mem,if_neg outside.1,metadata _ outside]
      exact inv.indexWords i
    · intro i
      have ne : Signing.wordAddress 0x80510 i.val ≠ (0x80438:Word) := by fin_cases i <;> decide
      rw [increment_mem,if_neg ne]
      exact words i
    · rw [increment_mem]; simp only [show (0x80440:Word) ≠ 0x80438 by decide,↓reduceIte]
      rw [metadata _ (by decide)]; exact inv.modeWord
  · intro a outside
    rw [increment_mem,if_neg outside.1,metadata a outside]

/-- All remaining keygen chain rounds, including the final loop-exit guard. -/
theorem run (hash : Hash) (count : Nat) (s : MachineState) (pc : s.pc = 0x1318)
    (level tree start : Nat) (side : Bool) (chain : Reference.Chain) (value : Reference.Digest)
    (bound : start + count = 7) (inv : Invariant level tree start side chain value s) :
    ∃ final, Trace hash keygen s (100*count+9) (107*count+9) count count final ∧
      final.pc = 0x14f4 ∧
      Invariant level tree 7 side chain (walk (Reference.chainHash hash level tree side chain) start count value) final ∧
      final.getReg .x1 = s.getReg .x1 ∧ final.getReg .x2 = s.getReg .x2 ∧
      (∀ a, Outside a → final.getMem a = s.getMem a) := by
  induction count generalizing s start value with
  | zero =>
    have startEq : start = 7 := by omega
    subst start
    obtain ⟨trace,gpc,gmem,ra,sp⟩ := guard s pc inv.modeWord
    refine ⟨guarded s,trace.trace,?_,?_,ra,sp,fun a _ => gmem a⟩
    · have eq : s.getMem 0x80438 = 7 := inv.stepWord
      rw [if_pos eq] at gpc
      exact gpc
    · exact inv.of_mem_eq gmem
  | succ count ih =>
    obtain ⟨next,trace,nextPC,nextInv,ra,sp,frame⟩ :=
      step hash s pc level tree start side chain value (by omega) inv
    obtain ⟨final,tail,finalPC,finalInv,finalRA,finalSP,finalFrame⟩ :=
      ih next nextPC (start+1) (Reference.chainHash hash level tree side chain start value)
        (by omega) nextInv
    refine ⟨final,?_,finalPC,finalInv,finalRA.trans ra,finalSP.trans sp,?_⟩
    · simpa [Nat.mul_add,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using trace.trans tail
    · intro a outside
      rw [finalFrame a outside,frame a outside]

/-- info: 'SigGolfCandidate.Hypertree.KeygenChainLoop.run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms run

end SigGolfCandidate.Hypertree.KeygenChainLoop
