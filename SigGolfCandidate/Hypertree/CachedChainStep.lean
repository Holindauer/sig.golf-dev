import SigGolfCandidate.Hypertree.VerifyChainStep
import SigGolfCandidate.Hypertree.InitialCachedChain
import SigGolfCandidate.Hypertree.CachedChain
namespace SigGolfCandidate.Hypertree.Verifying
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 Keygen Signing ChainLoopControl
set_option maxRecDepth 8192
theorem ChainData.cachedCheck (s : MachineState) (level tree : Nat) (side : Bool) (chain : Reference.Chain)
    (step : Nat) (value : Reference.Digest) (data : ChainData s level tree side chain step value) :
    ChainData (CachedCheck.shortCheck s) level tree side chain step value := by
  constructor
  · simpa only [CachedCheck.short_mem] using data.levelEq
  · simpa only [CachedCheck.short_mem] using data.leafEq
  · simpa only [CachedCheck.short_mem] using data.chainEq
  · simpa only [CachedCheck.short_mem] using data.stepEq
  · intro i; simpa only [CachedCheck.short_mem] using data.indexEq i
  · intro i; simpa only [CachedCheck.short_mem] using data.valueEq i

theorem initial_cached_step (image : Image)
    (checkCode : CheckReuse.Code image 0x14f4)
    (chainCode : InitialCachedChain.ChainCode image 0x1500) (hash : Hash) (s : MachineState) (level tree step : Nat)
    (side : Bool) (chain : Reference.Chain) (value : Reference.Digest)
    (pc : s.pc = 0x14f4) (base : s.getReg .x28 = 0x80438) (bound : step < 7) (data : ChainData s level tree side chain step value) :
    ∃ final, Trace hash image s 43 50 1 1 final ∧ final.pc = 0x1578 ∧
      ChainData final level tree side chain (step+1) (Reference.chainHash hash level tree side chain step value) ∧
      final.getReg .x28 = 0x80438 ∧ final.getReg .x1 = s.getReg .x1 ∧ final.getReg .x2 = s.getReg .x2 ∧
      (∀ a, OutsideChainWork a → final.getMem a = s.getMem a) ∧ CachedPrepare.Ready final := by
  have ne : s.getMem 0x80438 ≠ 7 := by
    rw [data.stepEq]
    intro eq
    have h := congrArg BitVec.toNat eq
    change step % 2^64 = 7 at h
    omega
  have checkedPC : (CheckReuse.shortCheck s).pc = 0x1500 := by rw [CheckReuse.short_pc s base, pc, if_neg ne]; rfl
  have checked := data.shortCheck
  obtain ⟨hashed, core, hashedPC, valueOut, ra, sp, frame, nextReady⟩ := InitialCachedChain.chain_compute image hash 0x1500 chainCode
    (CheckReuse.shortCheck s) checkedPC (by rw [CheckReuse.short_base]; exact base) level tree step side chain value checked.levelEq checked.leafEq checked.chainEq
    checked.stepEq checked.indexEq checked.valueEq
  have hashedPC' : hashed.pc = 0x161c := hashedPC
  have keep (a : Word)
      (hi : ∀ i : Fin 6, a ≠ wordAddress 0x80000 i.val)
      (ha : ∀ i : Fin 4, a ≠ wordAddress 0x80300 i.val)
      (hv : ∀ i : Fin 2, a ≠ wordAddress 0x80510 i.val) : hashed.getMem a = s.getMem a := by
    rw [frame a hi ha hv, CheckReuse.short_mem]
  have nextLevel : hashed.getMem 0x80400 = s.getMem 0x80400 := keep _ (by decide) (by decide) (by decide)
  have nextLeaf : hashed.getMem 0x80428 = s.getMem 0x80428 := keep _ (by decide) (by decide) (by decide)
  have nextChain : hashed.getMem 0x80430 = s.getMem 0x80430 := keep _ (by decide) (by decide) (by decide)
  have nextStep : hashed.getMem 0x80438 = s.getMem 0x80438 := keep _ (by decide) (by decide) (by decide)
  refine ⟨increment hashed (-192), ?_, ?_, ?_, CheckReuse.increment_base _ _, ?_, ?_, ?_, nextReady⟩
  · exact (CheckReuse.block image 0x14f4 checkCode s pc base).trace.trans core
  · rw [increment_pc, hashedPC']; rfl
  · constructor
    · rw [increment_mem, if_neg (by decide), nextLevel]; exact data.levelEq
    · rw [increment_mem, if_neg (by decide), nextLeaf]; exact data.leafEq
    · rw [increment_mem, if_neg (by decide), nextChain]; exact data.chainEq
    · rw [increment_mem, if_pos rfl, nextStep, data.stepEq, BitVec.ofNat_add]; rfl
    · intro i
      rw [increment_mem, if_neg (by fin_cases i <;> decide), keep]
      · exact data.indexEq i
      · intro j; fin_cases i <;> fin_cases j <;> decide
      · intro j; fin_cases i <;> fin_cases j <;> decide
      · intro j; fin_cases i <;> fin_cases j <;> decide
    · intro i
      rw [increment_mem, if_neg (by fin_cases i <;> decide)]
      exact valueOut i
  · exact (increment_stack hashed (-192)).1.trans (ra.trans (CheckReuse.short_stack s).1)
  · exact (increment_stack hashed (-192)).2.trans (sp.trans (CheckReuse.short_stack s).2)
  · intro a outside
    rw [increment_mem, if_neg outside.2.2.2, keep a (fun i => outside.1 ⟨i.val, by omega⟩) outside.2.1 outside.2.2.1]

/-- info: 'SigGolfCandidate.Hypertree.Verifying.initial_cached_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms initial_cached_step
theorem recurrent_cached_step (image : Image)
    (checkCode : CachedCheck.Code image 0x1578)
    (chainCode : CachedChain.ChainCode image 0x1584) (hash : Hash) (s : MachineState) (level tree step : Nat)
    (side : Bool) (chain : Reference.Chain) (value : Reference.Digest)
    (pc : s.pc = 0x1578) (base : s.getReg .x28 = 0x80438) (ready : CachedPrepare.Ready s) (bound : step < 7) (data : ChainData s level tree side chain step value) :
    ∃ final, Trace hash image s 28 35 1 1 final ∧ final.pc = 0x1578 ∧
      ChainData final level tree side chain (step+1) (Reference.chainHash hash level tree side chain step value) ∧
      final.getReg .x28 = 0x80438 ∧ final.getReg .x1 = s.getReg .x1 ∧ final.getReg .x2 = s.getReg .x2 ∧
      (∀ a, OutsideChainWork a → final.getMem a = s.getMem a) ∧ CachedPrepare.Ready final := by
  have ne : s.getMem 0x80438 ≠ 7 := by
    rw [data.stepEq]
    intro eq
    have h := congrArg BitVec.toNat eq
    change step % 2^64 = 7 at h
    omega
  have checkedPC : (CachedCheck.shortCheck s).pc = 0x1584 := by rw [CachedCheck.short_pc s base, pc, if_neg ne]; rfl
  have checked := data.cachedCheck
  obtain ⟨hashed, core, hashedPC, valueOut, ra, sp, frame, nextReady⟩ := CachedChain.chain_compute image hash 0x1584 chainCode
    (CachedCheck.shortCheck s) checkedPC (by rw [CachedCheck.short_base]; exact base) (CachedInvariant.check_ready s ready) level tree step side chain value checked.levelEq checked.leafEq checked.chainEq
    checked.stepEq checked.indexEq checked.valueEq
  have hashedPC' : hashed.pc = 0x161c := hashedPC
  have keep (a : Word)
      (hi : ∀ i : Fin 6, a ≠ wordAddress 0x80000 i.val)
      (ha : ∀ i : Fin 4, a ≠ wordAddress 0x80300 i.val)
      (hv : ∀ i : Fin 2, a ≠ wordAddress 0x80510 i.val) : hashed.getMem a = s.getMem a := by
    rw [frame a hi ha hv, CachedCheck.short_mem]
  have nextLevel : hashed.getMem 0x80400 = s.getMem 0x80400 := keep _ (by decide) (by decide) (by decide)
  have nextLeaf : hashed.getMem 0x80428 = s.getMem 0x80428 := keep _ (by decide) (by decide) (by decide)
  have nextChain : hashed.getMem 0x80430 = s.getMem 0x80430 := keep _ (by decide) (by decide) (by decide)
  have nextStep : hashed.getMem 0x80438 = s.getMem 0x80438 := keep _ (by decide) (by decide) (by decide)
  refine ⟨increment hashed (-192), ?_, ?_, ?_, CheckReuse.increment_base _ _, ?_, ?_, ?_, nextReady⟩
  · exact (CachedCheck.block image 0x1578 checkCode s pc base).trace.trans core
  · rw [increment_pc, hashedPC']; rfl
  · constructor
    · rw [increment_mem, if_neg (by decide), nextLevel]; exact data.levelEq
    · rw [increment_mem, if_neg (by decide), nextLeaf]; exact data.leafEq
    · rw [increment_mem, if_neg (by decide), nextChain]; exact data.chainEq
    · rw [increment_mem, if_pos rfl, nextStep, data.stepEq, BitVec.ofNat_add]; rfl
    · intro i
      rw [increment_mem, if_neg (by fin_cases i <;> decide), keep]
      · exact data.indexEq i
      · intro j; fin_cases i <;> fin_cases j <;> decide
      · intro j; fin_cases i <;> fin_cases j <;> decide
      · intro j; fin_cases i <;> fin_cases j <;> decide
    · intro i
      rw [increment_mem, if_neg (by fin_cases i <;> decide)]
      exact valueOut i
  · exact (increment_stack hashed (-192)).1.trans (ra.trans (CachedCheck.short_stack s).1)
  · exact (increment_stack hashed (-192)).2.trans (sp.trans (CachedCheck.short_stack s).2)
  · intro a outside
    rw [increment_mem, if_neg outside.2.2.2, keep a (fun i => outside.1 ⟨i.val, by omega⟩) outside.2.1 outside.2.2.1]

/-- info: 'SigGolfCandidate.Hypertree.Verifying.recurrent_cached_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms recurrent_cached_step
end SigGolfCandidate.Hypertree.Verifying
