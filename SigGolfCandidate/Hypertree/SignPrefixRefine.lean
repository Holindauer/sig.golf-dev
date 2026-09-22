import SigGolfCandidate.Hypertree.SignPrefixRandomizer

namespace SigGolfCandidate.Hypertree.Signing
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 Keygen
set_option maxRecDepth 4096

def OutsideIndexWork (a : Word) : Prop :=
  (∀ i : Fin 14, a ≠ wordAddress 0x80000 i.val) ∧
  (∀ i : Fin 4, a ≠ wordAddress 0x80300 i.val) ∧
  (∀ i : Fin 3, a ≠ wordAddress 0x80408 i.val)

def OutsidePrefix (a : Word) : Prop :=
  OutsideIndexWork a ∧ (∀ i : Fin 4, a ≠ wordAddress 0x20060 i.val) ∧ a ≠ 0x80440 ∧ a ≠ 0x80448

theorem index_refines_full (hash : Hash) (s : MachineState) (pk : PublicKey) (message : Message) (r : Bytes 32)
    (pc : s.pc = 0x10fc)
    (hpk : ∀ i, i < 16 → s.getByte (BitVec.ofNat 64 (0x40 + i)) = pk.extractLsb' (8*i) 8)
    (hmessage : ∀ i, i < 32 → s.getByte (BitVec.ofNat 64 i) = message.extractLsb' (8*i) 8)
    (hr : ∀ i, i < 32 → s.getByte (BitVec.ofNat 64 (0x20060 + i)) = r.extractLsb' (8*i) 8) :
    ∃ final, Trace hash sign s 121 136 1 2 final ∧ final.pc = 0x1220 ∧
      StoredIndex final ((Reference.indexOf hash pk message r).zeroExtend 192) ∧
      final.getReg .x2 = s.getReg .x2 ∧
      (∀ a, OutsideIndexWork a → final.getMem a = s.getMem a) := by
  obtain ⟨ready, prepare, readypc, words, prepareFrame⟩ := index_prepare s pc
  obtain ⟨ready', prepare', readySP⟩ := index_prepare_stack s pc
  have same := ordinary_deterministic prepare prepare'
  subst ready'
  obtain ⟨final, trace, finalpc, low, high, traceFrame, finalSP⟩ := index_trace_full hash ready readypc
  have query := index_query s ready pk message r hpk hmessage hr words
  refine ⟨final,prepare.trace.trans trace,finalpc,?_,finalSP.trans readySP,?_⟩
  · have stored := stored_index_of_answer final _ low high
    rw [query] at stored
    exact stored
  · intro a outside
    exact (traceFrame a outside.2.1 outside.2.2).trans (prepareFrame a outside.1)

theorem randomizer_refines_full (hash : Hash) (s : MachineState) (seed : Seed) (message : Message)
    (pc : s.pc = 0x1000)
    (hseed : ∀ i, i < 16 → s.getByte (BitVec.ofNat 64 (0x20+i)) = seed.extractLsb' (8*i) 8)
    (hmessage : ∀ i, i < 32 → s.getByte (BitVec.ofNat 64 i) = message.extractLsb' (8*i) 8) :
    ∃ final, Trace hash sign s 105 120 1 2 final ∧ final.pc = 0x10fc ∧
      (∀ i : Fin 4, final.getMem (wordAddress 0x20060 i.val) =
        (Reference.randomizer hash seed message).extractLsb' (64*i.val) 64) ∧
      final.getMem 0x80440 = 1 ∧ final.getMem 0x80448 = 0x20080 ∧ final.getReg .x2 = s.getReg .x2 ∧
      (∀ a, (∀ i : Fin 14, a ≠ wordAddress 0x80000 i.val) →
        (∀ i : Fin 4, a ≠ wordAddress 0x80300 i.val) →
        (∀ i : Fin 4, a ≠ wordAddress 0x20060 i.val) →
        a ≠ 0x80440 → a ≠ 0x80448 → final.getMem a = s.getMem a) := by
  obtain ⟨ready,prepare,rpc,words,prepareFrame,mode,pointer,readySP⟩ := randomizer_prepare_full s pc
  obtain ⟨final,run,fpc,output,frame,finalSP⟩ := randomizer_trace_full hash ready rpc
  have query := randomizer_query s ready seed message hseed hmessage words
  refine ⟨final,prepare.trace.trans run,fpc,?_,?_,?_,finalSP.trans readySP,?_⟩
  · intro i; rw [output i,query]; rfl
  · rw [frame _ (by intro i; fin_cases i <;> decide) (by intro i; fin_cases i <;> decide)]; exact mode
  · rw [frame _ (by intro i; fin_cases i <;> decide) (by intro i; fin_cases i <;> decide)]; exact pointer
  · intro a inputOutside answerOutside sigOutside modeOutside pointerOutside
    rw [frame a sigOutside answerOutside]
    exact prepareFrame a modeOutside pointerOutside (fun i => inputOutside ⟨i.val,by have := i.isLt; omega⟩)

theorem outside_prefix_low (a : Word) (low : a.toNat < 0x20060) : OutsidePrefix a := by
  have outside (base n : Nat) (lower : 0x20060 ≤ base) (upper : base+8*n < 2^64) (i : Fin n) :
      a ≠ wordAddress base i.val := by
    intro eq
    have h := congrArg BitVec.toNat eq
    have hi := i.isLt
    change a.toNat = (base+8*i.val)%2^64 at h
    omega
  refine ⟨⟨outside _ _ (by decide) (by decide),outside _ _ (by decide) (by decide),
    outside _ _ (by decide) (by decide)⟩,outside _ _ (by decide) (by decide),?_,?_⟩
  · exact outside 0x80440 1 (by decide) (by decide) 0
  · exact outside 0x80448 1 (by decide) (by decide) 0

/-- Full arbitrary-state signer prefix refinement, including persistent memory and stack. -/
theorem entry_full (hash : Hash) (s : MachineState) (seed : Seed) (pk : PublicKey) (message : Message)
    (pc : s.pc = 0x1000)
    (hseed : ∀ i, i < 16 → s.getByte (BitVec.ofNat 64 (0x20+i)) = seed.extractLsb' (8*i) 8)
    (hpk : ∀ i, i < 16 → s.getByte (BitVec.ofNat 64 (0x40+i)) = pk.extractLsb' (8*i) 8)
    (hmessage : ∀ i, i < 32 → s.getByte (BitVec.ofNat 64 i) = message.extractLsb' (8*i) 8) :
    ∃ final, Trace hash sign s 226 256 2 4 final ∧ final.pc = 0x1220 ∧
      StoredIndex final ((Reference.indexOf hash pk message (Reference.randomizer hash seed message)).zeroExtend 192) ∧
      (∀ i : Fin 4, final.getMem (wordAddress 0x20060 i.val) =
        (Reference.randomizer hash seed message).extractLsb' (64*i.val) 64) ∧
      final.getMem 0x80440 = 1 ∧ final.getMem 0x80448 = 0x20080 ∧ final.getReg .x2 = s.getReg .x2 ∧
      (∀ a, OutsidePrefix a → final.getMem a = s.getMem a) := by
  obtain ⟨randomized,pre,rpc,randomWords,mode,pointer,rsp,rframe⟩ := randomizer_refines_full hash s seed message pc hseed hmessage
  have lowFrame (a : Word) (low : a.toNat < 0x20060) : randomized.getMem a = s.getMem a := by
    have outside := outside_prefix_low a low
    exact rframe a outside.1.1 outside.1.2.1 outside.2.1 outside.2.2.1 outside.2.2.2
  have pkBytes : ∀ i, i < 16 → randomized.getByte (BitVec.ofNat 64 (0x40+i)) = pk.extractLsb' (8*i) 8 := by
    intro i hi
    rw [low_words_byte s randomized lowFrame 0x40 i (by decide) (by omega)]; exact hpk i hi
  have msgBytes : ∀ i, i < 32 → randomized.getByte (BitVec.ofNat 64 i) = message.extractLsb' (8*i) 8 := by
    intro i hi
    have eq := low_words_byte s randomized lowFrame 0 i (by decide) (by omega)
    simp only [Nat.zero_add] at eq
    rw [eq]; exact hmessage i hi
  obtain ⟨final,run,fpc,index,fsp,frame⟩ := index_refines_full hash randomized pk message (Reference.randomizer hash seed message)
    rpc pkBytes msgBytes (bytes_of_answer_words randomized 0x20060 _ (by decide) (by decide) randomWords)
  refine ⟨final,pre.trans run,fpc,index,?_,?_,?_,fsp.trans rsp,?_⟩
  · intro i
    rw [frame _ (by unfold OutsideIndexWork; fin_cases i <;> decide)]
    exact randomWords i
  · rw [frame _ (by unfold OutsideIndexWork; decide)]; exact mode
  · rw [frame _ (by unfold OutsideIndexWork; decide)]; exact pointer
  · intro a outside
    rw [frame a outside.1]
    exact rframe a outside.1.1 outside.1.2.1 outside.2.1 outside.2.2.1 outside.2.2.2

end SigGolfCandidate.Hypertree.Signing
