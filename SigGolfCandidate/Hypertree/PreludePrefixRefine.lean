import SigGolfCandidate.Hypertree.PreludeIndex
import SigGolfCandidate.Hypertree.SignPrefixRefine

namespace SigGolfCandidate.Hypertree.Signing.Prelude
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 OracleComp Keygen
set_option maxRecDepth 4096
theorem index_refines_full (hash : Hash) (s : MachineState) (pk : PublicKey) (message : Message) (r : Bytes 32)
    (pc : s.pc = 0x10fc)
    (hpk : ∀ i, i < 16 → s.getByte (BitVec.ofNat 64 (0x40 + i)) = pk.extractLsb' (8*i) 8)
    (hmessage : ∀ i, i < 32 → s.getByte (BitVec.ofNat 64 i) = message.extractLsb' (8*i) 8)
    (hr : ∀ i, i < 32 → s.getByte (BitVec.ofNat 64 (0x20060 + i)) = r.extractLsb' (8*i) 8) :
    ∃ final, Trace hash signPrelude s 121 136 1 2 final ∧ final.pc = 0x1220 ∧
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


theorem entry_full (hash : Hash) (s : MachineState) (secretKey : SecretKey) (pk : PublicKey) (message : Message)
    (pc : s.pc = 0x1004) (entryReady : s.getReg .x6 = 1)
    (hsecretKey : ∀ i, i < 32 → s.getByte (BitVec.ofNat 64 (0x20+i)) = secretKey.extractLsb' (8*i) 8)
    (hpk : ∀ i, i < 16 → s.getByte (BitVec.ofNat 64 (0x40+i)) = pk.extractLsb' (8*i) 8)
    (hmessage : ∀ i, i < 32 → s.getByte (BitVec.ofNat 64 i) = message.extractLsb' (8*i) 8) :
    ∃ final, Trace hash signPrelude s 237 267 2 4 final ∧ final.pc = 0x1220 ∧
      StoredIndex final ((Reference.indexOf hash pk message (Reference.randomizer hash secretKey message)).zeroExtend 192) ∧
      (∀ i : Fin 4, final.getMem (wordAddress 0x20060 i.val) =
        (Reference.randomizer hash secretKey message).extractLsb' (64*i.val) 64) ∧
      final.getMem 0x80440 = 1 ∧ final.getMem 0x80448 = 0x20080 ∧ final.getReg .x2 = s.getReg .x2 ∧
      (∀ a, OutsidePrefix a → final.getMem a = s.getMem a) := by
  obtain ⟨randomized,pre,rpc,randomWords,mode,pointer,rsp,rframe⟩ := randomizer_refines_full hash s secretKey message pc entryReady hsecretKey hmessage
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
  obtain ⟨final,run,fpc,index,fsp,frame⟩ := index_refines_full hash randomized pk message (Reference.randomizer hash secretKey message)
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

/-- info: 'SigGolfCandidate.Hypertree.Signing.Prelude.index_refines_full' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms index_refines_full

/-- info: 'SigGolfCandidate.Hypertree.Signing.Prelude.entry_full' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms entry_full

end SigGolfCandidate.Hypertree.Signing.Prelude
