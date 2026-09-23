import SigGolfCandidate.Hypertree.VerifyIndexFrame

namespace SigGolfCandidate.Hypertree.Verifying
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 Keygen Signing
set_option maxRecDepth 4096

/-- Memory words untouched by the randomized-index prefix. -/
def OutsideIndexPrefix (a : Word) : Prop :=
  (∀ i : Fin 14, a ≠ wordAddress 0x80000 i.val) ∧
  (∀ i : Fin 4, a ≠ wordAddress 0x80300 i.val) ∧
  (∀ i : Fin 3, a ≠ wordAddress 0x80408 i.val)

/-- The index prefix also preserves the rest of memory, including the witness and loop bookkeeping. -/
theorem index_refines_frame (hash : Hash) (s : MachineState) (pk : PublicKey) (message : Message) (r : Bytes 32)
    (pc : s.pc = 0x1024)
    (hpk : ∀ i, i < 16 → s.getByte (BitVec.ofNat 64 (0x40 + i)) = pk.extractLsb' (8 * i) 8)
    (hmessage : ∀ i, i < 32 → s.getByte (BitVec.ofNat 64 i) = message.extractLsb' (8 * i) 8)
    (hr : ∀ i, i < 32 → s.getByte (BitVec.ofNat 64 (0x3bc30 + i)) = r.extractLsb' (8 * i) 8) :
    ∃ final, Trace hash verify s 121 136 1 2 final ∧ final.pc = 0x1148 ∧
      StoredIndex final ((Reference.indexOf hash pk message r).zeroExtend 192) ∧
      (∀ a, OutsideIndexPrefix a → final.getMem a = s.getMem a) := by
  obtain ⟨ready, prepare, readypc, words, prepareFrame⟩ := index_prepare s pc
  obtain ⟨final, trace, finalpc, low, high, traceFrame⟩ := index_trace_frame hash ready readypc
  have query := index_query s ready pk message r hpk hmessage hr words
  refine ⟨final, prepare.trace.trans trace, finalpc, ?_, ?_⟩
  · have stored := stored_index_of_answer final _ low high
    rw [query] at stored
    exact stored
  · intro a outside
    exact (traceFrame a outside.2.1 outside.2.2).trans (prepareFrame a outside.1)

/-- The real verifier enters its loop with the decoded index, correct witness cursor, and read-only input memory intact. -/
theorem entry_index_frame (hash : Hash) (s : MachineState) (pk : PublicKey) (message : Message) (r : Bytes 32)
    (pc : s.pc = 0x1000)
    (hpk : ∀ i, i < 16 → s.getByte (BitVec.ofNat 64 (0x40 + i)) = pk.extractLsb' (8 * i) 8)
    (hmessage : ∀ i, i < 32 → s.getByte (BitVec.ofNat 64 i) = message.extractLsb' (8 * i) 8)
    (hr : ∀ i, i < 32 → s.getByte (BitVec.ofNat 64 (0x3bc30 + i)) = r.extractLsb' (8 * i) 8) :
    ∃ final, Trace hash verify s 130 145 1 2 final ∧ final.pc = 0x1148 ∧
      StoredIndex final ((Reference.indexOf hash pk message r).zeroExtend 192) ∧
      final.getMem 0x80440 = 0 ∧ final.getMem 0x80448 = 0x3bc50 ∧
      (∀ a, OutsideIndexPrefix a → a ≠ 0x80440 → a ≠ 0x80448 → final.getMem a = s.getMem a) := by
  have initpc : (initializeState s).pc = 0x1024 := by simp [initializeState_pc, pc]
  obtain ⟨final, trace, finalpc, index, frame⟩ := index_refines_frame hash (initializeState s) pk message r initpc
    (fun i hi => (initializeState_byte s 0x40 i (by decide) (by omega)).trans (hpk i hi))
    (fun i hi => (by simpa only [Nat.zero_add] using initializeState_byte s 0 i (by decide) (by omega) :
      (initializeState s).getByte (BitVec.ofNat 64 i) = s.getByte (BitVec.ofNat 64 i)).trans (hmessage i hi))
    (fun i hi => (initializeState_byte s 0x3bc30 i (by decide) (by omega)).trans (hr i hi))
  refine ⟨final, (initializeState_block s pc).trace.trans trace, finalpc, index, ?_, ?_, ?_⟩
  · rw [frame 0x80440 (by unfold OutsideIndexPrefix; decide), initializeState_mem]; simp
  · rw [frame 0x80448 (by unfold OutsideIndexPrefix; decide), initializeState_mem]; simp
  · intro a outside mode pointer
    rw [frame a outside, initializeState_mem, if_neg pointer, if_neg mode]

/-- info: 'SigGolfCandidate.Hypertree.Verifying.entry_index_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms entry_index_frame

end SigGolfCandidate.Hypertree.Verifying
