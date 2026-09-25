import SigGolfCandidate.Hypertree.VerifyLoader
import SigGolfCandidate.Hypertree.VerifyStack

namespace SigGolfCandidate.Hypertree.Verifying
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 Keygen Signing
set_option maxRecDepth 8192

/-- Scratch memory starts at zero, beyond every verifier input. -/
theorem loaded_scratch (pk : PublicKey) (message : Message) (witness : Bytes signatureBytes)
    (s : MachineState) (loaded : initialState submission .verify (message, pk, witness) = some s)
    (a : Word) (high : 0x80000 ≤ a.toNat) : s.getMem a = 0 := by
  unfold initialState at loaded
  rw [if_pos (admitted.2 .verify)] at loaded
  cases Option.some.inj loaded
  dsimp only [submission]
  dsimp only [inputBuffers, Riscv.standardLayout, Layout.message, Layout.secretKey, Layout.publicKey, Layout.cache, Layout.signature, Layout.witness, List.foldl_cons, List.foldl_nil]
  rw [MachineState.getMem_setReg]
  rw [show witnessBase ⟨signatureBytes, signatureBytes⟩ = 0x3bc30 by decide]
  rw [Memory.write_preserves _ 0x3bc30 (bytes witness) a
    (by rw [Memory.bytes_length (n := signatureBytes)]; decide)
    (by right; rw [Memory.bytes_length (n := signatureBytes)]; change 358400 ≤ a.toNat; omega)]
  rw [Memory.write_preserves _ 0x40 (bytes pk) a
    (by rw [Memory.bytes_length]; decide)
    (by right; rw [Memory.bytes_length]; omega)]
  rw [Memory.write_preserves _ 0 (bytes message) a
    (by rw [Memory.bytes_length]; decide)
    (by right; rw [Memory.bytes_length]; omega)]
  rw [show verify.data = [] by rfl, MachineState.writeBytesAsWords_nil]
  rfl

theorem loaded_stack (pk : PublicKey) (message : Message) (witness : Bytes signatureBytes)
    (s : MachineState) (loaded : initialState submission .verify (message, pk, witness) = some s) :
    s.getReg .x2 = 0x1000000 := by
  unfold initialState at loaded
  rw [if_pos (admitted.2 .verify)] at loaded
  cases Option.some.inj loaded
  rw [MachineState.getReg_setReg_eq (by decide)]
  rfl

/-- All persistent inputs lie below the scratch region used by index recovery. -/
theorem outside_index_of_lt (a : Word) (low : a.toNat < 0x80000) : OutsideIndexPrefix a := by
  refine ⟨?_, ?_, ?_⟩
  all_goals
    intro i eq
    have h := congrArg BitVec.toNat eq
    simp only [wordAddress, BitVec.toNat_ofNat] at h
    have := i.isLt
    omega

/-- Full loop-entry invariant for arbitrary typed verifier inputs. -/
theorem loaded_loop_entry (hash : Hash) (pk : PublicKey) (message : Message) (witness : Bytes signatureBytes) :
    ∃ initial final,
      initialState submission .verify (message, pk, witness) = some initial ∧
      Trace hash verify initial 130 145 1 2 final ∧ final.pc = 0x1148 ∧
      StoredIndex final ((Reference.indexOf hash pk message (SignatureEncoding.decode witness).randomizer).zeroExtend 192) ∧
      final.getReg .x2 = 0x1000000 ∧ final.getMem 0x80400 = 0 ∧
      final.getMem 0x80440 = 0 ∧ final.getMem 0x80448 = 0x3bc50 ∧
      final.getMem 0x80500 = 0 ∧ final.getMem 0x80508 = 0 ∧
      (∀ a, a.toNat < 0x80000 → final.getMem a = initial.getMem a) := by
  obtain ⟨initial, loaded, pc⟩ := initialState_exists submission admitted .verify (message, pk, witness)
  have randomizer : ∀ i, i < 32 → initial.getByte (BitVec.ofNat 64 (0x3bc30 + i)) =
      (SignatureEncoding.decode witness).randomizer.extractLsb' (8 * i) 8 := by
    intro i hi
    rw [loaded_witness pk message witness initial loaded i (by change i < 113616; omega)]
    dsimp only [SignatureEncoding.decode, SignatureEncoding.slice]
    rw [BitVec.extractLsb'_extractLsb'_of_le (by omega)]
  obtain ⟨final, trace, finalpc, index, mode, pointer, frame⟩ := entry_index_frame hash initial pk message
    (SignatureEncoding.decode witness).randomizer pc (loaded_publicKey pk message witness initial loaded)
    (loaded_message pk message witness initial loaded) randomizer
  refine ⟨initial, final, loaded, trace, finalpc, index, ?_, ?_, mode, pointer, ?_, ?_, ?_⟩
  · exact (entry_stack hash initial final pc trace).trans (loaded_stack pk message witness initial loaded)
  · rw [frame 0x80400 (by unfold OutsideIndexPrefix; decide) (by decide) (by decide)]
    exact loaded_scratch pk message witness initial loaded _ (by decide)
  · rw [frame 0x80500 (by unfold OutsideIndexPrefix; decide) (by decide) (by decide)]
    exact loaded_scratch pk message witness initial loaded _ (by decide)
  · rw [frame 0x80508 (by unfold OutsideIndexPrefix; decide) (by decide) (by decide)]
    exact loaded_scratch pk message witness initial loaded _ (by decide)
  · intro a low
    apply frame a (outside_index_of_lt a low)
    · intro eq; subst a; contradiction
    · intro eq; subst a; contradiction

/-- info: 'SigGolfCandidate.Hypertree.Verifying.loaded_loop_entry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms loaded_loop_entry

end SigGolfCandidate.Hypertree.Verifying
