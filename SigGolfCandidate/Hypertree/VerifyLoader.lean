import SigGolfCandidate.Hypertree.VerifyRefine
import SigGolfCandidate.Hypertree.SignatureDecode

namespace SigGolfCandidate.Hypertree.Verifying
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
set_option maxRecDepth 8192

/-- The verifier's public key survives loading the witness at its separate fixed address. -/
theorem loaded_publicKey (pk : PublicKey) (message : Message) (witness : Bytes signatureBytes)
    (s : MachineState) (loaded : initialState submission .verify (message, pk, witness) = some s)
    (i : Nat) (hi : i < 16) :
    s.getByte (BitVec.ofNat 64 (0x40 + i)) = pk.extractLsb' (8 * i) 8 := by
  unfold initialState at loaded
  rw [if_pos (admitted.2 .verify)] at loaded
  cases Option.some.inj loaded
  dsimp only [submission]
  dsimp only [inputBuffers, Riscv.standardLayout, Layout.message, Layout.secretKey, Layout.publicKey, Layout.cache, Layout.signature, Layout.witness, List.foldl_cons, List.foldl_nil]
  rw [Memory.getByte_setReg]
  rw [show witnessBase ⟨signatureBytes, signatureBytes⟩ = 0x3bc30 by decide]
  rw [Memory.write_preserves_byte _ 0x3bc30 (bytes witness) 0x40 i (by decide)
    (by rw [Memory.bytes_length (n := signatureBytes)]; decide) (by omega) (by left; omega)]
  exact Memory.write_value_byte _ 0x40 16 pk i (by decide) (by decide) hi

theorem loaded_message (pk : PublicKey) (message : Message) (witness : Bytes signatureBytes)
    (s : MachineState) (loaded : initialState submission .verify (message, pk, witness) = some s)
    (i : Nat) (hi : i < 32) :
    s.getByte (BitVec.ofNat 64 i) = message.extractLsb' (8 * i) 8 := by
  unfold initialState at loaded
  rw [if_pos (admitted.2 .verify)] at loaded
  cases Option.some.inj loaded
  dsimp only [submission]
  dsimp only [inputBuffers, Riscv.standardLayout, Layout.message, Layout.secretKey, Layout.publicKey, Layout.cache, Layout.signature, Layout.witness, List.foldl_cons, List.foldl_nil]
  rw [Memory.getByte_setReg]
  rw [show witnessBase ⟨signatureBytes, signatureBytes⟩ = 0x3bc30 by decide]
  have skipWitness (before : MachineState) := Memory.write_preserves_byte before 0x3bc30 (bytes witness) 0 i (by decide)
    (by rw [Memory.bytes_length (n := signatureBytes)]; decide) (by omega) (by left; omega)
  simp only [Nat.zero_add] at skipWitness
  rw [skipWitness]
  have skipKey (before : MachineState) := Memory.write_preserves_byte before 0x40 (bytes pk) 0 i (by decide)
    (by rw [Memory.bytes_length]; decide) (by omega) (by left; omega)
  simp only [Nat.zero_add] at skipKey
  rw [skipKey]
  simpa only [Nat.zero_add] using Memory.write_value_byte _ 0 32 message i (by decide) (by decide) hi

theorem loaded_witness (pk : PublicKey) (message : Message) (witness : Bytes signatureBytes)
    (s : MachineState) (loaded : initialState submission .verify (message, pk, witness) = some s)
    (i : Nat) (hi : i < signatureBytes) :
    s.getByte (BitVec.ofNat 64 (0x3bc30 + i)) = witness.extractLsb' (8 * i) 8 := by
  unfold initialState at loaded
  rw [if_pos (admitted.2 .verify)] at loaded
  cases Option.some.inj loaded
  dsimp only [submission]
  dsimp only [inputBuffers, Riscv.standardLayout, Layout.message, Layout.secretKey, Layout.publicKey, Layout.cache, Layout.signature, Layout.witness, List.foldl_cons, List.foldl_nil]
  rw [Memory.getByte_setReg]
  rw [show witnessBase ⟨signatureBytes, signatureBytes⟩ = 0x3bc30 by decide]
  exact Memory.write_value_byte _ 0x3bc30 signatureBytes witness i (by decide) (by decide) hi

/-- The protected verifier reaches its hypertree loop with the exact index of the public inputs and supplied witness randomizer. -/
theorem loaded_index_refines (hash : Hash) (pk : PublicKey) (message : Message) (witness : Bytes signatureBytes) :
    ∃ initial final,
      initialState submission .verify (message, pk, witness) = some initial ∧
      Trace hash verify initial 130 145 1 2 final ∧ final.pc = 0x1148 ∧
      readBuffer final 0x80408 19 =
        Reference.indexOf hash pk message (SignatureEncoding.decode witness).randomizer := by
  obtain ⟨initial, loaded, pc⟩ := initialState_exists submission admitted .verify (message, pk, witness)
  have randomizer : ∀ i, i < 32 → initial.getByte (BitVec.ofNat 64 (0x3bc30 + i)) =
      (SignatureEncoding.decode witness).randomizer.extractLsb' (8 * i) 8 := by
    intro i hi
    rw [loaded_witness pk message witness initial loaded i (by change i < 113616; omega)]
    dsimp only [SignatureEncoding.decode, SignatureEncoding.slice]
    rw [BitVec.extractLsb'_extractLsb'_of_le (by omega)]
  obtain ⟨final, trace, finalpc, index⟩ := entry_index_refines hash initial pk message
    (SignatureEncoding.decode witness).randomizer pc (loaded_publicKey pk message witness initial loaded)
    (loaded_message pk message witness initial loaded) randomizer
  exact ⟨initial, final, loaded, trace, finalpc, index⟩

/-- info: 'SigGolfCandidate.Hypertree.Verifying.loaded_index_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms loaded_index_refines

end SigGolfCandidate.Hypertree.Verifying
