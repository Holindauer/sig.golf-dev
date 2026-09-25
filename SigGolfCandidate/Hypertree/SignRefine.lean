import SigGolfCandidate.Hypertree.SignMemory
import SigGolfCandidate.Serialization
import SigGolfCandidate.Loader

namespace SigGolfCandidate.Hypertree.Signing
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false

/-- The exact reference tag6 query byte string. -/
def randomizerPayload (secretKey : SecretKey) (message : Message) : List Byte :=
  bytes (n := 8) (6 : BitVec 64) ++ bytes (n := 24) (0 : BitVec 192) ++
    (bytes secretKey ++ bytes message)

@[simp] theorem randomizerPayload_length (secretKey : SecretKey) (message : Message) :
    (randomizerPayload secretKey message).length = 96 := by simp [randomizerPayload, bytes]

theorem randomizerPayload_byte (secretKey : SecretKey) (message : Message) (i : Fin 96) :
    (randomizerPayload secretKey message)[i.val]'(by simp) =
      if i.val = 0 then 6 else if i.val < 32 then 0 else
        if i.val < 64 then secretKey.extractLsb' (8 * (i.val - 32)) 8
        else message.extractLsb' (8 * (i.val - 64)) 8 := by
  fin_cases i <;> simp [randomizerPayload, bytes, List.getElem_append]

theorem randomizerHashState_mem (s : MachineState) (a : Word) :
    (randomizerHashState s).getMem a = s.getMem a := by simp [randomizerHashState, execInstrBr]

theorem randomizerHashState_byte (s : MachineState) (a : Word) :
    (randomizerHashState s).getByte a = s.getByte a := by
  simp only [MachineState.getByte, randomizerHashState_mem]

/-- The bytecode's first oracle input is exactly the reference randomizer query.
Only the secret key and message loader facts are needed; all scratch preparation is proved. -/
theorem randomizer_query (original ready : MachineState) (secretKey : SecretKey) (message : Message)
    (hsecretKey : ∀ i, i < 32 → original.getByte (BitVec.ofNat 64 (0x20 + i)) = secretKey.extractLsb' (8 * i) 8)
    (hmessage : ∀ i, i < 32 → original.getByte (BitVec.ofNat 64 i) = message.extractLsb' (8 * i) 8)
    (words : ∀ i : Fin 12, ready.getMem (wordAddress 0x80000 i.val) = randomizerInputWord original i) :
    hashInput (randomizerHashState ready) = Reference.packed (randomizerPayload secretKey message) := by
  apply Serialization.hashInput_of_list (randomizerHashState ready) 0x80000 (randomizerPayload secretKey message)
  · exact (randomizerHashState_regs ready).2.1
  · rw [(randomizerHashState_regs ready).2.2.1, randomizerPayload_length]; rfl
  · intro i hi
    have bound : i < 96 := by simpa using hi
    rw [randomizerHashState_byte, prepared_randomizer_bytes original ready words ⟨i, bound⟩,
      randomizerInputByte_spec, randomizerPayload_byte secretKey message ⟨i, bound⟩]
    dsimp only
    split_ifs with h0 h32 h48
    · rfl
    · rfl
    · exact hsecretKey (i - 32) (by omega)
    · exact hmessage (i - 64) (by omega)

/-- Actual entry-to-randomizer execution refines the reference function, for every
fixed oracle. The typed loader can discharge the two explicit input-byte hypotheses. -/
theorem entry_randomizer_refines (hash : Hash) (s : MachineState) (secretKey : SecretKey) (message : Message)
    (pc : s.pc = 0x1000)
    (hsecretKey : ∀ i, i < 32 → s.getByte (BitVec.ofNat 64 (0x20 + i)) = secretKey.extractLsb' (8 * i) 8)
    (hmessage : ∀ i, i < 32 → s.getByte (BitVec.ofNat 64 i) = message.extractLsb' (8 * i) 8) :
    ∃ final, Trace hash sign s 117 132 1 2 final ∧ final.pc = 0x10fc ∧
      ∀ i : Fin 4, final.getMem (wordAddress 0x20060 i.val) =
        (Reference.randomizer hash secretKey message).extractLsb' (64 * i.val) 64 := by
  obtain ⟨ready, final, trace, finalpc, words, output⟩ := entry_randomizer_trace hash s pc
  have query := randomizer_query s ready secretKey message hsecretKey hmessage words
  refine ⟨final, trace, finalpc, ?_⟩
  intro i
  rw [output i, query]
  rfl

/-- info: 'SigGolfCandidate.Hypertree.Signing.entry_randomizer_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms entry_randomizer_refines

/-- The exact typed signer loader followed by real bytecode emits the reference
randomizer, for every secret key, untrusted cache, message and oracle. -/
theorem loaded_randomizer_refines (hash : Hash) (secretKey : SecretKey)
    (cache : Cache) (message : Message) :
    ∃ initial final,
      initialState submission .sign (secretKey, cache, message) = some initial ∧
      Trace hash sign initial 117 132 1 2 final ∧ final.pc = 0x10fc ∧
      readBuffer final 0x20060 32 = Reference.randomizer hash secretKey message := by
  obtain ⟨initial, loaded, pc⟩ := initialState_exists submission admitted .sign (secretKey, cache, message)
  obtain ⟨final, trace, finalpc, words⟩ := entry_randomizer_refines hash initial secretKey message pc
    (Loader.sign_secretKey submission (admitted.2 .sign) (by rfl) secretKey cache message initial loaded)
    (Loader.sign_message submission (admitted.2 .sign) (by rfl) secretKey cache message initial loaded)
  refine ⟨initial, final, loaded, trace, finalpc, ?_⟩
  apply Memory.readBuffer_of_bytes
  exact bytes_of_answer_words final 0x20060 (Reference.randomizer hash secretKey message)
    (by decide) (by decide) words

/-- info: 'SigGolfCandidate.Hypertree.Signing.loaded_randomizer_refines' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms loaded_randomizer_refines

/-- Stronger first-stage refinement retaining all low-memory inputs for the index hash. -/
theorem entry_randomizer_refines_frame (hash : Hash) (s : MachineState) (secretKey : SecretKey) (message : Message)
    (pc : s.pc = 0x1000)
    (hsecretKey : ∀ i, i < 32 → s.getByte (BitVec.ofNat 64 (0x20 + i)) = secretKey.extractLsb' (8 * i) 8)
    (hmessage : ∀ i, i < 32 → s.getByte (BitVec.ofNat 64 i) = message.extractLsb' (8 * i) 8) :
    ∃ final, Trace hash sign s 117 132 1 2 final ∧ final.pc = 0x10fc ∧
      (∀ i : Fin 4, final.getMem (wordAddress 0x20060 i.val) =
        (Reference.randomizer hash secretKey message).extractLsb' (64 * i.val) 64) ∧
      (∀ a, a.toNat < 0x20060 → final.getMem a = s.getMem a) := by
  obtain ⟨ready, prepared, readypc, words, prepareFrame⟩ := randomizer_prepare s pc
  obtain ⟨final, trace, finalpc, output, frame⟩ := randomizer_trace_frame hash ready readypc
  have query := randomizer_query s ready secretKey message hsecretKey hmessage words
  refine ⟨final, prepared.trace.trans trace, finalpc, ?_, ?_⟩
  · intro i
    rw [output i, query]
    rfl
  · intro a low
    have outside (base count : Nat) (lower : 0x20060 ≤ base)
        (bound : base + 8 * count ≤ MEMORY_BYTES) (i : Fin count) : a ≠ wordAddress base i.val := by
      have ne := outside_copy_word a.toNat base count i.val a.isLt bound i.isLt (Or.inl (by omega))
      simpa using ne
    rw [frame a (outside 0x20060 4 (by decide) (by decide))
      (outside 0x80300 4 (by decide) (by decide))]
    exact prepareFrame a (outside 0x80440 1 (by decide) (by decide) 0)
      (outside 0x80448 1 (by decide) (by decide) 0)
      (outside 0x80000 12 (by decide) (by decide))

/-- Word preservation below the signature buffer preserves each loaded input byte. -/
theorem low_words_byte (original final : MachineState)
    (frame : ∀ a, a.toNat < 0x20060 → final.getMem a = original.getMem a)
    (base i : Nat) (align : base % 8 = 0) (bound : base + i < 0x20060) :
    final.getByte (BitVec.ofNat 64 (base + i)) = original.getByte (BitVec.ofNat 64 (base + i)) := by
  rw [getByte_word final base i align (by omega), getByte_word original base i align (by omega)]
  rw [frame]
  have small : base + 8 * (i / 8) < 2 ^ 64 := by omega
  change (base + 8 * (i / 8)) % 2 ^ 64 < 0x20060
  rw [Nat.mod_eq_of_lt small]
  omega

end SigGolfCandidate.Hypertree.Signing
