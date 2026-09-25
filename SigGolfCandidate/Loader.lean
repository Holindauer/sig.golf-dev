import SigGolfCandidate.Memory

set_option maxRecDepth 8192

namespace SigGolfCandidate.Loader
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64

/-- The signer's secret key bytes are intact after all public inputs and the stack register are loaded. -/
theorem sign_secretKey (submission : Submission) (valid : (submission.image .sign).Valid submission.sizes submission.layout)
    (standard : submission.layout = standardLayout submission.sizes)
    (secretKey : SecretKey) (pk : PublicKey) (cache : Cache) (message : Message) (s : MachineState)
    (loaded : initialState submission .sign (secretKey, pk, cache, message) = some s)
    (i : Nat) (hi : i < 32) :
    s.getByte (BitVec.ofNat 64 (0x20 + i)) = secretKey.extractLsb' (8 * i) 8 := by
  unfold initialState at loaded
  rw [if_pos valid] at loaded
  cases Option.some.inj loaded
  rw [standard]
  dsimp only [inputBuffers, standardLayout, List.foldl_cons, List.foldl_nil]
  rw [Memory.getByte_setReg]
  rw [Memory.write_preserves_byte _ 0 (bytes message) 0x20 i (by decide) (by simp) (by omega) (by right; simp)]
  rw [Memory.write_preserves_byte _ 0x60 (bytes cache) 0x20 i (by decide) (by rw [Memory.bytes_length (n := CACHE_BYTES)]; decide) (by omega) (by left; omega)]
  rw [Memory.write_preserves_byte _ 0x40 (bytes pk) 0x20 i (by decide) (by simp) (by omega) (by left; omega)]
  exact Memory.write_value_byte _ 0x20 32 secretKey i (by decide) (by decide) hi

/-- The message occupies its fixed buffer in the official initial sign state. -/
theorem sign_message (submission : Submission) (valid : (submission.image .sign).Valid submission.sizes submission.layout)
    (standard : submission.layout = standardLayout submission.sizes)
    (secretKey : SecretKey) (pk : PublicKey) (cache : Cache) (message : Message) (s : MachineState)
    (loaded : initialState submission .sign (secretKey, pk, cache, message) = some s)
    (i : Nat) (hi : i < 32) :
    s.getByte (BitVec.ofNat 64 i) = message.extractLsb' (8 * i) 8 := by
  unfold initialState at loaded
  rw [if_pos valid] at loaded
  cases Option.some.inj loaded
  rw [standard]
  dsimp only [inputBuffers, standardLayout, List.foldl_cons, List.foldl_nil]
  rw [Memory.getByte_setReg]
  simpa only [Nat.zero_add] using Memory.write_value_byte _ 0 32 message i (by decide) (by decide) hi

/-- info: 'SigGolfCandidate.Loader.sign_secretKey' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sign_secretKey

/-- info: 'SigGolfCandidate.Loader.sign_message' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sign_message

/-- The public key remains intact after loading the cache and message. -/
theorem sign_publicKey (submission : Submission) (valid : (submission.image .sign).Valid submission.sizes submission.layout)
    (standard : submission.layout = standardLayout submission.sizes)
    (secretKey : SecretKey) (pk : PublicKey) (cache : Cache) (message : Message) (s : MachineState)
    (loaded : initialState submission .sign (secretKey, pk, cache, message) = some s)
    (i : Nat) (hi : i < 16) :
    s.getByte (BitVec.ofNat 64 (0x40 + i)) = pk.extractLsb' (8 * i) 8 := by
  unfold initialState at loaded
  rw [if_pos valid] at loaded
  cases Option.some.inj loaded
  rw [standard]
  dsimp only [inputBuffers, standardLayout, List.foldl_cons, List.foldl_nil]
  rw [Memory.getByte_setReg]
  rw [Memory.write_preserves_byte _ 0 (bytes message) 0x40 i (by decide) (by simp) (by omega) (by right; simp)]
  rw [Memory.write_preserves_byte _ 0x60 (bytes cache) 0x40 i (by decide) (by rw [Memory.bytes_length (n := CACHE_BYTES)]; decide) (by omega) (by left; omega)]
  exact Memory.write_value_byte _ 0x40 16 pk i (by decide) (by decide) hi

/-- info: 'SigGolfCandidate.Loader.sign_publicKey' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sign_publicKey

end SigGolfCandidate.Loader
