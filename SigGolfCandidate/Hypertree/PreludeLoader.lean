import SigGolfCandidate.Hypertree.PreludeJump
import SigGolfCandidate.Loader
namespace SigGolfCandidate.Hypertree.Signing.Prelude
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 Keygen
set_option maxRecDepth 8192
set_option maxHeartbeats 800000

/-- Research submission using the new signer; no complete certificate is asserted here. -/
def preludeSubmission : Submission :=
  { submission with image := fun phase => match phase with
      | .sign => signPrelude
      | other => submission.image other }

theorem sign_valid : (preludeSubmission.image .sign).Valid preludeSubmission.sizes preludeSubmission.layout := by decide

theorem loaded_scratch (secretKey : SecretKey) (cache : Cache) (message : Message)
    (s : MachineState) (loaded : initialState preludeSubmission .sign (secretKey, cache, message) = some s)
    (a : Word) (high : 0x80000 ≤ a.toNat) : s.getMem a = 0 := by
  unfold initialState at loaded
  rw [if_pos sign_valid] at loaded
  cases Option.some.inj loaded
  dsimp only [preludeSubmission, submission, inputBuffers, Riscv.standardLayout,
    List.foldl_cons, List.foldl_nil]
  rw [MachineState.getMem_setReg]
  rw [Memory.write_preserves _ 0 (bytes message) a
    (by rw [Memory.bytes_length]; decide) (by right; rw [Memory.bytes_length]; omega)]
  rw [Memory.write_preserves _ 0x60 (bytes cache) a
    (by rw [Memory.bytes_length]; decide) (by right; rw [Memory.bytes_length]; change 131168 ≤ a.toNat; omega)]
  rw [Memory.write_preserves _ 0x20 (bytes secretKey) a
    (by rw [Memory.bytes_length]; decide) (by right; rw [Memory.bytes_length]; omega)]
  rw [show signPrelude.data = [] by rfl, MachineState.writeBytesAsWords_nil]
  rfl

theorem loaded_stack (secretKey : SecretKey) (cache : Cache) (message : Message)
    (s : MachineState) (loaded : initialState preludeSubmission .sign (secretKey, cache, message) = some s) :
    s.getReg .x2 = 0x1000000 := by
  unfold initialState at loaded
  rw [if_pos sign_valid] at loaded
  cases Option.some.inj loaded
  rw [MachineState.getReg_setReg_eq (by decide)]
  rfl

theorem loaded_pc (secretKey : SecretKey) (cache : Cache) (message : Message)
    (s : MachineState) (loaded : initialState preludeSubmission .sign (secretKey, cache, message) = some s) :
    s.pc = 0x1000 := by
  unfold initialState at loaded
  rw [if_pos sign_valid] at loaded
  cases Option.some.inj loaded
  dsimp only [preludeSubmission, submission, inputBuffers, Riscv.standardLayout, List.foldl_cons, List.foldl_nil]
  simp only [MachineState.pc_setReg, MachineState.pc_writeBytesAsWords]

theorem secretKey_words_of_bytes (s : MachineState) (base : Nat) (value : SecretKey)
    (aligned : base%8=0) (bound : base+32<2^64)
    (bytes : ∀ i, i<32 → s.getByte (BitVec.ofNat 64 (base+i)) = value.extractLsb' (8*i) 8)
    (i : Fin 4) : s.getMem (wordAddress base i.val)=value.extractLsb' (64*i.val) 64 := by
  apply eq_of_forall_extractByte
  intro j hj
  have hi := i.isLt
  have whole : 8*i.val+j<32 := by omega
  have quot : (8*i.val+j)/8=i.val := by omega
  have rem : (8*i.val+j)%8=j := by omega
  have h := bytes (8*i.val+j) whole
  rw [getByte_word _ base (8*i.val+j) aligned (by omega)] at h
  simp only [quot,rem] at h
  rw [h]
  symm
  simpa only [quot,rem] using KeygenNode.extractByte_slice value (8*i.val+j)

theorem loaded_secret_words (secretKey : SecretKey) (cache : Cache) (message : Message)
    (s : MachineState) (loaded : initialState preludeSubmission .sign (secretKey, cache, message) = some s)
    (i : Fin 4) : s.getMem (wordAddress 0x20 i.val) = secretKey.extractLsb' (64*i.val) 64 := by
  apply secretKey_words_of_bytes s 0x20 secretKey (by decide) (by decide)
  exact Loader.sign_secretKey preludeSubmission sign_valid rfl secretKey cache message s loaded

/-- info: 'SigGolfCandidate.Hypertree.Signing.Prelude.loaded_scratch' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms loaded_scratch
/-- info: 'SigGolfCandidate.Hypertree.Signing.Prelude.loaded_secret_words' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms loaded_secret_words
end SigGolfCandidate.Hypertree.Signing.Prelude
