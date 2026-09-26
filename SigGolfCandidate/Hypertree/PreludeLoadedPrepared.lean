import SigGolfCandidate.Hypertree.PreludeLoader
namespace SigGolfCandidate.Hypertree.Signing.Prelude
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 Keygen
set_option maxRecDepth 8192

theorem loaded_prepared (hash : Hash) (secretKey : SecretKey) (cache : Cache) (message : Message)
    (s : MachineState) (loaded : initialState preludeSubmission .sign (secretKey, cache, message) = some s) :
    ∃ final instructions cycles,
      Trace hash signPrelude s instructions cycles 739 761 final ∧
      instructions ≤ 100422 ∧ cycles ≤ 105771 ∧
      final.pc = 0x1004 ∧ final.getReg .x2 = 0x1000000 ∧ final.getReg .x6 = 1 ∧
      (∀ i : Fin 2, final.getMem (wordAddress 0x40 i.val) =
        (Reference.keygen hash secretKey).extractLsb' (64*i.val) 64) ∧
      final.getMem 0x80400 = 0 ∧
      (∀ i : Fin 3, final.getMem (wordAddress 0x80408 i.val) = 0) ∧
      (∀ i : Fin 2, final.getMem (wordAddress 0x80500 i.val) = 0) ∧
      (∀ a : Nat, a % 8 = 0 → a + 8 ≤ 0x20080 → a ≠ 0x40 → a ≠ 0x48 →
        final.getMem (BitVec.ofNat 64 a) = s.getMem (BitVec.ofNat 64 a)) := by
  have pc := loaded_pc secretKey cache message s loaded
  have sp := loaded_stack secretKey cache message s loaded
  have zero := loaded_scratch secretKey cache message s loaded
  have words := loaded_secret_words secretKey cache message s loaded
  have jumpPC := entryJump_pc s pc
  have jumpSP : (entryJump s).getReg .x2 = 0x1000000 := by rw [entryJump_stack, sp]
  have low : (entryJump s).getMem 0x80500 = 0 := by rw [entryJump_mem]; exact zero _ (by decide)
  have high : (entryJump s).getMem 0x80508 = 0 := by rw [entryJump_mem]; exact zero _ (by decide)
  have index : ∀ i : Fin 3, (entryJump s).getMem (wordAddress 0x80408 i.val) =
      (BitVec.ofNat 192 0).extractLsb' (64*i.val) 64 := by
    intro i
    rw [entryJump_mem, zero _ (by fin_cases i <;> decide)]
    fin_cases i <;> rfl
  have secret : ∀ i : Fin 4, (entryJump s).getMem (wordAddress 0x20 i.val) =
      secretKey.extractLsb' (64*i.val) 64 := by intro i; rw [entryJump_mem]; exact words i
  have selector : (entryJump s).getMem 0x80420 = 0 := by rw [entryJump_mem]; exact zero _ (by decide)
  obtain ⟨final, n, c, run, nb, cb, fpc, fsp, ready, pk, level, idx, current, frame⟩ :=
    prepare_signer hash (entryJump s) secretKey jumpPC jumpSP low high index secret selector
  refine ⟨final, 1+n, 1+c, (entryJump_block s pc).trace.trans run,
    by omega, by omega, fpc, fsp, ready, pk, level, idx, current, ?_⟩
  intro a aligned bound h0 h1
  rw [frame a aligned bound h0 h1, entryJump_mem]

/-- info: 'SigGolfCandidate.Hypertree.Signing.Prelude.loaded_prepared' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms loaded_prepared
end SigGolfCandidate.Hypertree.Signing.Prelude
