import SigGolfCandidate.Hypertree.SignPreludeTreeEntry
namespace SigGolfCandidate.Hypertree.Signing
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 OracleComp Keygen

/-- Setup, encode zero digits, and call the root derivation, with all its entry invariants. -/
theorem derive_entry (image : Image) (setup : DeriveSetupCode image)
    (code : EncodeCode image 0x1340)
    (call : instructionAt image 0x1ca8 = some (.base (.JAL .x1 (-2272))))
    (s : MachineState) (secretKey : SecretKey)
    (pc : s.pc = 0x1c70) (stack : s.getReg .x2 = 0x1000000)
    (lo : s.getMem 0x80500 = 0) (hi : s.getMem 0x80508 = 0)
    (index : ∀ i : Fin 3, s.getMem (wordAddress 0x80408 i.val) =
      (BitVec.ofNat 192 0).extractLsb' (64*i.val) 64)
    (secret : ∀ i : Fin 4, s.getMem (wordAddress 0x20 i.val) =
      secretKey.extractLsb' (64*i.val) 64)
    (selector : s.getMem 0x80420 = 0) :
    ∃ final, OrdinarySteps image s 469 final ∧ final.pc = 0x13c8 ∧
      final.getReg .x1 = 0x1cac ∧ final.getReg .x2 = 0x1000000 ∧
      TreeContext final secretKey 159 0 ∧
      final.getMem 0x80448 = 0x20080 ∧ final.getMem 0x80440 ≠ 0 ∧
      final.getMem 0x80420 = 0 ∧
      (∀ i : Reference.Chain, final.getByte (BitVec.ofNat 64 (0x80600 + i.val)) =
        BitVec.ofNat 8 (Reference.digit 0 i).val) ∧
      (∀ a : Nat, a % 8 = 0 → a + 8 ≤ 0x20080 →
        final.getMem (BitVec.ofNat 64 a) = s.getMem (BitVec.ofNat 64 a)) := by
  obtain ⟨encoded, steps, ret, sp, digits, frame⟩ :=
    derive_encode image setup code s pc stack lo hi
  have ctx := encode_tree_context (deriveSetupState s) encoded secretKey
    (deriveSetup_context s secretKey index secret) frame
  have pointer : encoded.getMem 0x80448 = 0x20080 := by
    change encoded.getMem (BitVec.ofNat 64 0x80448) = _
    rw [frame _ (by decide) (by decide)]; exact deriveSetup_pointer s
  have mode : encoded.getMem 0x80440 = 1 := by
    change encoded.getMem (BitVec.ofNat 64 0x80440) = _
    rw [frame _ (by decide) (by decide)]; exact deriveSetup_mode s
  have select : encoded.getMem 0x80420 = 0 := by
    change encoded.getMem (BitVec.ofNat 64 0x80420) = _
    rw [frame _ (by decide) (by decide),
      deriveSetup_frame s _ (by decide) (by decide) (by decide)]
    exact selector
  refine ⟨deriveTreeCall encoded,
    ordinary_trans image s encoded _ 468 1 steps (deriveTreeCall_block image call encoded ret),
    deriveTreeCall_pc encoded ret, deriveTreeCall_return encoded ret, ?_,
    deriveTreeCall_context encoded secretKey ctx, ?_, ?_, ?_, ?_, ?_⟩
  · rw [deriveTreeCall_stack, sp, stack]
  · rw [deriveTreeCall_mem, pointer]
  · rw [deriveTreeCall_mem, mode]; decide
  · rw [deriveTreeCall_mem, select]
  · intro i; rw [deriveTreeCall_byte]; exact digits i
  · intro a aligned bound
    rw [deriveTreeCall_mem, frame a aligned (by omega)]
    apply deriveSetup_frame
    all_goals
      intro eq
      have ha : (BitVec.ofNat 64 a).toNat < 0x20080 := by
        simp only [BitVec.toNat_ofNat]; omega
      rw [eq] at ha
      exact absurd ha (by decide)

/-- info: 'SigGolfCandidate.Hypertree.Signing.derive_entry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms derive_entry
end SigGolfCandidate.Hypertree.Signing
