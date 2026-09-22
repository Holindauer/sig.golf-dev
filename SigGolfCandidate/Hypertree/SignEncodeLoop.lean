import SigGolfCandidate.Hypertree.SignEncode

namespace SigGolfCandidate.Hypertree.Signing
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false

def encodeDigit (message : BitVec 128) (i : Nat) : Nat := message.toNat / 8 ^ i % 8

def encodeSum (message : BitVec 128) (n : Nat) : Nat :=
  ∑ i ∈ Finset.range n, encodeDigit message i

theorem encodeDigit_lt (message : BitVec 128) (i : Nat) : encodeDigit message i < 8 :=
  Nat.mod_lt _ (by decide)

theorem encodeSum_succ (message : BitVec 128) (n : Nat) :
    encodeSum message (n + 1) = encodeSum message n + encodeDigit message n := by
  exact Finset.sum_range_succ _ _

theorem encode_shift_low (value : BitVec 128) :
    (value.extractLsb' 0 64 >>> 3) + (value.extractLsb' 64 64 <<< 61) =
      (value >>> 3).extractLsb' 0 64 := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_add, BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft,
    BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
  omega

theorem encode_shift_high (value : BitVec 128) :
    (value.extractLsb' 64 64 >>> 3) = (value >>> 3).extractLsb' 64 64 := by
  apply BitVec.eq_of_toNat_eq
  have bound := value.isLt
  simp [BitVec.toNat_ushiftRight, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
  omega

theorem encode_digit_limb (message : BitVec 128) (i : Nat) :
    (message >>> (3 * i)).extractLsb' 0 64 &&& 7 = BitVec.ofNat 64 (encodeDigit message i) := by
  apply BitVec.eq_of_toNat_eq
  have small := encodeDigit_lt message i
  have power : 8 ^ i = 2 ^ (3 * i) := by rw [show (8 : Nat) = 2 ^ 3 by decide, Nat.pow_mul]
  simp only [BitVec.toNat_and, BitVec.extractLsb'_toNat, BitVec.toNat_ushiftRight,
    Nat.shiftRight_eq_div_pow, Nat.pow_zero, Nat.div_one, BitVec.toNat_ofNat]
  change ((message.toNat / 2 ^ (3 * i)) % 2 ^ 64) &&& 7 = _
  rw [show (7 : Nat) = 2 ^ 3 - 1 by decide, Nat.and_two_pow_sub_one_eq_mod]
  simp only [show 2 ^ 3 = (8 : Nat) by decide]
  unfold encodeDigit at small ⊢
  rw [power]
  omega

/-- The running digest is shifted by three bits per completed message digit. -/
def EncodeInvariant (base : Word) (message : BitVec 128) (n : Nat) (s : MachineState) : Prop :=
  n ≤ 43 ∧ s.pc = (if n = 0 then base + 40 else base) ∧
  s.getReg .x6 = (message >>> (3 * (43 - n))).extractLsb' 0 64 ∧
  s.getReg .x7 = (message >>> (3 * (43 - n))).extractLsb' 64 64 ∧
  s.getReg .x10 = BitVec.ofNat 64 (0x80600 + (43 - n)) ∧
  s.getReg .x11 = BitVec.ofNat 64 n ∧
  s.getReg .x12 = 301 - BitVec.ofNat 64 (encodeSum message (43 - n))

def EncodedPrefix (message : BitVec 128) (n : Nat) (s : MachineState) : Prop :=
  ∀ i, i < 43 - n → s.getByte (BitVec.ofNat 64 (0x80600 + i)) = BitVec.ofNat 8 (encodeDigit message i)

theorem encode_next_invariant (base : Word) (message : BitVec 128) (n : Nat) (s : MachineState)
    (inv : EncodeInvariant base message (n + 1) s) : EncodeInvariant base message n (encodeNext s) := by
  obtain ⟨hn, pc, lo, hi, ptr, count, sum⟩ := inv
  have processed : 43 - n = (43 - (n + 1)) + 1 := by omega
  have shift : message >>> (3 * (43 - n)) = (message >>> (3 * (43 - (n + 1)))) >>> 3 := by
    rw [processed, Nat.mul_add, Nat.mul_one, BitVec.shiftRight_add]
  have hc : BitVec.ofNat 64 (n + 1) = 1 ↔ n = 0 := by
    constructor
    · intro eq
      have value := congrArg BitVec.toNat eq
      change (n + 1) % 2 ^ 64 = 1 at value
      rw [Nat.mod_eq_of_lt (by omega)] at value
      omega
    · intro eq; subst n; rfl
  obtain ⟨rlo, rhi, rptr, rcount, rsum⟩ := encodeNext_regs s
  refine ⟨by omega, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hp : s.pc = base := by simpa using pc
    rw [encodeNext_pc, hp, count]
    simp only [hc]
  · rw [rlo, lo, hi, shift]
    exact encode_shift_low _
  · rw [rhi, hi, shift]
    exact encode_shift_high _
  · rw [rptr, ptr, processed]
    change BitVec.ofNat 64 (0x80600 + (43 - (n + 1))) + BitVec.ofNat 64 1 = _
    rw [← BitVec.ofNat_add]
    congr 1
  · rw [rcount, count, BitVec.ofNat_add]
    exact BitVec.add_sub_cancel _ _
  · rw [rsum, sum, lo, encode_digit_limb, processed, encodeSum_succ, BitVec.ofNat_add]
    exact BitVec.sub_sub _ _ _

theorem encode_next_prefix (base : Word) (message : BitVec 128) (n : Nat) (s : MachineState)
    (inv : EncodeInvariant base message (n + 1) s) (outputPrefix : EncodedPrefix message (n + 1) s) :
    EncodedPrefix message n (encodeNext s) := by
  obtain ⟨hn, _, lo, _, ptr, _, _⟩ := inv
  intro i hi
  by_cases eq : i = 43 - (n + 1)
  · subst i
    rw [encodeNext_byte, ptr, if_pos rfl, lo, encode_digit_limb]
    simp
  · have ne : BitVec.ofNat 64 (0x80600 + i) ≠ BitVec.ofNat 64 (0x80600 + (43 - (n + 1))) := by
      intro he
      have values := congrArg BitVec.toNat he
      have h1 : 0x80600 + i < 2 ^ 64 := by omega
      have h2 : 0x80600 + (43 - (n + 1)) < 2 ^ 64 := by omega
      simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2] at values
      omega
    rw [encodeNext_byte, ptr, if_neg ne]
    exact outputPrefix i (by omega)

theorem encode_loop (image : Image) (base : Word) (code : EncodeLoopCode image base)
    (message : BitVec 128) (n : Nat) (s : MachineState)
    (inv : EncodeInvariant base message n s) (outputPrefix : EncodedPrefix message n s) :
    ∃ final, OrdinarySteps image s (10 * n) final ∧ EncodeInvariant base message 0 final ∧
      EncodedPrefix message 0 final ∧
      (∀ a, (∀ i : Fin 43, a ≠ BitVec.ofNat 64 (0x80600 + i.val)) → final.getByte a = s.getByte a) ∧ final.getReg .x2 = s.getReg .x2 := by
  induction n generalizing s with
  | zero => exact ⟨s, OrdinarySteps.refl _, inv, outputPrefix, (fun _ _ => rfl), rfl⟩
  | succ n ih =>
    have hn := inv.1
    have pc : s.pc = base := by simpa using inv.2.1
    have valid : accessValid (s.getReg .x10) 1 = true := by
      rw [inv.2.2.2.2.1]
      simp [accessValid, rangeValid, MEMORY_BYTES]
      omega
    obtain ⟨final, tail, finalInv, output, frame, stack⟩ := ih (encodeNext s)
      (encode_next_invariant base message n s inv) (encode_next_prefix base message n s inv outputPrefix)
    refine ⟨final, ?_, finalInv, output, ?_, ?_⟩
    · simpa only [Nat.mul_add, Nat.mul_one] using Keygen.ordinary_trans image s _ final 10 (10 * n)
        (encodeNext_block image base code s pc valid) tail
    · intro a outside
      rw [frame a outside, encodeNext_byte, inv.2.2.2.2.1,
        if_neg (outside ⟨43 - (n + 1), by omega⟩)]
    · exact stack.trans (encodeNext_sp s)

theorem encodeSum_reference (message : Reference.Digest) :
    encodeSum message 43 = ∑ i : Fin 43, Reference.messageDigit message i := by
  rw [encodeSum, ← Fin.sum_univ_eq_sum_range]
  rfl

theorem encodeSum_bound (message : BitVec 128) : encodeSum message 43 ≤ 301 := by
  calc
    _ ≤ ∑ _i ∈ Finset.range 43, (7 : Nat) := by
      apply Finset.sum_le_sum
      intro i _
      have := encodeDigit_lt message i
      omega
    _ = 301 := by simp

/-- The complete 43-round message-digit loop terminates in exactly 430 ordinary
instructions, stores the reference digits and computes the reference checksum. -/
theorem encode_message_refines (image : Image) (base : Word) (code : EncodeLoopCode image base)
    (message : Reference.Digest) (s : MachineState)
    (pc : s.pc = base)
    (lo : s.getReg .x6 = message.extractLsb' 0 64)
    (hi : s.getReg .x7 = message.extractLsb' 64 64)
    (ptr : s.getReg .x10 = 0x80600) (count : s.getReg .x11 = 43)
    (checksum : s.getReg .x12 = 301) :
    ∃ final, OrdinarySteps image s 430 final ∧ final.pc = base + 40 ∧
      final.getReg .x10 = 0x8062b ∧
      final.getReg .x12 = BitVec.ofNat 64 (Reference.checksum message) ∧
      (∀ i : Fin 43, final.getByte (BitVec.ofNat 64 (0x80600 + i.val)) =
        BitVec.ofNat 8 (Reference.messageDigit message i)) ∧
      (∀ a, (∀ i : Fin 43, a ≠ BitVec.ofNat 64 (0x80600 + i.val)) → final.getByte a = s.getByte a) ∧ final.getReg .x2 = s.getReg .x2 := by
  have initial : EncodeInvariant base message 43 s := by
    simp [EncodeInvariant, pc, lo, hi, ptr, count, checksum, encodeSum]
  have empty : EncodedPrefix message 43 s := by intro i h; omega
  obtain ⟨final, trace, inv, output, frame, stack⟩ := encode_loop image base code message 43 s initial empty
  refine ⟨final, trace, by simpa using inv.2.1, by simpa using inv.2.2.2.2.1, ?_, ?_, frame, stack⟩
  · rw [inv.2.2.2.2.2.2]
    have bound := encodeSum_bound message
    change BitVec.ofNat 64 301 - BitVec.ofNat 64 (encodeSum message 43) = _
    rw [BitVec.ofNat_sub_ofNat_of_le 301 (encodeSum message 43) (by omega) bound, encodeSum_reference]
    rfl
  · intro i
    exact output i.val (by have := i.isLt; omega)

/-- info: 'SigGolfCandidate.Hypertree.Signing.encode_message_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms encode_message_refines

end SigGolfCandidate.Hypertree.Signing
