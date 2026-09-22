import SigGolfCandidate.Hypertree.Expand

namespace SigGolfCandidate.Hypertree.Keygen
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 OracleComp

/-- Decode at a code address, without exposing any mutable machine fields. -/
def instructionAt (image : Image) (pc : Word) : Option Instruction :=
  fetch image { regs := fun _ => 0, mem := fun _ => 0, pc := pc }

theorem fetch_at (image : Image) (s : MachineState) :
    fetch image s = instructionAt image s.pc := rfl

/-- The six encodings of the generated word-copy loop. -/
def CopyCode (image : Image) (pc : Word) : Prop :=
  instructionAt image pc = some (.base (.LD .x11 .x6 0)) ∧
  instructionAt image (pc + 4) = some (.base (.SD .x7 .x11 0)) ∧
  instructionAt image (pc + 8) = some (.base (.ADDI .x6 .x6 8)) ∧
  instructionAt image (pc + 12) = some (.base (.ADDI .x7 .x7 8)) ∧
  instructionAt image (pc + 16) = some (.base (.ADDI .x10 .x10 (-1))) ∧
  instructionAt image (pc + 20) = some (.base (.BNE .x10 .x0 (-20)))

instance (image : Image) (pc : Word) : Decidable (CopyCode image pc) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))

/-- A complete copy iteration checked against the organizer's protected interpreter. -/
theorem copy_block (image : Image) (p : Word) (code : CopyCode image p)
    (s : MachineState) (pc : s.pc = p)
    (src : accessValid (s.getReg .x6) 8 = true)
    (dst : accessValid (s.getReg .x7) 8 = true) :
    OrdinarySteps image s 6 (Expansion.loopNext s) := by
  obtain ⟨c0,c1,c2,c3,c4,c5⟩ := code
  let s1 := execInstrBr s (.LD .x11 .x6 0)
  let s2 := execInstrBr s1 (.SD .x7 .x11 0)
  let s3 := execInstrBr s2 (.ADDI .x6 .x6 8)
  let s4 := execInstrBr s3 (.ADDI .x7 .x7 8)
  let s5 := execInstrBr s4 (.ADDI .x10 .x10 (-1))
  apply OrdinarySteps.step s s1 _ (.base (.LD .x11 .x6 0)) 5
  · simpa only [fetch_at, pc] using c0
  · simp [s1, ordinaryStep, memoryArgumentsValid, signExtend12, src]
  apply OrdinarySteps.step s1 s2 _ (.base (.SD .x7 .x11 0)) 4
  · simpa only [fetch_at, s1, execInstrBr, MachineState.setPC, pc] using c1
  · have hd : accessValid (s1.getReg .x7) 8 = true := by
      simpa [s1, execInstrBr, signExtend12, MachineState.getReg, MachineState.setReg, MachineState.setPC] using dst
    simp [s2, ordinaryStep, memoryArgumentsValid, signExtend12, hd]
  apply OrdinarySteps.step s2 s3 _ (.base (.ADDI .x6 .x6 8)) 3
  · simpa [fetch_at, s1, s2, execInstrBr, MachineState.setPC, pc, BitVec.add_assoc] using c2
  · rfl
  apply OrdinarySteps.step s3 s4 _ (.base (.ADDI .x7 .x7 8)) 2
  · simpa [fetch_at, s1, s2, s3, execInstrBr, MachineState.setPC, pc, BitVec.add_assoc] using c3
  · rfl
  apply OrdinarySteps.step s4 s5 _ (.base (.ADDI .x10 .x10 (-1))) 1
  · simpa [fetch_at, s1, s2, s3, s4, execInstrBr, MachineState.setPC, pc, BitVec.add_assoc] using c4
  · rfl
  apply OrdinarySteps.step s5 (Expansion.loopNext s) _ (.base (.BNE .x10 .x0 (-20))) 0
  · simpa [fetch_at, s1, s2, s3, s4, s5, execInstrBr, MachineState.setPC, pc, BitVec.add_assoc] using c5
  · rfl
  exact OrdinarySteps.refl _

theorem copy_next_pc (s : MachineState) :
    (Expansion.loopNext s).pc = if s.getReg .x10 = 1 then s.pc + 24 else s.pc := by
  have decrement (x : Word) : x - 1#64 = 0#64 ↔ x = 1#64 :=
    BitVec.sub_left_inj (x := x) (y := 1) 1
  simp only [Expansion.loopNext, execInstrBr, Expansion.pc_ite, Expansion.pc_setPC,
    Expansion.loop_body_pc, Expansion.loop_body_count, Expansion.reg_zero, signExtend13]
  simp [decrement, BitVec.add_assoc]

/-- The HASH service accepts exactly the fixed buffers used by all four images. -/
theorem hash_arguments (s : MachineState) (bits : Nat)
    (src : s.getReg .x10 = 0x80000) (len : s.getReg .x11 = BitVec.ofNat 64 bits)
    (dst : s.getReg .x12 = 0x80300) (bound : bits ≤ 6144) :
    hashArgumentsValid s = true := by
  have small : bits < 2 ^ 64 := by omega
  simp [hashArgumentsValid, src, len, dst, accessValid, rangeValid,
    BitVec.toNat_ofNat, MEMORY_BYTES]
  omega

/-- Hash output preserves all integer registers and advances exactly one instruction. -/
theorem hash_registers (s : MachineState) (answer : BitVec 256) (r : Reg) :
    (writeHash s answer).getReg r = s.getReg r := by simp [writeHash]

theorem hash_pc (s : MachineState) (answer : BitVec 256) :
    (writeHash s answer).pc = s.pc + 4 := rfl

/-- Resource accounting at a real HASH instruction, independent of the oracle answer. -/
theorem hash_then (image : Image) (hash : Hash) (s : MachineState) (bits : Nat)
    (code : instructionAt image s.pc = some (.base .ECALL))
    (service : s.getReg .x5 = 1)
    (src : s.getReg .x10 = 0x80000) (len : s.getReg .x11 = BitVec.ofNat 64 bits)
    (dst : s.getReg .x12 = 0x80300) (bound : bits ≤ 6144)
    (steps : Nat) (result : Execution)
    (tail : Executes hash image (writeHash s (hash (hashInput s))) steps result) :
    Executes hash image s (steps + 1)
      (result.charge (8 * compressions bits) 1 (compressions bits)) := by
  have small : bits < 2 ^ 64 := by omega
  have input_len : (hashInput s).1 = bits := by
    simp only [hashInput, len, BitVec.toNat_ofNat, Nat.mod_eq_of_lt small]
  simpa only [input_len] using Executes.hash s steps result code service
    (hash_arguments s bits src len dst bound) tail

/-- Source and destination are mathematical byte addresses, and `n` counts remaining words. -/
def CopyInvariant (p : Word) (source destination total n : Nat) (s : MachineState) : Prop :=
  n ≤ total ∧ total ≤ 2097152 ∧
  s.pc = (if n = 0 then p + 24 else p) ∧
  s.getReg .x6 = BitVec.ofNat 64 (source + 8 * (total - n)) ∧
  s.getReg .x7 = BitVec.ofNat 64 (destination + 8 * (total - n)) ∧
  s.getReg .x10 = BitVec.ofNat 64 n

theorem copy_invariant_next (p : Word) (source destination total n : Nat) (s : MachineState)
    (inv : CopyInvariant p source destination total (n + 1) s) :
    CopyInvariant p source destination total n (Expansion.loopNext s) := by
  obtain ⟨hn, ht, pc, src, dst, count⟩ := inv
  have hp : s.pc = p := by simpa using pc
  have heq : BitVec.ofNat 64 (n + 1) = 1 ↔ n = 0 := by
    have hsmall : n + 1 < 2 ^ 64 := by omega
    constructor
    · intro h
      have value := congrArg BitVec.toNat h
      change (n + 1) % 2 ^ 64 = 1 at value
      rw [Nat.mod_eq_of_lt hsmall] at value
      omega
    · intro h
      subst n
      rfl
  refine ⟨by omega, ht, ?_, ?_, ?_, ?_⟩
  · rw [copy_next_pc, count, hp]
    simp only [heq]
  · rw [(Expansion.loop_next_regs s).1, src]
    change BitVec.ofNat 64 (source + 8 * (total - (n + 1))) + BitVec.ofNat 64 8 = _
    rw [← BitVec.ofNat_add]
    congr 1
    omega
  · rw [(Expansion.loop_next_regs s).2.1, dst]
    change BitVec.ofNat 64 (destination + 8 * (total - (n + 1))) + BitVec.ofNat 64 8 = _
    rw [← BitVec.ofNat_add]
    congr 1
    omega
  · rw [(Expansion.loop_next_regs s).2.2, count, BitVec.ofNat_add]
    exact BitVec.add_sub_cancel _ _

theorem copy_accesses (p : Word) (source destination total n : Nat) (s : MachineState)
    (inv : CopyInvariant p source destination total (n + 1) s)
    (srcbound : source + 8 * total ≤ MEMORY_BYTES)
    (dstbound : destination + 8 * total ≤ MEMORY_BYTES)
    (srcalign : source % 8 = 0) (dstalign : destination % 8 = 0) :
    accessValid (s.getReg .x6) 8 = true ∧ accessValid (s.getReg .x7) 8 = true := by
  obtain ⟨hn, ht, _, src, dst, _⟩ := inv
  simp only [MEMORY_BYTES] at srcbound dstbound
  have hs : source + 8 * (total - (n + 1)) < 2 ^ 64 := by omega
  have hd : destination + 8 * (total - (n + 1)) < 2 ^ 64 := by omega
  simp [accessValid, rangeValid, src, dst, BitVec.toNat_ofNat,
    MEMORY_BYTES, Nat.add_mod, Nat.mul_mod,
    srcalign, dstalign]
  omega

theorem ordinary_trans (image : Image) (s t u : MachineState) (m n : Nat)
    (first : OrdinarySteps image s m t) (second : OrdinarySteps image t n u) :
    OrdinarySteps image s (n + m) u := by
  induction first with
  | refl => simpa using second
  | step s t v instruction m hf hs block ih =>
    simpa only [Nat.add_assoc] using OrdinarySteps.step s t u instruction (n + m) hf hs (ih second)

/-- Every in-bounds generated copy loop terminates after exactly six instructions per word.
The theorem permits overlapping buffers and arbitrary memory contents. -/
theorem copy_loop (image : Image) (p : Word) (code : CopyCode image p)
    (source destination total n : Nat) (s : MachineState)
    (inv : CopyInvariant p source destination total n s)
    (srcbound : source + 8 * total ≤ MEMORY_BYTES)
    (dstbound : destination + 8 * total ≤ MEMORY_BYTES)
    (srcalign : source % 8 = 0) (dstalign : destination % 8 = 0) :
    ∃ final, OrdinarySteps image s (6 * n) final ∧ CopyInvariant p source destination total 0 final := by
  induction n generalizing s with
  | zero => exact ⟨s, OrdinarySteps.refl _, inv⟩
  | succ n ih =>
    have access := copy_accesses p source destination total n s inv srcbound dstbound srcalign dstalign
    have block := copy_block image p code s (by simpa using inv.2.2.1) access.1 access.2
    obtain ⟨final, tail, done⟩ := ih (Expansion.loopNext s) (copy_invariant_next p source destination total n s inv)
    refine ⟨final, ?_, done⟩
    simpa only [Nat.mul_add, Nat.mul_one] using ordinary_trans image s _ final 6 (6 * n) block tail

/-- info: 'SigGolfCandidate.Hypertree.Keygen.copy_loop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms copy_loop

/-- info: 'SigGolfCandidate.Hypertree.Keygen.hash_then' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms hash_then

end SigGolfCandidate.Hypertree.Keygen
