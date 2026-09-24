import SigGolfCandidate.Hypertree.Expand
import SigGolfCandidate.Memory
import RiscvZkvm.Rv64.Logic.MemRegion

namespace SigGolfCandidate.Hypertree.Expansion
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64

private def source (i : Nat) : Word := BitVec.ofNat 64 (0x20060 + 8 * i)
private def destination (i : Nat) : Word := BitVec.ofNat 64 (0x3d3b0 + 8 * i)

private theorem source_value (i : Nat) (hi : i < 14954) :
    (source i).toNat = 0x20060 + 8 * i := by
  have bound : 0x20060 + 8 * i < 2 ^ 64 := by omega
  exact Nat.mod_eq_of_lt bound

private theorem destination_value (i : Nat) (hi : i < 14954) :
    (destination i).toNat = 0x3d3b0 + 8 * i := by
  have bound : 0x3d3b0 + 8 * i < 2 ^ 64 := by omega
  exact Nat.mod_eq_of_lt bound

private theorem disjoint (i j : Nat) (hi : i < 14954) (hj : j < 14954) :
    source i ≠ destination j := by
  intro h
  have eq := congrArg BitVec.toNat h
  rw [source_value i hi, destination_value j hj] at eq
  omega

private theorem destination_injective (i j : Nat) (hi : i < 14954) (hj : j < 14954)
    (ne : i ≠ j) : destination i ≠ destination j := by
  intro h
  have eq := congrArg BitVec.toNat h
  rw [destination_value i hi, destination_value j hj] at eq
  omega

/-- Source words remain intact and the completed destination prefix matches them. -/
private def Copied (original : MachineState) (n : Nat) (s : MachineState) : Prop :=
  (∀ i, i < 14954 → s.getMem (source i) = original.getMem (source i)) ∧
  (∀ i, i < 14954 - n → s.getMem (destination i) = original.getMem (source i))

private theorem copy_next (original s : MachineState) (n : Nat)
    (inv : Invariant (n + 1) s) (copied : Copied original (n + 1) s) :
    Copied original n (loopNext s) := by
  obtain ⟨hn, _, src, dst, _⟩ := inv
  have hindex : 14954 - (n + 1) < 14954 := by omega
  change s.getReg .x6 = source (14954 - (n + 1)) at src
  change s.getReg .x7 = destination (14954 - (n + 1)) at dst
  constructor
  · intro i hi
    rw [loop_next_mem, dst, if_neg (disjoint i _ hi hindex)]
    exact copied.1 i hi
  · intro i hi
    have hib : i < 14954 := by omega
    by_cases heq : i = 14954 - (n + 1)
    · subst i
      rw [loop_next_mem, dst, src, if_pos rfl]
      exact copied.1 _ hindex
    · rw [loop_next_mem, dst, if_neg (destination_injective i _ hib hindex heq)]
      exact copied.2 i (by omega)

private theorem finish_mem (s : MachineState) (a : Word) :
    (finishState s).getMem a = s.getMem a := by simp [finishState, execInstrBr]

private theorem prefix_mem (s : MachineState) (a : Word) :
    (prefixState s).getMem a = s.getMem a := by simp [prefixState, execInstrBr]

private theorem loop_copies (hash : Hash) (original : MachineState) (n : Nat) (s : MachineState)
    (inv : Invariant n s) (copied : Copied original n s) :
    ∃ final, Executes hash expand s (6 * n + 3) ⟨.success, final, 6 * n + 3, 0, 0⟩ ∧
      ∀ i, i < 14954 → final.getMem (destination i) = original.getMem (source i) := by
  induction n generalizing s with
  | zero =>
    refine ⟨finishState s, finish hash s (by simpa using inv.2.1), ?_⟩
    intro i hi
    rw [finish_mem]
    exact copied.2 i hi
  | succ n ih =>
    obtain ⟨final, trace, output⟩ := ih (loopNext s) (loop_invariant n s inv) (copy_next original s n inv copied)
    refine ⟨final, ?_, output⟩
    have block := loop_block s (by simpa using inv.2.1)
      (loop_accesses n s inv).1 (loop_accesses n s inv).2
    have hsteps : 6 * n + 3 + 6 = 6 * (n + 1) + 3 := by omega
    have hcycles : 6 + (6 * n + 3) = 6 * (n + 1) + 3 := by omega
    simpa only [Execution.charge, hsteps, hcycles, Nat.zero_add] using block.then_executes trace

/-- Every one of the 14,954 signature words is copied exactly by the submitted bytecode. -/
theorem copies_words (hash : Hash) (s : MachineState) (pc : s.pc = 0x1000) :
    ∃ final, Executes hash expand s 89733 ⟨.success, final, 89733, 0, 0⟩ ∧
      ∀ i, i < 14954 →
        final.getMem (BitVec.ofNat 64 (0x3d3b0 + 8 * i)) = s.getMem (BitVec.ofNat 64 (0x20060 + 8 * i)) := by
  have initial : Copied s 14954 (prefixState s) := by
    constructor
    · intro i _
      exact prefix_mem s _
    · intro i hi
      omega
  obtain ⟨final, trace, output⟩ := loop_copies hash s 14954 (prefixState s) (prefix_invariant s pc) initial
  refine ⟨final, ?_, output⟩
  have hsteps : (6 * 14954 + 3) + 6 = 89733 := by decide
  have hcycles : 6 + (6 * 14954 + 3) = 89733 := by decide
  simpa only [Execution.charge, hsteps, hcycles, Nat.zero_add] using (prefix_block s pc).then_executes trace

private theorem copied_bytes (original final : MachineState)
    (words : ∀ i, i < 14954 → final.getMem (destination i) = original.getMem (source i))
    (i : Nat) (hi : i < 119632) :
    final.getByte (BitVec.ofNat 64 (0x3d3b0 + i)) = original.getByte (BitVec.ofNat 64 (0x20060 + i)) := by
  have dstAlign : (BitVec.ofNat 64 0x3d3b0).toNat % 8 = 0 := by decide
  have srcAlign : (BitVec.ofNat 64 0x20060).toNat % 8 = 0 := by decide
  have dstBound : (BitVec.ofNat 64 0x3d3b0).toNat + i < 2 ^ 64 := by change 250800 + i < 2 ^ 64; omega
  have srcBound : (BitVec.ofNat 64 0x20060).toNat + i < 2 ^ 64 := by change 131168 + i < 2 ^ 64; omega
  simp only [MachineState.getByte, BitVec.ofNat_add,
    alignToDword_add_ofNat_of_aligned dstAlign dstBound,
    alignToDword_add_ofNat_of_aligned srcAlign srcBound,
    byteOffset_add_ofNat_of_aligned dstAlign dstBound,
    byteOffset_add_ofNat_of_aligned srcAlign srcBound]
  apply congrArg (fun word => extractByte word (i % 8))
  simpa only [destination, source, BitVec.ofNat_add] using words (i / 8) (by omega)

private theorem foldl_eq_on {α β : Type} (xs : List α) (f g : β → α → β)
    (same : ∀ x, x ∈ xs → ∀ acc, f acc x = g acc x) (acc : β) :
    xs.foldl f acc = xs.foldl g acc := by
  induction xs generalizing acc with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.foldl_cons]
    rw [same x (by simp)]
    exact ih (fun y hy => same y (by simp [hy])) _

/-- The source and destination have the same bytes under the organizer's output decoder. -/
theorem copies_buffer (hash : Hash) (s : MachineState) (pc : s.pc = 0x1000) :
    ∃ final, Executes hash expand s 89733 ⟨.success, final, 89733, 0, 0⟩ ∧
      readBuffer final 0x3d3b0 signatureBytes = readBuffer s 0x20060 signatureBytes := by
  obtain ⟨final, trace, words⟩ := copies_words hash s pc
  refine ⟨final, trace, ?_⟩
  unfold readBuffer
  apply congrArg (BitVec.ofNat (8 * signatureBytes))
  apply foldl_eq_on
  intro i hi acc
  rw [copied_bytes s final words i (by simpa [signatureBytes] using hi)]

/-- Expansion preserves the signature buffer through the official submission interface. -/
theorem run_copies_buffer (hash : Hash) (input : Input submission.sizes .expand) :
    ∃ initial, initialState submission .expand input = some initial ∧
      (submission.runWith hash .expand input).value = some (readBuffer initial 0x20060 signatureBytes) := by
  obtain ⟨initial, loaded, pc⟩ := initialState_exists submission admitted .expand input
  obtain ⟨final, trace, same⟩ := copies_buffer hash initial pc
  have run := runWith_of_executes submission hash .expand input initial 89733
    ⟨.success, final, 89733, 0, 0⟩ loaded trace (by decide)
  refine ⟨initial, loaded, ?_⟩
  rw [run]
  change some (readBuffer final (witnessBase submission.sizes) signatureBytes) = _
  rw [show witnessBase submission.sizes = 0x3d3b0 from by decide]
  exact congrArg some same

set_option maxRecDepth 4096 in
/-- Expansion returns the exact typed signature through the official loader and decoder. -/
theorem run_identity (hash : Hash) (input : Input submission.sizes .expand) :
    (submission.runWith hash .expand input).value = some input.2.2 := by
  rcases input with ⟨message, pk, signature⟩
  obtain ⟨initial, loaded, output⟩ := run_copies_buffer hash (message, pk, signature)
  rw [output]
  apply congrArg some
  unfold initialState at loaded
  rw [if_pos (admitted.2 .expand)] at loaded
  cases Option.some.inj loaded
  dsimp only [inputBuffers, Riscv.standardLayout, Layout.message, Layout.secretKey, Layout.publicKey, Layout.cache, Layout.signature, Layout.witness, List.foldl_cons, List.foldl_nil]
  rw [Memory.readBuffer_setReg]
  exact Memory.read_write_buffer _ 0x20060 signatureBytes signature (by decide) (by decide)

/-- info: 'SigGolfCandidate.Hypertree.Expansion.run_identity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms run_identity

/-- info: 'SigGolfCandidate.Hypertree.Expansion.copies_words' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms copies_words

/-- info: 'SigGolfCandidate.Hypertree.Expansion.run_copies_buffer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms run_copies_buffer

end SigGolfCandidate.Hypertree.Expansion
