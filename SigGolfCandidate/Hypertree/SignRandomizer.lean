import SigGolfCandidate.Hypertree.SignCopy
import SigGolfCandidate.Hypertree.KeygenTrace

namespace SigGolfCandidate.Hypertree.Signing
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 OracleComp Keygen
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false

def randomizerHashState (s : MachineState) : MachineState :=
  let s := execInstrBr s (.LUI .x10 0x80)
  let s := execInstrBr s (.ADDI .x10 .x10 0)
  let s := execInstrBr s (.ADDI .x11 .x0 768)
  let s := execInstrBr s (.LUI .x12 0x80)
  let s := execInstrBr s (.ADDI .x12 .x12 0x300)
  execInstrBr s (.ADDI .x5 .x0 1)

theorem randomizerHashState_block (s : MachineState) (pc : s.pc = 0x10b4) :
    OrdinarySteps sign s 6 (randomizerHashState s) := by
  let s1 := execInstrBr s (.LUI .x10 0x80)
  let s2 := execInstrBr s1 (.ADDI .x10 .x10 0)
  let s3 := execInstrBr s2 (.ADDI .x11 .x0 768)
  let s4 := execInstrBr s3 (.LUI .x12 0x80)
  let s5 := execInstrBr s4 (.ADDI .x12 .x12 0x300)
  let s6 := execInstrBr s5 (.ADDI .x5 .x0 1)
  apply OrdinarySteps.step s s1 _ (.base (.LUI .x10 0x80)) 5
  · have hp : s.pc = 0x10b4 := by simp [execInstrBr, pc]
    simp only [fetch, hp]; decide
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.ADDI .x10 .x10 0)) 4
  · have hp : s1.pc = 0x10b8 := by simp [s1, execInstrBr, pc]
    simp only [fetch, hp]; decide
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.ADDI .x11 .x0 768)) 3
  · have hp : s2.pc = 0x10bc := by simp [s1, s2, execInstrBr, pc]
    simp only [fetch, hp]; decide
  · rfl
  apply OrdinarySteps.step s3 s4 _ (.base (.LUI .x12 0x80)) 2
  · have hp : s3.pc = 0x10c0 := by simp [s1, s2, s3, execInstrBr, pc]
    simp only [fetch, hp]; decide
  · rfl
  apply OrdinarySteps.step s4 s5 _ (.base (.ADDI .x12 .x12 0x300)) 1
  · have hp : s4.pc = 0x10c4 := by simp [s1, s2, s3, s4, execInstrBr, pc]
    simp only [fetch, hp]; decide
  · rfl
  apply OrdinarySteps.step s5 s6 _ (.base (.ADDI .x5 .x0 1)) 0
  · have hp : s5.pc = 0x10c8 := by simp [s1, s2, s3, s4, s5, execInstrBr, pc]
    simp only [fetch, hp]; decide
  · rfl
  exact OrdinarySteps.refl _

def randomizerCopyState (s : MachineState) : MachineState :=
  let s := execInstrBr s (.LUI .x6 0x80)
  let s := execInstrBr s (.ADDI .x6 .x6 0x300)
  let s := execInstrBr s (.LUI .x7 0x20)
  let s := execInstrBr s (.ADDI .x7 .x7 0x60)
  execInstrBr s (.ADDI .x10 .x0 4)

theorem randomizerCopyState_block (s : MachineState) (pc : s.pc = 0x10d0) :
    OrdinarySteps sign s 5 (randomizerCopyState s) := by
  let s1 := execInstrBr s (.LUI .x6 0x80)
  let s2 := execInstrBr s1 (.ADDI .x6 .x6 0x300)
  let s3 := execInstrBr s2 (.LUI .x7 0x20)
  let s4 := execInstrBr s3 (.ADDI .x7 .x7 0x60)
  let s5 := execInstrBr s4 (.ADDI .x10 .x0 4)
  apply OrdinarySteps.step s s1 _ (.base (.LUI .x6 0x80)) 4
  · have hp : s.pc = 0x10d0 := by simp [execInstrBr, pc]
    simp only [fetch, hp]; decide
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.ADDI .x6 .x6 0x300)) 3
  · have hp : s1.pc = 0x10d4 := by simp [s1, execInstrBr, pc]
    simp only [fetch, hp]; decide
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.LUI .x7 0x20)) 2
  · have hp : s2.pc = 0x10d8 := by simp [s1, s2, execInstrBr, pc]
    simp only [fetch, hp]; decide
  · rfl
  apply OrdinarySteps.step s3 s4 _ (.base (.ADDI .x7 .x7 0x60)) 1
  · have hp : s3.pc = 0x10dc := by simp [s1, s2, s3, execInstrBr, pc]
    simp only [fetch, hp]; decide
  · rfl
  apply OrdinarySteps.step s4 s5 _ (.base (.ADDI .x10 .x0 4)) 0
  · have hp : s4.pc = 0x10e0 := by simp [s1, s2, s3, s4, execInstrBr, pc]
    simp only [fetch, hp]; decide
  · rfl
  exact OrdinarySteps.refl _

theorem randomizerHashState_regs (s : MachineState) :
    (randomizerHashState s).getReg .x5 = 1 ∧
    (randomizerHashState s).getReg .x10 = 0x80000 ∧
    (randomizerHashState s).getReg .x11 = 768 ∧
    (randomizerHashState s).getReg .x12 = 0x80300 := by
  simp [randomizerHashState, execInstrBr, signExtend12,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]

theorem randomizerHashState_pc (s : MachineState) :
    (randomizerHashState s).pc = s.pc + 24 := by
  simp [randomizerHashState, execInstrBr, BitVec.add_assoc]

theorem randomizerCopyState_mem (s : MachineState) (a : Word) :
    (randomizerCopyState s).getMem a = s.getMem a := by
  simp [randomizerCopyState, execInstrBr]

theorem randomizerCopyState_invariant (s : MachineState) (pc : s.pc = 0x10d0) :
    CopyInvariant 0x10e4 0x80300 0x20060 4 4 (randomizerCopyState s) := by
  simp [CopyInvariant, randomizerCopyState, execInstrBr, signExtend12, pc,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]

theorem randomizer_copy_code : CopyCode sign 0x10e4 := by decide

/-- All four words of the hash answer are copied to the serialized signature prefix. -/
theorem randomizer_copy (s : MachineState) (pc : s.pc = 0x10d0) :
    ∃ final, OrdinarySteps sign s 29 final ∧ final.pc = 0x10fc ∧
      ∀ i, i < 4 → final.getMem (wordAddress 0x20060 i) = s.getMem (wordAddress 0x80300 i) := by
  obtain ⟨final, loop, inv, output, _⟩ := copy_all sign 0x10e4 randomizer_copy_code
    0x80300 0x20060 4 (randomizerCopyState s) (randomizerCopyState_invariant s pc)
    (by decide) (by decide) (by decide) (by decide) (by decide)
  refine ⟨final, ?_, ?_, ?_⟩
  · exact ordinary_trans sign s _ final 5 24 (randomizerCopyState_block s pc) loop
  · simpa [CopyInvariant] using inv.2.2.1
  · intro i hi
    simpa only [randomizerCopyState_mem] using output i hi

theorem hash_answer_word (s : MachineState) (answer : BitVec 256)
    (dst : s.getReg .x12 = 0x80300) (i : Fin 4) :
    (writeHash s answer).getMem (wordAddress 0x80300 i.val) =
      answer.extractLsb' (64 * i.val) 64 := by
  fin_cases i <;> simp [writeHash, dst, wordAddress, MachineState.writeWords,
    Expansion.mem_setMem]

/-- The actual randomizer HASH and output-copy block. For every oracle and memory
contents it writes the full 256-bit oracle answer to the signature prefix in 51 cycles,
with exactly one oracle call and two compressions. The query is the exact protected
interpreter's hashInput; identifying its payload is a separate prefix invariant. -/
theorem randomizer_trace (hash : Hash) (s : MachineState) (pc : s.pc = 0x10b4) :
    ∃ final, Trace hash sign s 36 51 1 2 final ∧ final.pc = 0x10fc ∧
      ∀ i : Fin 4, final.getMem (wordAddress 0x20060 i.val) =
        (hash (hashInput (randomizerHashState s))).extractLsb' (64 * i.val) 64 := by
  let hs := randomizerHashState s
  have hpc : hs.pc = 0x10cc := by simp [hs, randomizerHashState_pc, pc]
  obtain ⟨service, src, len, dst⟩ := randomizerHashState_regs s
  have hf : fetch sign hs = some (.base .ECALL) := by simp only [fetch, hpc]; decide
  have hv : hashArgumentsValid hs = true := hash_arguments hs 768 src len dst (by decide)
  have hlen : (hashInput hs).1 = 768 := by simp [hashInput, hs, len]
  let answer := hash (hashInput hs)
  have outpc : (writeHash hs answer).pc = 0x10d0 := by simp [hash_pc, hpc]
  obtain ⟨final, copied, finalpc, words⟩ := randomizer_copy (writeHash hs answer) outpc
  have call : Trace hash sign hs 1 16 1 2 (writeHash hs answer) := by
    simpa [hlen, compressions] using Trace.hash hs (writeHash hs answer) 0 0 0 0 hf service hv
      (Trace.refl (writeHash hs answer))
  refine ⟨final, ?_, finalpc, ?_⟩
  · exact ((randomizerHashState_block s pc).trace.trans call).trans copied.trace
  · intro i
    rw [words i.val i.isLt]
    exact hash_answer_word hs answer dst i

/-- info: 'SigGolfCandidate.Hypertree.Signing.randomizer_trace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms randomizer_trace

theorem hash_answer_frame (s : MachineState) (answer : BitVec 256)
    (dst : s.getReg .x12 = 0x80300) (a : Word)
    (outside : ∀ i : Fin 4, a ≠ wordAddress 0x80300 i.val) :
    (writeHash s answer).getMem a = s.getMem a := by
  have h0 : a ≠ 0x80300 := outside 0
  have h1 : a ≠ 0x80308 := outside 1
  have h2 : a ≠ 0x80310 := outside 2
  have h3 : a ≠ 0x80318 := outside 3
  simp only [writeHash, MachineState.getMem_setPC, dst, MachineState.writeWords,
    Expansion.mem_setMem]
  change (if a = 0x80318 then _ else if a = 0x80310 then _ else
    if a = 0x80308 then _ else if a = 0x80300 then _ else s.getMem a) = s.getMem a
  rw [if_neg h3, if_neg h2, if_neg h1, if_neg h0]

/-- The first HASH/copy block also preserves every word outside the answer and
32-byte signature prefix, which includes all secret key, public-key and message inputs. -/
theorem randomizer_trace_frame (hash : Hash) (s : MachineState) (pc : s.pc = 0x10b4) :
    ∃ final, Trace hash sign s 36 51 1 2 final ∧ final.pc = 0x10fc ∧
      (∀ i : Fin 4, final.getMem (wordAddress 0x20060 i.val) =
        (hash (hashInput (randomizerHashState s))).extractLsb' (64 * i.val) 64) ∧
      (∀ a, (∀ i : Fin 4, a ≠ wordAddress 0x20060 i.val) →
        (∀ i : Fin 4, a ≠ wordAddress 0x80300 i.val) → final.getMem a = s.getMem a) := by
  let hs := randomizerHashState s
  have hpc : hs.pc = 0x10cc := by simp [hs, randomizerHashState_pc, pc]
  obtain ⟨service, src, len, dst⟩ := randomizerHashState_regs s
  have hf : fetch sign hs = some (.base .ECALL) := by simp only [fetch, hpc]; decide
  have hv : hashArgumentsValid hs = true := hash_arguments hs 768 src len dst (by decide)
  have hlen : (hashInput hs).1 = 768 := by simp [hashInput, hs, len]
  let answer := hash (hashInput hs)
  have outpc : (writeHash hs answer).pc = 0x10d0 := by simp [hash_pc, hpc]
  obtain ⟨final, loop, inv, output, frame⟩ := copy_all sign 0x10e4 randomizer_copy_code
    0x80300 0x20060 4 (randomizerCopyState (writeHash hs answer))
    (randomizerCopyState_invariant (writeHash hs answer) outpc)
    (by decide) (by decide) (by decide) (by decide) (by decide)
  have copied : OrdinarySteps sign (writeHash hs answer) 29 final :=
    ordinary_trans sign _ _ final 5 24 (randomizerCopyState_block _ outpc) loop
  have call : Trace hash sign hs 1 16 1 2 (writeHash hs answer) := by
    simpa [hlen, compressions] using Trace.hash hs (writeHash hs answer) 0 0 0 0 hf service hv
      (Trace.refl (writeHash hs answer))
  refine ⟨final, ((randomizerHashState_block s pc).trace.trans call).trans copied.trace,
    by simpa [CopyInvariant] using inv.2.2.1, ?_, ?_⟩
  · intro i
    rw [output i.val i.isLt, randomizerCopyState_mem]
    exact hash_answer_word hs answer dst i
  · intro a sigOutside answerOutside
    rw [frame a (fun i hi => sigOutside ⟨i, hi⟩), randomizerCopyState_mem,
      hash_answer_frame hs answer dst a answerOutside]
    simp [hs, randomizerHashState, execInstrBr]

end SigGolfCandidate.Hypertree.Signing
