import SigGolfCandidate.Hypertree.VerifyPrepare
import SigGolfCandidate.Hypertree.SignIndexRefine

namespace SigGolfCandidate.Hypertree.Verifying
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 OracleComp Keygen Signing
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false

def initializeState (s : MachineState) : MachineState :=
  let s := execInstrBr s (.ADDI .x6 .x0 0)
  let s := execInstrBr s (.LUI .x28 0x80)
  let s := execInstrBr s (.ADDI .x28 .x28 0x440)
  let s := execInstrBr s (.SD .x28 .x6 0)
  let s := execInstrBr s (.LUI .x6 0x3c)
  let s := execInstrBr s (.ADDI .x6 .x6 0xc50)
  let s := execInstrBr s (.LUI .x28 0x80)
  let s := execInstrBr s (.ADDI .x28 .x28 0x448)
  execInstrBr s (.SD .x28 .x6 0)

theorem initializeState_block (s : MachineState) (pc : s.pc = 0x1000) :
    OrdinarySteps verify s 9 (initializeState s) := by
  let s1 := execInstrBr s (.ADDI .x6 .x0 0)
  let s2 := execInstrBr s1 (.LUI .x28 0x80)
  let s3 := execInstrBr s2 (.ADDI .x28 .x28 0x440)
  let s4 := execInstrBr s3 (.SD .x28 .x6 0)
  let s5 := execInstrBr s4 (.LUI .x6 0x3c)
  let s6 := execInstrBr s5 (.ADDI .x6 .x6 0xc50)
  let s7 := execInstrBr s6 (.LUI .x28 0x80)
  let s8 := execInstrBr s7 (.ADDI .x28 .x28 0x448)
  let s9 := execInstrBr s8 (.SD .x28 .x6 0)
  apply OrdinarySteps.step s s1 _ (.base (.ADDI .x6 .x0 0)) 8
  · have hp : s.pc = 0x1000 := by simp [execInstrBr, pc]
    simp only [fetch, hp]; decide
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.LUI .x28 0x80)) 7
  · have hp : s1.pc = 0x1004 := by simp [s1, execInstrBr, pc]
    simp only [fetch, hp]; decide
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.ADDI .x28 .x28 0x440)) 6
  · have hp : s2.pc = 0x1008 := by simp [s1, s2, execInstrBr, pc]
    simp only [fetch, hp]; decide
  · rfl
  apply OrdinarySteps.step s3 s4 _ (.base (.SD .x28 .x6 0)) 5
  · have hp : s3.pc = 0x100c := by simp [s1, s2, s3, execInstrBr, pc]
    simp only [fetch, hp]; decide
  · simp [s1, s2, s3, s4, ordinaryStep, memoryArgumentsValid, execInstrBr, signExtend12, accessValid, rangeValid, MEMORY_BYTES, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s4 s5 _ (.base (.LUI .x6 0x3c)) 4
  · have hp : s4.pc = 0x1010 := by simp [s1, s2, s3, s4, execInstrBr, pc]
    simp only [fetch, hp]; decide
  · rfl
  apply OrdinarySteps.step s5 s6 _ (.base (.ADDI .x6 .x6 0xc50)) 3
  · have hp : s5.pc = 0x1014 := by simp [s1, s2, s3, s4, s5, execInstrBr, pc]
    simp only [fetch, hp]; decide
  · rfl
  apply OrdinarySteps.step s6 s7 _ (.base (.LUI .x28 0x80)) 2
  · have hp : s6.pc = 0x1018 := by simp [s1, s2, s3, s4, s5, s6, execInstrBr, pc]
    simp only [fetch, hp]; decide
  · rfl
  apply OrdinarySteps.step s7 s8 _ (.base (.ADDI .x28 .x28 0x448)) 1
  · have hp : s7.pc = 0x101c := by simp [s1, s2, s3, s4, s5, s6, s7, execInstrBr, pc]
    simp only [fetch, hp]; decide
  · rfl
  apply OrdinarySteps.step s8 s9 _ (.base (.SD .x28 .x6 0)) 0
  · have hp : s8.pc = 0x1020 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, execInstrBr, pc]
    simp only [fetch, hp]; decide
  · simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, ordinaryStep, memoryArgumentsValid, execInstrBr, signExtend12, accessValid, rangeValid, MEMORY_BYTES, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  exact OrdinarySteps.refl _

theorem initializeState_pc (s : MachineState) : (initializeState s).pc = s.pc + 36 := by
  simp [initializeState, execInstrBr, BitVec.add_assoc]

theorem initializeState_mem (s : MachineState) (a : Word) :
    (initializeState s).getMem a = if a = 0x80448 then 0x3bc50 else if a = 0x80440 then 0 else s.getMem a := by
  simp [initializeState, execInstrBr, signExtend12, Expansion.mem_setMem,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]

theorem initializeState_byte (s : MachineState) (base i : Nat)
    (aligned : base % 8 = 0) (bound : base + i < 0x80000) :
    (initializeState s).getByte (BitVec.ofNat 64 (base + i)) = s.getByte (BitVec.ofNat 64 (base + i)) := by
  rw [getByte_word _ base i aligned (by omega), getByte_word s base i aligned (by omega), initializeState_mem]
  have small : base + 8 * (i / 8) < 2 ^ 64 := by omega
  have value : (wordAddress base (i / 8)).toNat = base + 8 * (i / 8) := Nat.mod_eq_of_lt small
  have ne1 : wordAddress base (i / 8) ≠ 0x80448 := by
    intro h
    have eq := congrArg BitVec.toNat h
    rw [value] at eq
    change base + 8 * (i / 8) = 0x80448 at eq
    omega
  have ne2 : wordAddress base (i / 8) ≠ 0x80440 := by
    intro h
    have eq := congrArg BitVec.toNat h
    rw [value] at eq
    change base + 8 * (i / 8) = 0x80440 at eq
    omega
  rw [if_neg ne1, if_neg ne2]

def indexInputByte (s : MachineState) (i : Fin 112) : Byte :=
  extractByte (indexInputWord s ⟨i.val / 8, by have := i.isLt; omega⟩) (i.val % 8)

theorem indexInputByte_spec (s : MachineState) (i : Fin 112) :
    indexInputByte s i =
      if i.val = 0 then 5 else if i.val < 32 then 0 else
        if i.val < 48 then s.getByte (BitVec.ofNat 64 (0x40 + (i.val - 32)))
        else if i.val < 80 then s.getByte (BitVec.ofNat 64 (i.val - 48))
        else s.getByte (BitVec.ofNat 64 (0x3bc30 + (i.val - 80))) := by
  fin_cases i <;> first | rfl | simp [indexInputByte, indexInputWord, extractByte]

theorem prepared_index_bytes (original ready : MachineState)
    (words : ∀ i : Fin 14, ready.getMem (wordAddress 0x80000 i.val) = indexInputWord original i)
    (i : Fin 112) :
    ready.getByte (BitVec.ofNat 64 (0x80000 + i.val)) = indexInputByte original i := by
  rw [getByte_word ready 0x80000 i.val (by decide) (by have := i.isLt; omega)]
  exact congrArg (fun word => extractByte word (i.val % 8))
    (words ⟨i.val / 8, by have := i.isLt; omega⟩)

theorem index_query (original ready : MachineState) (pk : PublicKey) (message : Message) (r : Bytes 32)
    (hpk : ∀ i, i < 16 → original.getByte (BitVec.ofNat 64 (0x40 + i)) = pk.extractLsb' (8 * i) 8)
    (hmessage : ∀ i, i < 32 → original.getByte (BitVec.ofNat 64 i) = message.extractLsb' (8 * i) 8)
    (hr : ∀ i, i < 32 → original.getByte (BitVec.ofNat 64 (0x3bc30 + i)) = r.extractLsb' (8 * i) 8)
    (words : ∀ i : Fin 14, ready.getMem (wordAddress 0x80000 i.val) = indexInputWord original i) :
    hashInput (indexHashState ready) = Reference.packed (indexPayload pk message r) := by
  apply Serialization.hashInput_of_list (indexHashState ready) 0x80000 (indexPayload pk message r)
  · exact (indexHashState_regs ready).2.1
  · rw [(indexHashState_regs ready).2.2.1, indexPayload_length]; rfl
  · intro i hi
    have bound : i < 112 := by simpa using hi
    rw [indexHashState_byte, prepared_index_bytes original ready words ⟨i, bound⟩,
      indexInputByte_spec, indexPayload_byte pk message r ⟨i, bound⟩]
    dsimp only
    split_ifs with h0 h32 h48 h80
    · rfl
    · rfl
    · exact hpk (i - 32) (by omega)
    · exact hmessage (i - 48) (by omega)
    · exact hr (i - 80) (by omega)

theorem index_refines (hash : Hash) (s : MachineState) (pk : PublicKey) (message : Message) (r : Bytes 32)
    (pc : s.pc = 0x1024)
    (hpk : ∀ i, i < 16 → s.getByte (BitVec.ofNat 64 (0x40 + i)) = pk.extractLsb' (8 * i) 8)
    (hmessage : ∀ i, i < 32 → s.getByte (BitVec.ofNat 64 i) = message.extractLsb' (8 * i) 8)
    (hr : ∀ i, i < 32 → s.getByte (BitVec.ofNat 64 (0x3bc30 + i)) = r.extractLsb' (8 * i) 8) :
    ∃ final, Trace hash verify s 121 136 1 2 final ∧ final.pc = 0x1148 ∧
      readBuffer final 0x80408 19 = Reference.indexOf hash pk message r := by
  obtain ⟨ready, prepare, readypc, words, _⟩ := index_prepare s pc
  obtain ⟨final, trace, finalpc, low, high⟩ := index_trace hash ready readypc
  have query := index_query s ready pk message r hpk hmessage hr words
  refine ⟨final, prepare.trace.trans trace, finalpc, ?_⟩
  rw [read_index_words final _ low high, query]
  rfl

/-- Exact verifier entry through randomized-index recovery, for arbitrary witness bytes. -/
theorem entry_index_refines (hash : Hash) (s : MachineState) (pk : PublicKey) (message : Message) (r : Bytes 32)
    (pc : s.pc = 0x1000)
    (hpk : ∀ i, i < 16 → s.getByte (BitVec.ofNat 64 (0x40 + i)) = pk.extractLsb' (8 * i) 8)
    (hmessage : ∀ i, i < 32 → s.getByte (BitVec.ofNat 64 i) = message.extractLsb' (8 * i) 8)
    (hr : ∀ i, i < 32 → s.getByte (BitVec.ofNat 64 (0x3bc30 + i)) = r.extractLsb' (8 * i) 8) :
    ∃ final, Trace hash verify s 130 145 1 2 final ∧ final.pc = 0x1148 ∧
      readBuffer final 0x80408 19 = Reference.indexOf hash pk message r := by
  have initpc : (initializeState s).pc = 0x1024 := by simp [initializeState_pc, pc]
  obtain ⟨final, trace, finalpc, value⟩ := index_refines hash (initializeState s) pk message r initpc
    (fun i hi => (initializeState_byte s 0x40 i (by decide) (by omega)).trans (hpk i hi))
    (fun i hi => (by simpa only [Nat.zero_add] using initializeState_byte s 0 i (by decide) (by omega) :
      (initializeState s).getByte (BitVec.ofNat 64 i) = s.getByte (BitVec.ofNat 64 i)).trans (hmessage i hi))
    (fun i hi => (initializeState_byte s 0x3bc30 i (by decide) (by omega)).trans (hr i hi))
  exact ⟨final, (initializeState_block s pc).trace.trans trace, finalpc, value⟩

/-- info: 'SigGolfCandidate.Hypertree.Verifying.entry_index_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms entry_index_refines

end SigGolfCandidate.Hypertree.Verifying
