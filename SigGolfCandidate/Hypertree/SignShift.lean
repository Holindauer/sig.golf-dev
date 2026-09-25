import SigGolfCandidate.Hypertree.SignIndexRefine

namespace SigGolfCandidate.Hypertree.Signing
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false

def shiftIndexState (s : MachineState) : MachineState :=
  let s := execInstrBr s (.LUI .x28 0x80)
  let s := execInstrBr s (.ADDI .x28 .x28 0x408)
  let s := execInstrBr s (.LD .x6 .x28 0)
  let s := execInstrBr s (.LUI .x28 0x80)
  let s := execInstrBr s (.ADDI .x28 .x28 0x410)
  let s := execInstrBr s (.LD .x7 .x28 0)
  let s := execInstrBr s (.LUI .x28 0x80)
  let s := execInstrBr s (.ADDI .x28 .x28 0x418)
  let s := execInstrBr s (.LD .x10 .x28 0)
  let s := execInstrBr s (.ANDI .x11 .x6 1)
  let s := execInstrBr s (.LUI .x28 0x80)
  let s := execInstrBr s (.ADDI .x28 .x28 0x420)
  let s := execInstrBr s (.SD .x28 .x11 0)
  let s := execInstrBr s (.SRLI .x6 .x6 1)
  let s := execInstrBr s (.SLLI .x11 .x7 63)
  let s := execInstrBr s (.ADD .x6 .x6 .x11)
  let s := execInstrBr s (.LUI .x28 0x80)
  let s := execInstrBr s (.ADDI .x28 .x28 0x408)
  let s := execInstrBr s (.SD .x28 .x6 0)
  let s := execInstrBr s (.SRLI .x7 .x7 1)
  let s := execInstrBr s (.SLLI .x11 .x10 63)
  let s := execInstrBr s (.ADD .x7 .x7 .x11)
  let s := execInstrBr s (.LUI .x28 0x80)
  let s := execInstrBr s (.ADDI .x28 .x28 0x410)
  let s := execInstrBr s (.SD .x28 .x7 0)
  let s := execInstrBr s (.SRLI .x10 .x10 1)
  let s := execInstrBr s (.LUI .x28 0x80)
  let s := execInstrBr s (.ADDI .x28 .x28 0x418)
  execInstrBr s (.SD .x28 .x10 0)

theorem shiftIndexState_block (s : MachineState) (pc : s.pc = 0x1220) :
    OrdinarySteps sign s 29 (shiftIndexState s) := by
  let s1 := execInstrBr s (.LUI .x28 0x80)
  let s2 := execInstrBr s1 (.ADDI .x28 .x28 0x408)
  let s3 := execInstrBr s2 (.LD .x6 .x28 0)
  let s4 := execInstrBr s3 (.LUI .x28 0x80)
  let s5 := execInstrBr s4 (.ADDI .x28 .x28 0x410)
  let s6 := execInstrBr s5 (.LD .x7 .x28 0)
  let s7 := execInstrBr s6 (.LUI .x28 0x80)
  let s8 := execInstrBr s7 (.ADDI .x28 .x28 0x418)
  let s9 := execInstrBr s8 (.LD .x10 .x28 0)
  let s10 := execInstrBr s9 (.ANDI .x11 .x6 1)
  let s11 := execInstrBr s10 (.LUI .x28 0x80)
  let s12 := execInstrBr s11 (.ADDI .x28 .x28 0x420)
  let s13 := execInstrBr s12 (.SD .x28 .x11 0)
  let s14 := execInstrBr s13 (.SRLI .x6 .x6 1)
  let s15 := execInstrBr s14 (.SLLI .x11 .x7 63)
  let s16 := execInstrBr s15 (.ADD .x6 .x6 .x11)
  let s17 := execInstrBr s16 (.LUI .x28 0x80)
  let s18 := execInstrBr s17 (.ADDI .x28 .x28 0x408)
  let s19 := execInstrBr s18 (.SD .x28 .x6 0)
  let s20 := execInstrBr s19 (.SRLI .x7 .x7 1)
  let s21 := execInstrBr s20 (.SLLI .x11 .x10 63)
  let s22 := execInstrBr s21 (.ADD .x7 .x7 .x11)
  let s23 := execInstrBr s22 (.LUI .x28 0x80)
  let s24 := execInstrBr s23 (.ADDI .x28 .x28 0x410)
  let s25 := execInstrBr s24 (.SD .x28 .x7 0)
  let s26 := execInstrBr s25 (.SRLI .x10 .x10 1)
  let s27 := execInstrBr s26 (.LUI .x28 0x80)
  let s28 := execInstrBr s27 (.ADDI .x28 .x28 0x418)
  let s29 := execInstrBr s28 (.SD .x28 .x10 0)
  apply OrdinarySteps.step s s1 _ (.base (.LUI .x28 0x80)) 28
  · have hp : s.pc = 0x1220 := by simp [execInstrBr, pc]
    simp only [fetch, hp]; decide
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.ADDI .x28 .x28 0x408)) 27
  · have hp : s1.pc = 0x1224 := by simp [s1, execInstrBr, pc]
    simp only [fetch, hp]; decide
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.LD .x6 .x28 0)) 26
  · have hp : s2.pc = 0x1228 := by simp [s1, s2, execInstrBr, pc]
    simp only [fetch, hp]; decide
  · simp [s1, s2, s3, ordinaryStep, memoryArgumentsValid, execInstrBr, signExtend12, accessValid, rangeValid, MEMORY_BYTES, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s3 s4 _ (.base (.LUI .x28 0x80)) 25
  · have hp : s3.pc = 0x122c := by simp [s1, s2, s3, execInstrBr, pc]
    simp only [fetch, hp]; decide
  · rfl
  apply OrdinarySteps.step s4 s5 _ (.base (.ADDI .x28 .x28 0x410)) 24
  · have hp : s4.pc = 0x1230 := by simp [s1, s2, s3, s4, execInstrBr, pc]
    simp only [fetch, hp]; decide
  · rfl
  apply OrdinarySteps.step s5 s6 _ (.base (.LD .x7 .x28 0)) 23
  · have hp : s5.pc = 0x1234 := by simp [s1, s2, s3, s4, s5, execInstrBr, pc]
    simp only [fetch, hp]; decide
  · simp [s1, s2, s3, s4, s5, s6, ordinaryStep, memoryArgumentsValid, execInstrBr, signExtend12, accessValid, rangeValid, MEMORY_BYTES, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s6 s7 _ (.base (.LUI .x28 0x80)) 22
  · have hp : s6.pc = 0x1238 := by simp [s1, s2, s3, s4, s5, s6, execInstrBr, pc]
    simp only [fetch, hp]; decide
  · rfl
  apply OrdinarySteps.step s7 s8 _ (.base (.ADDI .x28 .x28 0x418)) 21
  · have hp : s7.pc = 0x123c := by simp [s1, s2, s3, s4, s5, s6, s7, execInstrBr, pc]
    simp only [fetch, hp]; decide
  · rfl
  apply OrdinarySteps.step s8 s9 _ (.base (.LD .x10 .x28 0)) 20
  · have hp : s8.pc = 0x1240 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, execInstrBr, pc]
    simp only [fetch, hp]; decide
  · simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, ordinaryStep, memoryArgumentsValid, execInstrBr, signExtend12, accessValid, rangeValid, MEMORY_BYTES, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s9 s10 _ (.base (.ANDI .x11 .x6 1)) 19
  · have hp : s9.pc = 0x1244 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, execInstrBr, pc]
    simp only [fetch, hp]; decide
  · rfl
  apply OrdinarySteps.step s10 s11 _ (.base (.LUI .x28 0x80)) 18
  · have hp : s10.pc = 0x1248 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, execInstrBr, pc]
    simp only [fetch, hp]; decide
  · rfl
  apply OrdinarySteps.step s11 s12 _ (.base (.ADDI .x28 .x28 0x420)) 17
  · have hp : s11.pc = 0x124c := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, execInstrBr, pc]
    simp only [fetch, hp]; decide
  · rfl
  apply OrdinarySteps.step s12 s13 _ (.base (.SD .x28 .x11 0)) 16
  · have hp : s12.pc = 0x1250 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, execInstrBr, pc]
    simp only [fetch, hp]; decide
  · simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, ordinaryStep, memoryArgumentsValid, execInstrBr, signExtend12, accessValid, rangeValid, MEMORY_BYTES, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s13 s14 _ (.base (.SRLI .x6 .x6 1)) 15
  · have hp : s13.pc = 0x1254 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, execInstrBr, pc]
    simp only [fetch, hp]; decide
  · rfl
  apply OrdinarySteps.step s14 s15 _ (.base (.SLLI .x11 .x7 63)) 14
  · have hp : s14.pc = 0x1258 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, execInstrBr, pc]
    simp only [fetch, hp]; decide
  · rfl
  apply OrdinarySteps.step s15 s16 _ (.base (.ADD .x6 .x6 .x11)) 13
  · have hp : s15.pc = 0x125c := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, execInstrBr, pc]
    simp only [fetch, hp]; decide
  · rfl
  apply OrdinarySteps.step s16 s17 _ (.base (.LUI .x28 0x80)) 12
  · have hp : s16.pc = 0x1260 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, execInstrBr, pc]
    simp only [fetch, hp]; decide
  · rfl
  apply OrdinarySteps.step s17 s18 _ (.base (.ADDI .x28 .x28 0x408)) 11
  · have hp : s17.pc = 0x1264 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, execInstrBr, pc]
    simp only [fetch, hp]; decide
  · rfl
  apply OrdinarySteps.step s18 s19 _ (.base (.SD .x28 .x6 0)) 10
  · have hp : s18.pc = 0x1268 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, execInstrBr, pc]
    simp only [fetch, hp]; decide
  · simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, ordinaryStep, memoryArgumentsValid, execInstrBr, signExtend12, accessValid, rangeValid, MEMORY_BYTES, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s19 s20 _ (.base (.SRLI .x7 .x7 1)) 9
  · have hp : s19.pc = 0x126c := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, execInstrBr, pc]
    simp only [fetch, hp]; decide
  · rfl
  apply OrdinarySteps.step s20 s21 _ (.base (.SLLI .x11 .x10 63)) 8
  · have hp : s20.pc = 0x1270 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, execInstrBr, pc]
    simp only [fetch, hp]; decide
  · rfl
  apply OrdinarySteps.step s21 s22 _ (.base (.ADD .x7 .x7 .x11)) 7
  · have hp : s21.pc = 0x1274 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, execInstrBr, pc]
    simp only [fetch, hp]; decide
  · rfl
  apply OrdinarySteps.step s22 s23 _ (.base (.LUI .x28 0x80)) 6
  · have hp : s22.pc = 0x1278 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, execInstrBr, pc]
    simp only [fetch, hp]; decide
  · rfl
  apply OrdinarySteps.step s23 s24 _ (.base (.ADDI .x28 .x28 0x410)) 5
  · have hp : s23.pc = 0x127c := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, execInstrBr, pc]
    simp only [fetch, hp]; decide
  · rfl
  apply OrdinarySteps.step s24 s25 _ (.base (.SD .x28 .x7 0)) 4
  · have hp : s24.pc = 0x1280 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, execInstrBr, pc]
    simp only [fetch, hp]; decide
  · simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, ordinaryStep, memoryArgumentsValid, execInstrBr, signExtend12, accessValid, rangeValid, MEMORY_BYTES, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s25 s26 _ (.base (.SRLI .x10 .x10 1)) 3
  · have hp : s25.pc = 0x1284 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, execInstrBr, pc]
    simp only [fetch, hp]; decide
  · rfl
  apply OrdinarySteps.step s26 s27 _ (.base (.LUI .x28 0x80)) 2
  · have hp : s26.pc = 0x1288 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26, execInstrBr, pc]
    simp only [fetch, hp]; decide
  · rfl
  apply OrdinarySteps.step s27 s28 _ (.base (.ADDI .x28 .x28 0x418)) 1
  · have hp : s27.pc = 0x128c := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26, s27, execInstrBr, pc]
    simp only [fetch, hp]; decide
  · rfl
  apply OrdinarySteps.step s28 s29 _ (.base (.SD .x28 .x10 0)) 0
  · have hp : s28.pc = 0x1290 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26, s27, s28, execInstrBr, pc]
    simp only [fetch, hp]; decide
  · simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26, s27, s28, s29, ordinaryStep, memoryArgumentsValid, execInstrBr, signExtend12, accessValid, rangeValid, MEMORY_BYTES, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  exact OrdinarySteps.refl _

theorem shiftIndexState_pc (s : MachineState) : (shiftIndexState s).pc = s.pc + 116 := by
  simp [shiftIndexState, execInstrBr, BitVec.add_assoc]

/-- Exact three-word right shift and low-bit selection, with a full memory frame. -/
theorem shiftIndexState_mem (s : MachineState) (a : Word) :
    (shiftIndexState s).getMem a =
      if a = 0x80418 then s.getMem 0x80418 >>> 1 else
      if a = 0x80410 then (s.getMem 0x80410 >>> 1) + (s.getMem 0x80418 <<< 63) else
      if a = 0x80408 then (s.getMem 0x80408 >>> 1) + (s.getMem 0x80410 <<< 63) else
      if a = 0x80420 then s.getMem 0x80408 &&& 1 else s.getMem a := by
  simp [shiftIndexState, execInstrBr, signExtend12, Expansion.mem_setMem,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]

/-- info: 'SigGolfCandidate.Hypertree.Signing.shiftIndexState_block' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms shiftIndexState_block

theorem shifted_limb (index : BitVec 192) (i : Fin 2) :
    (index.extractLsb' (64 * i.val) 64 >>> 1) +
      (index.extractLsb' (64 * (i.val + 1)) 64 <<< 63) =
      (index >>> 1).extractLsb' (64 * i.val) 64 := by
  apply BitVec.eq_of_toNat_eq
  fin_cases i <;>
    simp [BitVec.toNat_add, BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft,
      BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq] <;> omega

theorem shifted_high_limb (index : BitVec 192) :
    (index.extractLsb' 128 64 >>> 1) = (index >>> 1).extractLsb' 128 64 := by
  apply BitVec.eq_of_toNat_eq
  have bound := index.isLt
  simp [BitVec.toNat_ushiftRight, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
  omega

/-- The 192-bit scratch representation used for the 160-bit tree index. -/
def StoredIndex (s : MachineState) (index : BitVec 192) : Prop :=
  ∀ i : Fin 3, s.getMem (wordAddress 0x80408 i.val) = index.extractLsb' (64 * i.val) 64

/-- One actual main-loop block removes the next selector bit and divides the index by two. -/
theorem shiftIndexState_refines (s : MachineState) (index : BitVec 192)
    (stored : StoredIndex s index) :
    StoredIndex (shiftIndexState s) (index >>> 1) ∧
      ((shiftIndexState s).getMem 0x80420).toNat = index.toNat % 2 := by
  have w0 : s.getMem 0x80408 = index.extractLsb' 0 64 := stored 0
  have w1 : s.getMem 0x80410 = index.extractLsb' 64 64 := stored 1
  have w2 : s.getMem 0x80418 = index.extractLsb' 128 64 := stored 2
  constructor
  · intro i
    fin_cases i
    · change (shiftIndexState s).getMem 0x80408 = _
      rw [shiftIndexState_mem, if_neg (by decide), if_neg (by decide), if_pos rfl, w0, w1]
      exact shifted_limb index 0
    · change (shiftIndexState s).getMem 0x80410 = _
      rw [shiftIndexState_mem, if_neg (by decide), if_pos rfl, w1, w2]
      exact shifted_limb index 1
    · change (shiftIndexState s).getMem 0x80418 = _
      rw [shiftIndexState_mem, if_pos rfl, w2]
      exact shifted_high_limb index
  · rw [shiftIndexState_mem, if_neg (by decide), if_neg (by decide), if_neg (by decide), if_pos rfl, w0]
    simp [BitVec.toNat_and, BitVec.extractLsb'_toNat]

/-- A freshly extracted index has exactly the three-word representation required by
the repeated shift invariant, including the zero upper 32 bits. -/
theorem stored_index_of_answer (s : MachineState) (answer : BitVec 256)
    (low : ∀ i : Fin 2, s.getMem (wordAddress 0x80408 i.val) = answer.extractLsb' (64 * i.val) 64)
    (high : s.getMem 0x80418 = (answer.extractLsb' 128 64 <<< 32) >>> 32) :
    StoredIndex s ((answer.extractLsb' 0 160).zeroExtend 192) := by
  intro i
  fin_cases i
  · rw [show s.getMem (wordAddress 0x80408 0) = answer.extractLsb' 0 64 from low 0]
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.extractLsb'_toNat, BitVec.toNat_setWidth, Nat.shiftRight_eq_div_pow]
  · rw [show s.getMem (wordAddress 0x80408 1) = answer.extractLsb' 64 64 from low 1]
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.extractLsb'_toNat, BitVec.toNat_setWidth, Nat.shiftRight_eq_div_pow]
    omega
  · change s.getMem 0x80418 = _
    rw [high]
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, BitVec.extractLsb'_toNat,
      BitVec.toNat_setWidth, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
    omega

/-- info: 'SigGolfCandidate.Hypertree.Signing.shiftIndexState_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms shiftIndexState_refines

end SigGolfCandidate.Hypertree.Signing
