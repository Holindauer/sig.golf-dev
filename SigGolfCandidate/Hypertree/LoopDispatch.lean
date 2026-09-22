import SigGolfCandidate.Hypertree.SignEncodeSubroutine

namespace SigGolfCandidate.Hypertree.Signing
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 Keygen
set_option maxRecDepth 4096

/-- The six actual instructions dispatching the bottom layer directly and encoding higher layers before their tree call. -/
def DispatchCode (image : Image) (base : Word) : Prop :=
  instructionAt image base = some (.base (.LUI .x28 0x80)) ∧
  instructionAt image (base + 4) = some (.base (.ADDI .x28 .x28 0x400)) ∧
  instructionAt image (base + 8) = some (.base (.LD .x6 .x28 0)) ∧
  instructionAt image (base + 12) = some (.base (.BEQ .x6 .x0 8)) ∧
  instructionAt image (base + 16) = some (.base (.JAL .x1 156)) ∧
  instructionAt image (base + 20) = some (.base (.JAL .x1 288))

instance (image : Image) (base : Word) : Decidable (DispatchCode image base) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))

def dispatchReadState (s : MachineState) : MachineState :=
  let s := execInstrBr s (.LUI .x28 0x80)
  let s := execInstrBr s (.ADDI .x28 .x28 0x400)
  let s := execInstrBr s (.LD .x6 .x28 0)
  execInstrBr s (.BEQ .x6 .x0 8)

def dispatchEncodeState (s : MachineState) : MachineState :=
  execInstrBr (dispatchReadState s) (.JAL .x1 156)

def dispatchSavedState (s : MachineState) : MachineState := enterState (dispatchEncodeState s)

theorem dispatchReadState_block (image : Image) (base : Word) (code : DispatchCode image base)
    (s : MachineState) (pc : s.pc = base) : OrdinarySteps image s 4 (dispatchReadState s) := by
  let s1 := execInstrBr s (.LUI .x28 0x80)
  let s2 := execInstrBr s1 (.ADDI .x28 .x28 0x400)
  let s3 := execInstrBr s2 (.LD .x6 .x28 0)
  apply OrdinarySteps.step s s1 _ (.base (.LUI .x28 0x80)) 3
  · simpa only [fetch_at, pc] using code.1
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.ADDI .x28 .x28 0x400)) 2
  · simpa [fetch_at, s1, execInstrBr, pc] using code.2.1
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.LD .x6 .x28 0)) 1
  · simpa [fetch_at, s1, s2, execInstrBr, pc, BitVec.add_assoc] using code.2.2.1
  · simp [s1, s2, s3, ordinaryStep, memoryArgumentsValid, execInstrBr, signExtend12,
      accessValid, rangeValid, MEMORY_BYTES, MachineState.getReg_setReg_eq]
  apply OrdinarySteps.step s3 (dispatchReadState s) _ (.base (.BEQ .x6 .x0 8)) 0
  · simpa [fetch_at, s1, s2, s3, execInstrBr, pc, BitVec.add_assoc] using code.2.2.2.1
  · rfl
  exact OrdinarySteps.refl _

theorem dispatchReadState_pc (s : MachineState) :
    (dispatchReadState s).pc = s.pc + (if s.getMem 0x80400 = 0 then 20 else 16) := by
  simp [dispatchReadState, execInstrBr, signExtend12, signExtend13,
    MachineState.getReg_setReg_eq, BitVec.add_assoc]
  split <;> rfl

theorem dispatchReadState_mem (s : MachineState) (a : Word) :
    (dispatchReadState s).getMem a = s.getMem a := by simp [dispatchReadState, execInstrBr]

theorem dispatchReadState_sp (s : MachineState) :
    (dispatchReadState s).getReg .x2 = s.getReg .x2 := by
  simp [dispatchReadState, execInstrBr, MachineState.getReg_setReg_ne]

theorem dispatchEncodeState_mem (s : MachineState) (a : Word) :
    (dispatchEncodeState s).getMem a = s.getMem a := by
  simp [dispatchEncodeState, execInstrBr, dispatchReadState_mem]

theorem dispatchEncodeState_sp (s : MachineState) :
    (dispatchEncodeState s).getReg .x2 = s.getReg .x2 := by
  simp [dispatchEncodeState, execInstrBr, MachineState.getReg_setReg_ne, dispatchReadState_sp]

private theorem jump_block (image : Image) (s : MachineState) (offset : BitVec 21)
    (code : fetch image s = some (.base (.JAL .x1 offset))) :
    OrdinarySteps image s 1 (execInstrBr s (.JAL .x1 offset)) := by
  exact OrdinarySteps.step s _ _ _ 0 code rfl (OrdinarySteps.refl _)

/-- The actual optional encoding and tree call, with precise instruction count and digit contents. -/
theorem dispatch_to_tree (image : Image) (base : Word) (code : DispatchCode image base)
    (encode : EncodeCode image (base + 172))
    (aligned : (base + 20) &&& ~~~1#64 = base + 20)
    (s : MachineState) (message : Reference.Digest) (pc : s.pc = base)
    (stack : s.getReg .x2 = 0x1000000)
    (lo : s.getMem 0x80500 = message.extractLsb' 0 64)
    (hi : s.getMem 0x80508 = message.extractLsb' 64 64) :
    ∃ final, OrdinarySteps image s (if s.getMem 0x80400 = 0 then 5 else 460) final ∧
      final.pc = base + 308 ∧ final.getReg .x1 = base + 24 ∧ final.getReg .x2 = s.getReg .x2 ∧
      (s.getMem 0x80400 ≠ 0 → ∀ i : Reference.Chain,
        final.getByte (BitVec.ofNat 64 (0x80600 + i.val)) = BitVec.ofNat 8 (Reference.digit message i).val) ∧
      (∀ a, (∀ i : Fin 46, a ≠ BitVec.ofNat 64 (0x80600 + i.val)) →
        final.getByte a = if s.getMem 0x80400 = 0 then s.getByte a else (dispatchSavedState s).getByte a) := by
  have pre := dispatchReadState_block image base code s pc
  by_cases bottom : s.getMem 0x80400 = 0
  · have atTree : (dispatchReadState s).pc = base + 20 := by rw [dispatchReadState_pc, pc, if_pos bottom]
    have jump := jump_block image (dispatchReadState s) 288 (by simpa only [fetch_at, atTree] using code.2.2.2.2.2)
    refine ⟨execInstrBr (dispatchReadState s) (.JAL .x1 288), ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa only [if_pos bottom] using ordinary_trans image s _ _ 4 1 pre jump
    · simp [execInstrBr, signExtend21, atTree, BitVec.add_assoc]
    · simp [execInstrBr, atTree, MachineState.getReg_setReg_eq, BitVec.add_assoc]
    · simp [execInstrBr, MachineState.getReg_setReg_ne, dispatchReadState_sp]
    · intro notBottom; exact False.elim (notBottom bottom)
    · intro a _; rw [if_pos bottom]; simp [execInstrBr, MachineState.getByte, dispatchReadState_mem]
  · have atEncodeCall : (dispatchReadState s).pc = base + 16 := by rw [dispatchReadState_pc, pc, if_neg bottom]
    have call := jump_block image (dispatchReadState s) 156
      (by simpa only [fetch_at, atEncodeCall] using code.2.2.2.2.1)
    have encodePC : (dispatchEncodeState s).pc = base + 172 := by
      simp [dispatchEncodeState, execInstrBr, signExtend21, atEncodeCall, BitVec.add_assoc]
    have returnAddress : (dispatchEncodeState s).getReg .x1 = base + 20 := by
      simp [dispatchEncodeState, execInstrBr, atEncodeCall, MachineState.getReg_setReg_eq, BitVec.add_assoc]
    obtain ⟨encoded, body, bodyPC, bodySP, digits, frame⟩ := encode_subroutine image (base + 172) encode
      (dispatchEncodeState s) message encodePC (by rw [dispatchEncodeState_sp, stack])
      (by rw [dispatchEncodeState_mem]; exact lo) (by rw [dispatchEncodeState_mem]; exact hi)
    have atTree : encoded.pc = base + 20 := by rw [bodyPC, returnAddress, aligned]
    have jump := jump_block image encoded 288 (by simpa only [fetch_at, atTree] using code.2.2.2.2.2)
    refine ⟨execInstrBr encoded (.JAL .x1 288), ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa only [if_neg bottom] using ordinary_trans image s _ _ 5 455
        (ordinary_trans image s _ _ 4 1 pre call) (ordinary_trans image _ _ _ 454 1 body jump)
    · simp [execInstrBr, signExtend21, atTree, BitVec.add_assoc]
    · simp [execInstrBr, atTree, MachineState.getReg_setReg_eq, BitVec.add_assoc]
    · simp [execInstrBr, MachineState.getReg_setReg_ne, bodySP, dispatchEncodeState_sp]
    · intro _ i; simpa only [execInstrBr, MachineState.getByte, MachineState.getMem_setPC, MachineState.getMem_setReg] using digits i
    · intro a outside
      simpa only [if_neg bottom, execInstrBr, MachineState.getByte, MachineState.getMem_setPC, MachineState.getMem_setReg, dispatchSavedState] using frame a outside

theorem sign_dispatch_code : DispatchCode sign 0x1294 := by decide

theorem verify_dispatch_code : DispatchCode verify 0x11bc := by decide

/-- info: 'SigGolfCandidate.Hypertree.Signing.dispatch_to_tree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms dispatch_to_tree

end SigGolfCandidate.Hypertree.Signing
