import SigGolfCandidate.Hypertree.FusedPrepare
namespace SigGolfCandidate.Hypertree.ReuseChainBaseChunks
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 Keygen
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
def prepare (s : MachineState) : MachineState :=
  let s := execInstrBr s (.LD .x11 .x28 (216))
  let s := execInstrBr s (.SD .x28 .x11 (-1048))
  let s := execInstrBr s (.LD .x11 .x28 (224))
  let s := execInstrBr s (.SD .x28 .x11 (-1040))
  let s := execInstrBr s (.ADDI .x10 .x0 2)
  let s := execInstrBr s (.LD .x11 .x28 (-56))
  let s := execInstrBr s (.SLLI .x11 .x11 8)
  let s := execInstrBr s (.ADD .x10 .x10 .x11)
  let s := execInstrBr s (.LD .x11 .x28 (-16))
  let s := execInstrBr s (.SLLI .x11 .x11 16)
  let s := execInstrBr s (.ADD .x10 .x10 .x11)
  let s := execInstrBr s (.LD .x11 .x28 (-8))
  let s := execInstrBr s (.SLLI .x11 .x11 24)
  let s := execInstrBr s (.ADD .x10 .x10 .x11)
  let s := execInstrBr s (.LD .x11 .x28 (0))
  let s := execInstrBr s (.SLLI .x11 .x11 32)
  let s := execInstrBr s (.ADD .x10 .x10 .x11)
  let s := execInstrBr s (.SD .x28 .x10 (-1080))
  let s := execInstrBr s (.LD .x11 .x28 (-48))
  let s := execInstrBr s (.SD .x28 .x11 (-1072))
  let s := execInstrBr s (.LD .x11 .x28 (-40))
  let s := execInstrBr s (.SD .x28 .x11 (-1064))
  let s := execInstrBr s (.LD .x11 .x28 (-32))
  let s := execInstrBr s (.SD .x28 .x11 (-1056))
  let s := execInstrBr s (.ADDI .x28 .x28 (-1056))
  let s := execInstrBr s (.ADDI .x10 .x28 (-24))
  let s := execInstrBr s (.ADDI .x11 .x0 384)
  let s := execInstrBr s (.ADDI .x12 .x28 744)
  let s := execInstrBr s (.ADDI .x5 .x0 1)
  execInstrBr s (.JAL .x0 120)

def shadow (s : MachineState) : MachineState :=
  (s.setReg .x28 0x80000).setPC (s.pc + 4)

def n0 (s : MachineState) : MachineState :=
  let s := execInstrBr s (.LD .x11 .x28 (216))
  let s := execInstrBr s (.SD .x28 .x11 (-1048))
  let s := execInstrBr s (.LD .x11 .x28 (224))
  execInstrBr s (.SD .x28 .x11 (-1040))

def o0 (s : MachineState) : MachineState :=
  let s := execInstrBr s (.LUI .x28 128)
  let s := execInstrBr s (.LD .x11 .x28 1296)
  let s := execInstrBr s (.SD .x28 .x11 32)
  let s := execInstrBr s (.LD .x11 .x28 1304)
  execInstrBr s (.SD .x28 .x11 40)

@[simp] theorem base0 (s : MachineState) : (n0 s).getReg .x28 = s.getReg .x28 := by
  simp [n0, execInstrBr, MachineState.getReg, MachineState.setReg, MachineState.setMem, MachineState.setPC]

theorem eq0 (s : MachineState) (base : s.getReg .x28 = 0x80438) : o0 s = shadow (n0 s) := by
  cases s with
  | mk regs mem code pc committed publicValues privateInput inputBufBase =>
    simp [MachineState.getReg] at base
    simp [n0, o0, shadow, execInstrBr, MachineState.getReg, MachineState.setReg,
      MachineState.getMem, MachineState.setMem, MachineState.setPC, signExtend12, signExtend21, base, BitVec.add_assoc]
    all_goals first | rfl | (funext r; cases r <;> simp_all)

def n1 (s : MachineState) : MachineState :=
  let s := execInstrBr s (.ADDI .x10 .x0 2)
  let s := execInstrBr s (.LD .x11 .x28 (-56))
  let s := execInstrBr s (.SLLI .x11 .x11 8)
  execInstrBr s (.ADD .x10 .x10 .x11)

def o1 (s : MachineState) : MachineState :=
  let s := execInstrBr s (.ADDI .x10 .x0 2)
  let s := execInstrBr s (.LD .x11 .x28 1024)
  let s := execInstrBr s (.SLLI .x11 .x11 8)
  execInstrBr s (.ADD .x10 .x10 .x11)

@[simp] theorem base1 (s : MachineState) : (n1 s).getReg .x28 = s.getReg .x28 := by
  simp [n1, execInstrBr, MachineState.getReg, MachineState.setReg, MachineState.setMem, MachineState.setPC]

theorem eq1 (s : MachineState) (base : s.getReg .x28 = 0x80438) : o1 (shadow s) = shadow (n1 s) := by
  cases s with
  | mk regs mem code pc committed publicValues privateInput inputBufBase =>
    simp [MachineState.getReg] at base
    simp [n1, o1, shadow, execInstrBr, MachineState.getReg, MachineState.setReg,
      MachineState.getMem, MachineState.setMem, MachineState.setPC, signExtend12, signExtend21, base, BitVec.add_assoc]
    all_goals first | rfl | (funext r; cases r <;> simp_all)

def n2 (s : MachineState) : MachineState :=
  let s := execInstrBr s (.LD .x11 .x28 (-16))
  let s := execInstrBr s (.SLLI .x11 .x11 16)
  execInstrBr s (.ADD .x10 .x10 .x11)

def o2 (s : MachineState) : MachineState :=
  let s := execInstrBr s (.LD .x11 .x28 1064)
  let s := execInstrBr s (.SLLI .x11 .x11 16)
  execInstrBr s (.ADD .x10 .x10 .x11)

@[simp] theorem base2 (s : MachineState) : (n2 s).getReg .x28 = s.getReg .x28 := by
  simp [n2, execInstrBr, MachineState.getReg, MachineState.setReg, MachineState.setMem, MachineState.setPC]

theorem eq2 (s : MachineState) (base : s.getReg .x28 = 0x80438) : o2 (shadow s) = shadow (n2 s) := by
  cases s with
  | mk regs mem code pc committed publicValues privateInput inputBufBase =>
    simp [MachineState.getReg] at base
    simp [n2, o2, shadow, execInstrBr, MachineState.getReg, MachineState.setReg,
      MachineState.getMem, MachineState.setMem, MachineState.setPC, signExtend12, signExtend21, base, BitVec.add_assoc]
    all_goals first | rfl | (funext r; cases r <;> simp_all)

def n3 (s : MachineState) : MachineState :=
  let s := execInstrBr s (.LD .x11 .x28 (-8))
  let s := execInstrBr s (.SLLI .x11 .x11 24)
  execInstrBr s (.ADD .x10 .x10 .x11)

def o3 (s : MachineState) : MachineState :=
  let s := execInstrBr s (.LD .x11 .x28 1072)
  let s := execInstrBr s (.SLLI .x11 .x11 24)
  execInstrBr s (.ADD .x10 .x10 .x11)

@[simp] theorem base3 (s : MachineState) : (n3 s).getReg .x28 = s.getReg .x28 := by
  simp [n3, execInstrBr, MachineState.getReg, MachineState.setReg, MachineState.setMem, MachineState.setPC]

theorem eq3 (s : MachineState) (base : s.getReg .x28 = 0x80438) : o3 (shadow s) = shadow (n3 s) := by
  cases s with
  | mk regs mem code pc committed publicValues privateInput inputBufBase =>
    simp [MachineState.getReg] at base
    simp [n3, o3, shadow, execInstrBr, MachineState.getReg, MachineState.setReg,
      MachineState.getMem, MachineState.setMem, MachineState.setPC, signExtend12, signExtend21, base, BitVec.add_assoc]
    all_goals first | rfl | (funext r; cases r <;> simp_all)

def n4 (s : MachineState) : MachineState :=
  let s := execInstrBr s (.LD .x11 .x28 (0))
  let s := execInstrBr s (.SLLI .x11 .x11 32)
  execInstrBr s (.ADD .x10 .x10 .x11)

def o4 (s : MachineState) : MachineState :=
  let s := execInstrBr s (.LD .x11 .x28 1080)
  let s := execInstrBr s (.SLLI .x11 .x11 32)
  execInstrBr s (.ADD .x10 .x10 .x11)

@[simp] theorem base4 (s : MachineState) : (n4 s).getReg .x28 = s.getReg .x28 := by
  simp [n4, execInstrBr, MachineState.getReg, MachineState.setReg, MachineState.setMem, MachineState.setPC]

theorem eq4 (s : MachineState) (base : s.getReg .x28 = 0x80438) : o4 (shadow s) = shadow (n4 s) := by
  cases s with
  | mk regs mem code pc committed publicValues privateInput inputBufBase =>
    simp [MachineState.getReg] at base
    simp [n4, o4, shadow, execInstrBr, MachineState.getReg, MachineState.setReg,
      MachineState.getMem, MachineState.setMem, MachineState.setPC, signExtend12, signExtend21, base, BitVec.add_assoc]
    all_goals first | rfl | (funext r; cases r <;> simp_all)

def n5 (s : MachineState) : MachineState :=
  execInstrBr s (.SD .x28 .x10 (-1080))

def o5 (s : MachineState) : MachineState :=
  execInstrBr s (.SD .x28 .x10 0)

@[simp] theorem base5 (s : MachineState) : (n5 s).getReg .x28 = s.getReg .x28 := by
  simp [n5, execInstrBr, MachineState.getReg, MachineState.setReg, MachineState.setMem, MachineState.setPC]

theorem eq5 (s : MachineState) (base : s.getReg .x28 = 0x80438) : o5 (shadow s) = shadow (n5 s) := by
  cases s with
  | mk regs mem code pc committed publicValues privateInput inputBufBase =>
    simp [MachineState.getReg] at base
    simp [n5, o5, shadow, execInstrBr, MachineState.getReg, MachineState.setReg,
      MachineState.getMem, MachineState.setMem, MachineState.setPC, signExtend12, signExtend21, base, BitVec.add_assoc]
    all_goals first | rfl | (funext r; cases r <;> simp_all)

def n6 (s : MachineState) : MachineState :=
  let s := execInstrBr s (.LD .x11 .x28 (-48))
  execInstrBr s (.SD .x28 .x11 (-1072))

def o6 (s : MachineState) : MachineState :=
  let s := execInstrBr s (.LD .x11 .x28 1032)
  execInstrBr s (.SD .x28 .x11 8)

@[simp] theorem base6 (s : MachineState) : (n6 s).getReg .x28 = s.getReg .x28 := by
  simp [n6, execInstrBr, MachineState.getReg, MachineState.setReg, MachineState.setMem, MachineState.setPC]

theorem eq6 (s : MachineState) (base : s.getReg .x28 = 0x80438) : o6 (shadow s) = shadow (n6 s) := by
  cases s with
  | mk regs mem code pc committed publicValues privateInput inputBufBase =>
    simp [MachineState.getReg] at base
    simp [n6, o6, shadow, execInstrBr, MachineState.getReg, MachineState.setReg,
      MachineState.getMem, MachineState.setMem, MachineState.setPC, signExtend12, signExtend21, base, BitVec.add_assoc]
    all_goals first | rfl | (funext r; cases r <;> simp_all)

def n7 (s : MachineState) : MachineState :=
  let s := execInstrBr s (.LD .x11 .x28 (-40))
  execInstrBr s (.SD .x28 .x11 (-1064))

def o7 (s : MachineState) : MachineState :=
  let s := execInstrBr s (.LD .x11 .x28 1040)
  execInstrBr s (.SD .x28 .x11 16)

@[simp] theorem base7 (s : MachineState) : (n7 s).getReg .x28 = s.getReg .x28 := by
  simp [n7, execInstrBr, MachineState.getReg, MachineState.setReg, MachineState.setMem, MachineState.setPC]

theorem eq7 (s : MachineState) (base : s.getReg .x28 = 0x80438) : o7 (shadow s) = shadow (n7 s) := by
  cases s with
  | mk regs mem code pc committed publicValues privateInput inputBufBase =>
    simp [MachineState.getReg] at base
    simp [n7, o7, shadow, execInstrBr, MachineState.getReg, MachineState.setReg,
      MachineState.getMem, MachineState.setMem, MachineState.setPC, signExtend12, signExtend21, base, BitVec.add_assoc]
    all_goals first | rfl | (funext r; cases r <;> simp_all)

def n8 (s : MachineState) : MachineState :=
  let s := execInstrBr s (.LD .x11 .x28 (-32))
  execInstrBr s (.SD .x28 .x11 (-1056))

def o8 (s : MachineState) : MachineState :=
  let s := execInstrBr s (.LD .x11 .x28 1048)
  execInstrBr s (.SD .x28 .x11 24)

@[simp] theorem base8 (s : MachineState) : (n8 s).getReg .x28 = s.getReg .x28 := by
  simp [n8, execInstrBr, MachineState.getReg, MachineState.setReg, MachineState.setMem, MachineState.setPC]

theorem eq8 (s : MachineState) (base : s.getReg .x28 = 0x80438) : o8 (shadow s) = shadow (n8 s) := by
  cases s with
  | mk regs mem code pc committed publicValues privateInput inputBufBase =>
    simp [MachineState.getReg] at base
    simp [n8, o8, shadow, execInstrBr, MachineState.getReg, MachineState.setReg,
      MachineState.getMem, MachineState.setMem, MachineState.setPC, signExtend12, signExtend21, base, BitVec.add_assoc]
    all_goals first | rfl | (funext r; cases r <;> simp_all)

def n9 (s : MachineState) : MachineState :=
  let s := execInstrBr s (.ADDI .x28 .x28 (-1056))
  let s := execInstrBr s (.ADDI .x10 .x28 (-24))
  let s := execInstrBr s (.ADDI .x11 .x0 384)
  let s := execInstrBr s (.ADDI .x12 .x28 744)
  let s := execInstrBr s (.ADDI .x5 .x0 1)
  execInstrBr s (.JAL .x0 120)

def o9 (s : MachineState) : MachineState :=
  let s := execInstrBr s (.ADDI .x28 .x28 24)
  let s := execInstrBr s (.ADDI .x10 .x28 (-24))
  let s := execInstrBr s (.ADDI .x11 .x0 384)
  let s := execInstrBr s (.ADDI .x12 .x28 744)
  let s := execInstrBr s (.ADDI .x5 .x0 1)
  execInstrBr s (.JAL .x0 116)

theorem eq9 (s : MachineState) (base : s.getReg .x28 = 0x80438) : o9 (shadow s) = n9 s := by
  cases s with
  | mk regs mem code pc committed publicValues privateInput inputBufBase =>
    simp [MachineState.getReg] at base
    simp [n9, o9, shadow, execInstrBr, MachineState.getReg, MachineState.setReg,
      MachineState.getMem, MachineState.setMem, MachineState.setPC, signExtend12, signExtend21, base, BitVec.add_assoc]
    all_goals first | rfl | (funext r; cases r <;> simp_all)

theorem prepare_equiv (s : MachineState) (base : s.getReg .x28 = 0x80438) :
    prepare s = FusedPrepare.state s := by
  change n9 (n8 (n7 (n6 (n5 (n4 (n3 (n2 (n1 (n0 (s)))))))))) = o9 (o8 (o7 (o6 (o5 (o4 (o3 (o2 (o1 (o0 (s))))))))))
  rw [eq0 s base]
  rw [eq1 _ (by simpa only [base0] using base)]
  rw [eq2 _ (by simpa only [base0, base1] using base)]
  rw [eq3 _ (by simpa only [base0, base1, base2] using base)]
  rw [eq4 _ (by simpa only [base0, base1, base2, base3] using base)]
  rw [eq5 _ (by simpa only [base0, base1, base2, base3, base4] using base)]
  rw [eq6 _ (by simpa only [base0, base1, base2, base3, base4, base5] using base)]
  rw [eq7 _ (by simpa only [base0, base1, base2, base3, base4, base5, base6] using base)]
  rw [eq8 _ (by simpa only [base0, base1, base2, base3, base4, base5, base6, base7] using base)]
  rw [eq9 _ (by simpa only [base0, base1, base2, base3, base4, base5, base6, base7, base8] using base)]

/-- info: 'SigGolfCandidate.Hypertree.ReuseChainBaseChunks.prepare_equiv' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms prepare_equiv
end SigGolfCandidate.Hypertree.ReuseChainBaseChunks
