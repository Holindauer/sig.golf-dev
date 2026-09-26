import SigGolfCandidate.Hypertree.RegisterHeader
namespace SigGolfCandidate.Hypertree.RegisterHeader
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 Keygen
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false

def shadow (s : MachineState) (saved : Word) : MachineState :=
  (s.setReg .x14 (s.getReg .x10)).setReg .x10 saved

def addField (r : Reg) (offset : BitVec 12) (shift : BitVec 6) (s : MachineState) : MachineState :=
  let s := execInstrBr s (.LD .x11 .x28 offset)
  let s := execInstrBr s (.SLLI .x11 .x11 shift)
  execInstrBr s (.ADD r r .x11)

theorem addField_shadow (s : MachineState) (saved : Word) (offset : BitVec 12) (shift : BitVec 6) :
    addField .x14 offset shift (shadow s saved) = shadow (addField .x10 offset shift s) saved := by
  cases s with
  | mk regs mem code pc committed publicValues privateInput inputBufBase =>
    simp [addField,shadow,execInstrBr,MachineState.getReg,MachineState.setReg,
      MachineState.getMem,MachineState.setMem,MachineState.setPC]
    all_goals first | rfl | (funext r; cases r <;> simp_all)

def seed (r : Reg) (s : MachineState) := execInstrBr s (.ADDI r .x0 2)

theorem seed_shadow (s : MachineState) : seed .x14 s = shadow (seed .x10 s) (s.getReg .x10) := by
  cases s with
  | mk regs mem code pc committed publicValues privateInput inputBufBase =>
    simp [seed,shadow,execInstrBr,MachineState.getReg,MachineState.setReg,MachineState.setPC]
    all_goals first | rfl | (funext r; cases r <;> simp_all)

def header (r : Reg) (s : MachineState) : MachineState :=
  let s := seed r s
  let s := addField r (-56) 8 s
  let s := addField r (-16) 16 s
  let s := addField r (-8) 24 s
  addField r 0 32 s

theorem header_shadow (s : MachineState) : header .x14 s = shadow (header .x10 s) (s.getReg .x10) := by
  dsimp only [header]
  rw [seed_shadow,addField_shadow,addField_shadow,addField_shadow,addField_shadow]

def copyValue (s : MachineState) : MachineState :=
  let s := execInstrBr s (.LD .x11 .x28 216)
  let s := execInstrBr s (.SD .x28 .x11 (-1048))
  let s := execInstrBr s (.LD .x11 .x28 224)
  execInstrBr s (.SD .x28 .x11 (-1040))

def storeHeader (r : Reg) (s : MachineState) : MachineState := execInstrBr s (.SD .x28 r (-1080))

def copyField (src dst : BitVec 12) (s : MachineState) : MachineState :=
  let s := execInstrBr s (.LD .x11 .x28 src)
  execInstrBr s (.SD .x28 .x11 dst)

def copyIndex (s : MachineState) : MachineState :=
  copyField (-32) (-1056) (copyField (-40) (-1064) (copyField (-48) (-1072) s))

theorem store_shadow (s : MachineState) (saved : Word) :
    storeHeader .x14 (shadow s saved) = shadow (storeHeader .x10 s) saved := by
  cases s with
  | mk regs mem code pc committed publicValues privateInput inputBufBase =>
    simp [storeHeader,shadow,execInstrBr,MachineState.getReg,MachineState.setReg,
      MachineState.getMem,MachineState.setMem,MachineState.setPC]
    all_goals first | rfl | (funext r; cases r <;> simp_all)

theorem copyField_shadow (s : MachineState) (saved : Word) (src dst : BitVec 12) :
    copyField src dst (shadow s saved) = shadow (copyField src dst s) saved := by
  cases s with
  | mk regs mem code pc committed publicValues privateInput inputBufBase =>
    simp [copyField,shadow,execInstrBr,MachineState.getReg,MachineState.setReg,
      MachineState.getMem,MachineState.setMem,MachineState.setPC]
    all_goals first | rfl | (funext r; cases r <;> simp_all)

theorem index_shadow (s : MachineState) (saved : Word) :
    copyIndex (shadow s saved) = shadow (copyIndex s) saved := by
  simp only [copyIndex,copyField_shadow]

theorem tail_shadow (s : MachineState) (saved : Word) :
    PersistentStepBase.newTail (shadow s saved) =
      (PersistentStepBase.newTail s).setReg .x14 (s.getReg .x10) := by
  cases s with
  | mk regs mem code pc committed publicValues privateInput inputBufBase =>
    simp [PersistentStepBase.newTail,shadow,execInstrBr,MachineState.getReg,MachineState.setReg,
      MachineState.getMem,MachineState.setMem,MachineState.setPC]
    all_goals first | rfl | (funext r; cases r <;> simp_all)

/-- Initial setup changes only the cached header register. -/
theorem initial_chunks (s : MachineState) :
    initial s = (PersistentStepBase.initial s).setReg .x14
      ((copyIndex (storeHeader .x10 (header .x10 (copyValue s)))).getReg .x10) := by
  change PersistentStepBase.newTail (copyIndex (storeHeader .x14 (header .x14 (copyValue s)))) = _
  rw [header_shadow,store_shadow,index_shadow,tail_shadow]
  rfl

theorem stored_header (s : MachineState) (base : s.getReg .x28 = 0x80438) :
    (copyIndex (storeHeader .x10 s)).getMem 0x80000 =
      (copyIndex (storeHeader .x10 s)).getReg .x10 := by
  simp [copyIndex,copyField,storeHeader,execInstrBr,base,signExtend12,
    MachineState.getReg_setReg_ne,MachineState.getMem_setReg,MachineState.getMem_setMem_ne,
    MachineState.getMem_setMem_eq,MachineState.getReg_setPC,MachineState.getMem_setPC]

/-- info: 'SigGolfCandidate.Hypertree.RegisterHeader.header_shadow' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms header_shadow
/-- info: 'SigGolfCandidate.Hypertree.RegisterHeader.initial_chunks' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms initial_chunks
end SigGolfCandidate.Hypertree.RegisterHeader
