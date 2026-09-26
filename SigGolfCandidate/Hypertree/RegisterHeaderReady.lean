import SigGolfCandidate.Hypertree.RegisterHeaderChunks
namespace SigGolfCandidate.Hypertree.RegisterHeader
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 Keygen
set_option maxRecDepth 8192

def suffix (r : Reg) (s : MachineState) : MachineState :=
  PersistentStepBase.newTail (copyIndex (storeHeader r s))

theorem tail_mem (s : MachineState) (a : Word) :
    (PersistentStepBase.newTail s).getMem a = s.getMem a := by
  simp [PersistentStepBase.newTail,execInstrBr,MachineState.getMem_setReg]

theorem suffix_ready (s : MachineState) (saved : Word) (base : s.getReg .x28 = 0x80438) :
    Ready (suffix .x14 (shadow s saved)) := by
  unfold suffix
  rw [store_shadow,index_shadow,tail_shadow]
  unfold Ready
  simp only [MachineState.getReg_setReg_eq,MachineState.getMem_setReg]
  rw [tail_mem,stored_header s base]
  exact MachineState.getReg_setReg_eq (by decide)

theorem field_base (s : MachineState) (offset : BitVec 12) (shift : BitVec 6) :
    (addField .x10 offset shift s).getReg .x28 = s.getReg .x28 := by
  simp [addField,execInstrBr,MachineState.getReg_setReg_ne]

theorem header_base (s : MachineState) : (header .x10 s).getReg .x28 = s.getReg .x28 := by
  dsimp only [header]
  simp only [field_base]
  simp [seed,execInstrBr,MachineState.getReg_setReg_ne]

theorem copy_base (s : MachineState) : (copyValue s).getReg .x28 = s.getReg .x28 := by
  simp [copyValue,execInstrBr,MachineState.getReg_setReg_ne]

theorem initial_ready (s : MachineState) (base : s.getReg .x28 = 0x80438) : Ready (initial s) := by
  change Ready (suffix .x14 (header .x14 (copyValue s)))
  rw [header_shadow]
  apply suffix_ready
  exact (header_base _).trans ((copy_base s).trans base)

/-- info: 'SigGolfCandidate.Hypertree.RegisterHeader.initial_ready' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms initial_ready
end SigGolfCandidate.Hypertree.RegisterHeader
