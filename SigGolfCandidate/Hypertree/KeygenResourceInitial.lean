import SigGolfCandidate.Hypertree.ResourceRun
import SigGolfCandidate.Memory

namespace SigGolfCandidate.Hypertree.KeygenResource
open SigGolfCandidate.Resources SigGolf SigGolf.Riscv RiscvZkvm.Rv64

/-- Only four initially zero control words are needed; all secret key-dependent data stays unknown. -/
def initialAbstract : AbstractState :=
  ⟨0x1000, [(.x2, 0x1000000)],
    [(0x80408, 0), (0x80410, 0), (0x80418, 0), (0x80440, 0)]⟩

private def blank : MachineState := { regs := fun _ => 0, mem := fun _ => 0, pc := 0x1000 }

def secretKeyState (secretKey : SecretKey) : MachineState :=
  (blank.writeBytesAsWords (BitVec.ofNat 64 0x20) (bytes secretKey)).setReg .x2 (BitVec.ofNat 64 0x1000000)

theorem secretKey_loaded (secretKey : SecretKey) : initialState submission .keygen secretKey = some (secretKeyState secretKey) := by
  unfold initialState
  rw [if_pos (admitted.2 .keygen)]
  have hd : (submission.image .keygen).data = [] := rfl
  have hb : dataBase (submission.image .keygen) = 0x1000000 := by decide
  simp only [hd, hb, inputBuffers, List.foldl_cons, List.foldl_nil]
  rw [MachineState.writeBytesAsWords]
  rfl

private theorem initial_mem_known (p v : Word) (known : lookup p initialAbstract.mem = some v) :
    v = 0 ∧ 0x80408 ≤ p.toNat := by
  simp only [initialAbstract, lookup] at known
  split_ifs at known <;> simp_all

theorem secretKey_models (secretKey : SecretKey) : initialAbstract.Models (secretKeyState secretKey) := by
  refine ⟨?_, ?_, ?_⟩
  · simp [secretKeyState, initialAbstract, blank]
  · intro r value known
    by_cases hz : r = .x0
    · subst r
      simp [AbstractState.getReg] at known
      subst value
      rfl
    · by_cases hs : r = .x2
      · subst r
        have value_eq : value = 0x1000000 := by
          simpa [initialAbstract, AbstractState.getReg, lookup] using known.symm
        rw [value_eq]
        exact MachineState.getReg_setReg_eq (by decide)
      · simp [initialAbstract, AbstractState.getReg, lookup, hz, hs] at known
  · intro p value known
    obtain ⟨rfl, lower⟩ := initial_mem_known p value known
    simp only [secretKeyState, MachineState.getMem_setReg]
    rw [Memory.write_preserves blank 0x20 (bytes secretKey) p]
    · rfl
    · simp [bytes]
    · right
      have len : (bytes secretKey).length = 32 := by simp [bytes]
      rw [len]
      omega

/-- info: 'SigGolfCandidate.Hypertree.KeygenResource.secretKey_models' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms secretKey_models

end SigGolfCandidate.Hypertree.KeygenResource
