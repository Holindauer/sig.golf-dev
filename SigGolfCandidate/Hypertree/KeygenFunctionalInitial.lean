import SigGolfCandidate.Hypertree.KeygenResourceInitial
import SigGolfCandidate.Hypertree.KeygenTreeExecution

namespace SigGolfCandidate.Hypertree.KeygenFunctional
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 OracleComp Keygen KeygenResource KeygenSecretStart
set_option maxRecDepth 4096

theorem seed_byte (seed : Seed) (i : Nat) (hi : i<16) :
    (seedState seed).getByte (BitVec.ofNat 64 (0x20+i))=seed.extractLsb' (8*i) 8 := by
  simp only [seedState,Memory.getByte_setReg]
  exact Memory.write_value_byte _ 0x20 16 seed i (by decide) (by decide) hi

theorem seed_word (seed : Seed) (i : Fin 2) :
    (seedState seed).getMem (Signing.wordAddress 0x20 i.val)=seed.extractLsb' (64*i.val) 64 := by
  apply eq_of_forall_extractByte
  intro j hj
  have hi := i.isLt
  have whole : 8*i.val+j<16 := by omega
  have quot : (8*i.val+j)/8=i.val := by omega
  have rem : (8*i.val+j)%8=j := by omega
  have h := seed_byte seed (8*i.val+j) whole
  rw [Signing.getByte_word _ 0x20 (8*i.val+j) (by decide) (by omega)] at h
  simp only [quot,rem] at h
  rw [h]
  symm
  simpa only [quot,rem] using KeygenNode.extractByte_slice seed (8*i.val+j)

theorem seed_zero (seed : Seed) (a : Word) (outside : 0x30≤a.toNat) :
    (seedState seed).getMem a=0 := by
  simp only [seedState,MachineState.getMem_setReg]
  rw [Memory.write_preserves _ 0x20 (bytes seed) a (by simp [bytes]) (by right; simpa [bytes] using outside)]
  rfl

theorem seed_pc (seed : Seed) : (seedState seed).pc=0x1000 := by
  simp only [seedState,MachineState.pc_setReg,MachineState.pc_writeBytesAsWords]
  rfl

theorem seed_sp (seed : Seed) : (seedState seed).getReg .x2=0x1000000 := by
  simp only [seedState,MachineState.getReg_setReg_eq (by decide : Reg.x2≠Reg.x0)]
  rfl

theorem prefix_context (seed : Seed) :
    Context 159 0 false seed (prefixState (seedState seed)) := by
  constructor
  · rw [prefix_mem,if_pos rfl]; rfl
  · rw [prefix_mem,if_neg (by decide),seed_zero _ _ (by decide)]; rfl
  · intro i
    rw [prefix_mem,if_neg (by fin_cases i <;> decide),seed_zero _ _ (by fin_cases i <;> decide)]
    fin_cases i <;> rfl
  · intro i
    rw [prefix_mem,if_neg (by fin_cases i <;> decide)]
    exact seed_word seed i
  · rw [prefix_mem,if_neg (by decide),seed_zero _ _ (by decide)]

end SigGolfCandidate.Hypertree.KeygenFunctional
