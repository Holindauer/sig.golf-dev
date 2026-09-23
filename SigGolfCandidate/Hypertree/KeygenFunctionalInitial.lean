import SigGolfCandidate.Hypertree.KeygenResourceInitial
import SigGolfCandidate.Hypertree.KeygenTreeExecution

namespace SigGolfCandidate.Hypertree.KeygenFunctional
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 OracleComp Keygen KeygenResource KeygenSecretStart
set_option maxRecDepth 4096

theorem secretKey_byte (secretKey : SecretKey) (i : Nat) (hi : i<32) :
    (secretKeyState secretKey).getByte (BitVec.ofNat 64 (0x20+i))=secretKey.extractLsb' (8*i) 8 := by
  simp only [secretKeyState,Memory.getByte_setReg]
  exact Memory.write_value_byte _ 0x20 32 secretKey i (by decide) (by decide) hi

theorem secretKey_word (secretKey : SecretKey) (i : Fin 4) :
    (secretKeyState secretKey).getMem (Signing.wordAddress 0x20 i.val)=secretKey.extractLsb' (64*i.val) 64 := by
  apply eq_of_forall_extractByte
  intro j hj
  have hi := i.isLt
  have whole : 8*i.val+j<32 := by omega
  have quot : (8*i.val+j)/8=i.val := by omega
  have rem : (8*i.val+j)%8=j := by omega
  have h := secretKey_byte secretKey (8*i.val+j) whole
  rw [Signing.getByte_word _ 0x20 (8*i.val+j) (by decide) (by omega)] at h
  simp only [quot,rem] at h
  rw [h]
  symm
  simpa only [quot,rem] using KeygenNode.extractByte_slice secretKey (8*i.val+j)

theorem secretKey_zero (secretKey : SecretKey) (a : Word) (outside : 0x40≤a.toNat) :
    (secretKeyState secretKey).getMem a=0 := by
  simp only [secretKeyState,MachineState.getMem_setReg]
  rw [Memory.write_preserves _ 0x20 (bytes secretKey) a (by simp [bytes]) (by right; simpa [bytes] using outside)]
  rfl

theorem secretKey_pc (secretKey : SecretKey) : (secretKeyState secretKey).pc=0x1000 := by
  simp only [secretKeyState,MachineState.pc_setReg,MachineState.pc_writeBytesAsWords]
  rfl

theorem secretKey_sp (secretKey : SecretKey) : (secretKeyState secretKey).getReg .x2=0x1000000 := by
  simp only [secretKeyState,MachineState.getReg_setReg_eq (by decide : Reg.x2≠Reg.x0)]
  rfl

theorem prefix_context (secretKey : SecretKey) :
    Context 159 0 false secretKey (prefixState (secretKeyState secretKey)) := by
  constructor
  · rw [prefix_mem,if_pos rfl]; rfl
  · rw [prefix_mem,if_neg (by decide),secretKey_zero _ _ (by decide)]; rfl
  · intro i
    rw [prefix_mem,if_neg (by fin_cases i <;> decide),secretKey_zero _ _ (by fin_cases i <;> decide)]
    fin_cases i <;> rfl
  · intro i
    rw [prefix_mem,if_neg (by fin_cases i <;> decide)]
    exact secretKey_word secretKey i
  · rw [prefix_mem,if_neg (by decide),secretKey_zero _ _ (by decide)]

end SigGolfCandidate.Hypertree.KeygenFunctional
