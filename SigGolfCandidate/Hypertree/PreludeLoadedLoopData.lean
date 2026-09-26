import SigGolfCandidate.Hypertree.PreludeLoadedPrefix
import SigGolfCandidate.Hypertree.PreludeLayers
namespace SigGolfCandidate.Hypertree.Signing.Prelude
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 Keygen
set_option maxRecDepth 8192

theorem loaded_loop_data (hash : Hash) (secretKey : SecretKey) (cache : Cache) (message : Message)
    (s : MachineState) (loaded : initialState preludeSubmission .sign (secretKey, cache, message) = some s) :
    ∃ ready instructions cycles, Trace hash signPrelude s instructions cycles 741 765 ready ∧
      instructions ≤ 100659 ∧ cycles ≤ 106038 ∧ ready.pc = 0x1220 ∧
      LoopData ready secretKey 0 (Reference.indexOf hash (Reference.keygen hash secretKey) message
        (Reference.randomizer hash secretKey message)).toNat 0 ∧
      (∀ i : Fin 4, ready.getMem (wordAddress 0x20060 i.val) =
        (Reference.randomizer hash secretKey message).extractLsb' (64*i.val) 64) ∧
      (∀ i : Fin 2, ready.getMem (wordAddress 0x40 i.val) =
        (Reference.keygen hash secretKey).extractLsb' (64*i.val) 64) := by
  obtain ⟨ready,n,c,run,nb,cb,pc,index,sp,level,mode,ptr,current,randomizer,pk,sk⟩ :=
    loaded_prefix hash secretKey cache message s loaded
  refine ⟨ready,n,c,run,nb,cb,pc,?_,randomizer,pk⟩
  constructor
  · exact sp
  · exact level
  · have eq : (Reference.indexOf hash (Reference.keygen hash secretKey) message
          (Reference.randomizer hash secretKey message)).zeroExtend 192 =
        BitVec.ofNat 192 (Reference.indexOf hash (Reference.keygen hash secretKey) message
          (Reference.randomizer hash secretKey message)).toNat := by
      apply BitVec.eq_of_toNat_eq
      simp
    rw [←eq]; exact index
  · exact sk
  · exact mode
  · exact ptr
  · intro i; rw [current i]; fin_cases i <;> rfl

/-- info: 'SigGolfCandidate.Hypertree.Signing.Prelude.loaded_loop_data' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms loaded_loop_data
end SigGolfCandidate.Hypertree.Signing.Prelude
