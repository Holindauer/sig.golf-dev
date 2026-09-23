import SigGolfCandidate.Hypertree.SignExecutionSetup
import SigGolfCandidate.Hypertree.SignFinish

namespace SigGolfCandidate.Hypertree.Signing
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 Keygen Verifying
set_option maxRecDepth 4096

/-- Actual universal signer execution, with an exact compression count and reference output words.
Success occurs precisely when the supplied public key equals the secret key's reference root. -/
theorem sign_execution (hash : Hash) (secretKey : SecretKey) (pk : PublicKey) (cache : Cache) (message : Message) :
    ∃ initial final instructions cycles,
      initialState submission .sign (secretKey,pk,cache,message)=some initial ∧
      Executes hash sign initial instructions
        ⟨if Reference.keygen hash secretKey=pk then .success else .failure,final,cycles,117508,121008⟩ ∧
      instructions≤16000241 ∧ cycles≤16800271 ∧
      LayersStored final 0 (Reference.sign hash secretKey pk message).layers ∧
      (∀ i : Fin 4, final.getMem (wordAddress 0x20060 i.val)=
        (Reference.sign hash secretKey pk message).randomizer.extractLsb' (64*i.val) 64) := by
  obtain ⟨initial,ready,loaded,pre,readyPC,data,randomizer,pkWords⟩ := loaded_loop_data hash secretKey pk cache message
  let index := Reference.indexOf hash pk message (Reference.randomizer hash secretKey message)
  have small : index.toNat<2^192 := by have := index.isLt; omega
  obtain ⟨done,n,c,body,nb,cb,donePC,root,stored,frame⟩ :=
    sign_layers hash secretKey 160 ready 0 index.toNat 0 (by decide) small (by simpa using readyPC) data
  have finalRoot : ∀ i : Fin 2, done.getMem (wordAddress 0x80500 i.val) =
      (Reference.keygen hash secretKey).extractLsb' (64*i.val) 64 := by
    intro i
    rw [root i,Reference.roots_after_succ hash secretKey 159 0]
    simp only [Nat.zero_add,Nat.div_eq_of_lt index.isLt]
    rfl
  have finalPk : ∀ i : Fin 2, done.getMem (wordAddress 0x40 i.val)=pk.extractLsb' (64*i.val) 64 := by
    intro i
    rw [show wordAddress 0x40 i.val=BitVec.ofNat 64 (0x40+8*i.val) by rfl,
      frame _ (by have := i.isLt; omega) (by omega) (by have := i.isLt; change 0x40+8*i.val<0x20080; omega)]
    exact pkWords i
  have rootMatch : RootMatches done ↔ Reference.keygen hash secretKey=pk := by
    constructor
    · intro h
      apply digest_eq_of_words
      intro i
      rw [←finalRoot i,←finalPk i]
      fin_cases i
      · exact h.1
      · exact h.2
    · intro eq
      constructor
      · exact (finalRoot 0).trans (eq ▸ (finalPk 0).symm)
      · exact (finalRoot 1).trans (eq ▸ (finalPk 1).symm)
  obtain ⟨steps,final,stepsBound,footer,footerFrame⟩ := sign_footer_executes hash done donePC
  have all := (pre.trans body).then_executes footer
  have execution : Executes hash sign initial (226+n+steps)
      ⟨if Reference.keygen hash secretKey=pk then .success else .failure,final,256+c+steps,117508,121008⟩ := by
    simpa only [Execution.charge,rootMatch,show loopCalls 160 0=117506 by rfl,show loopBlocks 160 0=121004 by rfl,
      Nat.reduceAdd,Nat.zero_add,Nat.add_zero,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using all
  refine ⟨initial,final,226+n+steps,256+c+steps,loaded,execution,by omega,by omega,?_,?_⟩
  · have transport : ∀ (level : Nat) (signatures : List Reference.LayerSignature),
        LayersStored done level signatures → LayersStored final level signatures := by
      intro level signatures
      induction signatures generalizing level with
      | nil => intro _; trivial
      | cons signature rest ih =>
        intro h
        refine ⟨?_,ih (level+1) h.2⟩
        have hstored := h.1
        unfold LayerStored at hstored ⊢
        split at hstored <;> rename_i zero
        · rw [if_pos zero]
          exact ⟨fun i => (footerFrame _).trans (hstored.1 i),fun i => (footerFrame _).trans (hstored.2 i)⟩
        · rw [if_neg zero]
          exact ⟨fun chain i => (footerFrame _).trans (hstored.1 chain i),fun i => (footerFrame _).trans (hstored.2 i)⟩
    exact transport 0 _ stored
  · intro i
    rw [footerFrame]
    rw [show wordAddress 0x20060 i.val=BitVec.ofNat 64 (0x20060+8*i.val) by rfl,
      frame _ (by have := i.isLt; omega) (by omega) (by have := i.isLt; change 0x20060+8*i.val<0x20080; omega)]
    exact randomizer i

/-- info: 'SigGolfCandidate.Hypertree.Signing.sign_execution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sign_execution
end SigGolfCandidate.Hypertree.Signing
