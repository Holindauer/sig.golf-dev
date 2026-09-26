import SigGolfCandidate.Hypertree.PreludeLoadedLoopData
import SigGolfCandidate.Hypertree.PreludeFinish

namespace SigGolfCandidate.Hypertree.Signing.Prelude
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 Keygen Verifying
set_option maxRecDepth 4096

/-- Universal execution from the official three-input loaded signer state. -/
theorem sign_execution (hash : Hash) (secretKey : SecretKey) (cache : Cache) (message : Message)
    (initial : MachineState)
    (loaded : initialState preludeSubmission .sign (secretKey,cache,message)=some initial) :
    ∃ final instructions cycles,
      Executes hash signPrelude initial instructions
        ⟨.success,final,cycles,118247,121769⟩ ∧
      instructions≤16167394 ∧ cycles≤17028613 ∧
      LayersStored final 0 (Reference.sign hash secretKey (Reference.keygen hash secretKey) message).layers ∧
      (∀ i : Fin 4, final.getMem (wordAddress 0x20060 i.val)=
        (Reference.sign hash secretKey (Reference.keygen hash secretKey) message).randomizer.extractLsb' (64*i.val) 64) := by
  let pk := Reference.keygen hash secretKey
  obtain ⟨ready,pn,pcost,pre,pnb,pcb,readyPC,data,randomizer,pkWords⟩ :=
    loaded_loop_data hash secretKey cache message initial loaded
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
  have rootMatch : RootMatches done := by
    constructor
    · exact (finalRoot 0).trans (finalPk 0).symm
    · exact (finalRoot 1).trans (finalPk 1).symm
  obtain ⟨steps,final,stepsBound,footer,footerFrame⟩ := sign_footer_executes hash done donePC
  have all := (pre.trans body).then_executes footer
  have execution : Executes hash signPrelude initial (pn+n+steps)
      ⟨.success,final,pcost+c+steps,118247,121769⟩ := by
    simpa only [Execution.charge,if_pos rootMatch,show loopCalls 160 0=117506 by rfl,show loopBlocks 160 0=121004 by rfl,
      Nat.reduceAdd,Nat.zero_add,Nat.add_zero,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using all
  refine ⟨final,pn+n+steps,pcost+c+steps,execution,by omega,by omega,?_,?_⟩
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

/-- info: 'SigGolfCandidate.Hypertree.Signing.Prelude.sign_execution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sign_execution
end SigGolfCandidate.Hypertree.Signing.Prelude
