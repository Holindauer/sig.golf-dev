import SigGolfCandidate.Hypertree.SignLayerFrame

namespace SigGolfCandidate.Hypertree.Signing
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 Keygen Verifying
set_option maxRecDepth 4096

/-- A full actual signing iteration, including the loop's advance and branch. -/
theorem sign_layer (hash : Hash) (s : MachineState) (secretKey : SecretKey) (level index : Nat)
    (current : Reference.Digest) (pc : s.pc = 0x1220) (bound : level < 160) (small : index < 2^192)
    (data : LoopData s secretKey level index current) :
    ∃ final instructions cycles, Trace hash sign s instructions cycles
      (if level = 0 then 5 else 739) (if level = 0 then 5 else 761) final ∧
      instructions ≤ (if level = 0 then 588 else 100417) ∧ cycles ≤ (if level = 0 then 623 else 105766) ∧
      final.pc = (if level+1=160 then 0x12f8 else 0x1220) ∧
      LoopData final secretKey (level+1) (index/2) (Reference.treeRoot hash secretKey level (index/2)) ∧
      LayerStored final (0x20060+layerOffset level) level
        (Reference.signLayer hash secretKey level (index/2) (index%2==1) current) ∧
      (∀ address : Nat, address<0x80000 → address%8=0 →
        OutsideLayer (0x20060+layerOffset level) level (BitVec.ofNat 64 address) →
        final.getMem (BitVec.ofNat 64 address) = s.getMem (BitVec.ofNat 64 address)) := by
  obtain ⟨ready,pre,readyPC,readyRA,readySP,context,ptr,mode,selector,digits,preFrame⟩ :=
    sign_layer_prepare hash s secretKey level index current pc bound small data
  have valid := sign_pointer_valid level bound
  obtain ⟨done,n,c,body,nb,cb,donePC,doneSP,root,stored,frame⟩ :=
    sign_tree hash ready secretKey (0x20060+layerOffset level) level (index/2) current (index%2==1)
      readyPC readySP bound valid context ptr (by rw [mode]; decide) selector digits
  have atAdvance : done.pc = 0x12ac := by rw [donePC,readyRA]; decide
  have keep (a : Word) (region : (0x80400≤a.toNat ∧ a.toNat<0x80428) ∨ (0x80440≤a.toNat ∧ a.toNat<0x80450)) :
      done.getMem a = ready.getMem a :=
    frame a (outsideTreeWork_metadata a region) (outsideLayer_high _ _ valid a (by omega))
  have counter : done.getMem 0x80400 = BitVec.ofNat 64 level := (keep _ (by decide)).trans context.levelEq
  have pointer : done.getMem 0x80448 = BitVec.ofNat 64 (0x20060+layerOffset level) := (keep _ (by decide)).trans ptr
  have advance := advance_block sign 0x12ac sign_advance_code done atAdvance
  have after := advanceState_layer done 0x20060 level bound counter pointer
  have zero : done.getMem 0x80400 = 0 ↔ level = 0 := by rw [counter]; exact level_word_zero level bound
  have nextPC : (advanceState done).pc = (if level+1=160 then 0x12f8 else 0x1220) := by
    simpa using advanceState_layer_pc done 0x12ac level atAdvance bound counter
  have total := pre.trans (body.trans advance.trace)
  simp only [zero,Nat.zero_add,Nat.add_zero] at total
  refine ⟨advanceState done,_,_,total,?_,?_,nextPC,?_,?_,?_⟩
  · by_cases h : level=0 <;> simp only [h,if_true,if_false] at nb ⊢ <;> omega
  · by_cases h : level=0 <;> simp only [h,if_true,if_false] at cb ⊢ <;> omega
  · constructor
    · rw [advanceState_sp,doneSP,readySP]
    · exact after.1
    · intro i
      rw [advanceState_mem,if_neg (by fin_cases i <;> decide),if_neg (by fin_cases i <;> decide),
        keep _ (by fin_cases i <;> decide)]
      exact context.indexEq i
    · intro i
      have low : (wordAddress 0x20 i.val).toNat < 0x80000 := by fin_cases i <;> decide
      have outside : OutsideLayer (0x20060+layerOffset level) level (wordAddress 0x20 i.val) := by
        left; simp only [wordAddress,BitVec.toNat_ofNat]; have := i.isLt; omega
      rw [advance_low_frame done _ low,frame _ (outsideTreeWork_low _ low) outside]
      exact context.secretKeyEq i
    · rw [advanceState_mem,if_neg (by decide),if_neg (by decide),keep _ (by decide)]; exact mode
    · exact after.2
    · intro i
      rw [advanceState_mem,if_neg (by fin_cases i <;> decide),if_neg (by fin_cases i <;> decide)]
      exact root i
  · exact stored.frame done (advanceState done) _ _ _ valid (advance_low_frame done)
  · intro address low aligned outside
    have lowWord : (BitVec.ofNat 64 address).toNat < 0x80000 := by
      simpa only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (show address<2^64 by omega)] using low
    rw [advance_low_frame done _ lowWord,frame _ (outsideTreeWork_low _ lowWord) outside,preFrame address low aligned]

/-- info: 'SigGolfCandidate.Hypertree.Signing.sign_layer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sign_layer
end SigGolfCandidate.Hypertree.Signing
