import SigGolfCandidate.Hypertree.SignLayersMemory

namespace SigGolfCandidate.Hypertree.Signing
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 Keygen Verifying
set_option maxRecDepth 4096

def loopCalls (count level : Nat) : Nat := 739*count - (if level=0 ∧ count≠0 then 734 else 0)
def loopBlocks (count level : Nat) : Nat := 761*count - (if level=0 ∧ count≠0 then 756 else 0)

theorem loopCalls_succ (count level : Nat) :
    loopCalls (count+1) level = (if level=0 then 5 else 739)+loopCalls count (level+1) := by
  unfold loopCalls
  by_cases h : level=0 <;> simp [h] <;> omega

theorem loopBlocks_succ (count level : Nat) :
    loopBlocks (count+1) level = (if level=0 then 5 else 761)+loopBlocks count (level+1) := by
  unfold loopBlocks
  by_cases h : level=0 <;> simp [h] <;> omega

/-- The complete 160-layer actual signer loop, including all serialized signature fields. -/
theorem sign_layers (hash : Hash) (secretKey : SecretKey) (count : Nat) :
    ∀ (s : MachineState) (level index : Nat) (current : Reference.Digest),
    level+count=160 → index<2^192 → s.pc=(if level=160 then 0x12f8 else 0x1220) →
    LoopData s secretKey level index current →
    ∃ final instructions cycles, Trace hash sign s instructions cycles (loopCalls count level) (loopBlocks count level) final ∧
      instructions ≤ 100417*count ∧ cycles ≤ 105766*count ∧ final.pc=0x12f8 ∧
      (∀ i : Fin 2, final.getMem (wordAddress 0x80500 i.val) =
        (Reference.rootsAfter hash secretKey count level index current).extractLsb' (64*i.val) 64) ∧
      LayersStored final level (Reference.signLayers hash secretKey count level index current) ∧
      (∀ address : Nat, address<0x80000 → address%8=0 → address<0x20060+layerOffset level →
        final.getMem (BitVec.ofNat 64 address) = s.getMem (BitVec.ofNat 64 address)) := by
  induction count with
  | zero =>
    intro s level index current total small pc data
    have levelEq : level=160 := by omega
    refine ⟨s,0,0,?_,by omega,by omega,?_,data.currentWords,True.intro,?_⟩
    · simpa [loopCalls,loopBlocks] using Trace.refl (hash := hash) (image := sign) s
    · simpa [levelEq] using pc
    · intro address low aligned before; rfl
  | succ count ih =>
    intro s level index current total small pc data
    have bound : level<160 := by omega
    have startPC : s.pc=0x1220 := by simpa only [if_neg (show level≠160 by omega)] using pc
    obtain ⟨next,n,c,run,nb,cb,nextPC,nextData,stored,frame⟩ := sign_layer hash s secretKey level index current startPC bound small data
    obtain ⟨final,ns,cs,rest,nsb,csb,finalPC,root,storedRest,restFrame⟩ :=
      ih next (level+1) (index/2) (Reference.treeRoot hash secretKey level (index/2)) (by omega) (by omega) nextPC nextData
    refine ⟨final,n+ns,c+cs,?_,?_,?_,finalPC,root,?_,?_⟩
    · simpa only [loopCalls_succ,loopBlocks_succ] using run.trans rest
    · have : n≤100417 := by split at nb <;> omega
      omega
    · have : c≤105766 := by split at cb <;> omega
      omega
    · exact ⟨stored.prefix_frame next final level _ bound restFrame,storedRest⟩
    · intro address low aligned before
      rw [restFrame address low aligned (by have := layerOffset_mono level (level+1) (by omega); omega)]
      apply frame address low aligned
      left
      simpa only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (show address<2^64 by omega)] using before

/-- info: 'SigGolfCandidate.Hypertree.Signing.sign_layers' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sign_layers
end SigGolfCandidate.Hypertree.Signing
