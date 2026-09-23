import SigGolfCandidate.Hypertree.KeygenLeafLoop
import SigGolfCandidate.Hypertree.KeygenLeafPrologue

namespace SigGolfCandidate.Hypertree.KeygenLeafCall
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 OracleComp Keygen KeygenSecretStart
set_option maxRecDepth 4096

def Outside (side : Bool) (a : Word) : Prop :=
  a ≠ 0xffffe0 ∧ KeygenLeafLoop.Outside a ∧
    (∀ i : Fin 96, a ≠ Signing.wordAddress 0x80000 i.val) ∧
    ∀ i : Fin 2, a ≠ KeygenSavePublic.wordAddress side i.val

instance (side : Bool) (a : Word) : Decidable (Outside side a) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

/-- A complete upper-leaf call, with the exact generated keygen entry and return. -/
theorem execute (hash : Hash) (s : MachineState) (pc : s.pc=0x11cc)
    (sp : s.getReg .x2=0xfffff0) (level tree : Nat) (side : Bool) (secretKey : SecretKey)
    (nonzero : BitVec.ofNat 64 level ≠ 0) (context : Context level tree side secretKey s) :
    ∃ final, Trace hash keygen s 38487 41158 369 380 final ∧
      final.pc=s.getReg .x1 &&& ~~~1#64 ∧ final.getReg .x2=s.getReg .x2 ∧
      (∀ i : Fin 2, final.getMem (KeygenSavePublic.wordAddress side i.val) =
        (Reference.leafRoot hash secretKey level tree side).extractLsb' (64*i.val) 64) ∧
      (∀ a, Outside side a → final.getMem a=s.getMem a) := by
  obtain ⟨ready,pre,rpc,rcontext,rchain,rsp,saved,entryFrame⟩ :=
    KeygenLeafPrologue.prepare s pc sp level tree side secretKey nonzero context
  obtain ⟨ended,rounds,endPC,endContext,endCounter,endpoints,endRA,endSP,endFrame⟩ :=
    KeygenLeafLoop.loop hash 46 ready 0 level tree side secretKey (by decide) rpc rcontext rchain
      (by intro chain lt; omega)
  have esp : ended.getReg .x2=0xffffe0 := endSP.trans rsp
  have esaved : ended.getMem 0xffffe0=s.getReg .x1 := by
    rw [endFrame _ (by decide),saved]
  obtain ⟨final,tail,fpc,fsp,words,frame⟩ :=
    KeygenLeaf.compute_return keygen hash 0x1548 KeygenLeaf.keygen_code keygen_leaf_return ended endPC
      level tree side (Reference.endpoint hash secretKey level tree side)
      endContext.levelWord endContext.leafWord endContext.indexWords
      (KeygenLeafLoop.endpoint_words hash secretKey level tree side ended endpoints)
      (by rw [esp]; decide)
      (by rw [esp]; decide)
      (by rw [esp]; decide)
      (by rw [esp]; cases side <;> decide)
  refine ⟨final,pre.trace.trans (rounds.trans tail),?_,?_,?_,?_⟩
  · rw [fpc,esp,esaved]
  · rw [fsp,esp,sp]; rfl
  · intro i
    have nz : level≠0 := by intro eq; apply nonzero; rw [eq]; rfl
    simpa only [Reference.leafRoot,if_neg nz] using words i
  · intro a outside
    obtain ⟨hs,loopOutside,inputOutside,publicOutside⟩ := outside
    rw [frame a inputOutside loopOutside.2.1.2.2.1 publicOutside,endFrame a loopOutside,
      entryFrame a hs loopOutside.1 loopOutside.2.1.1]

/-- info: 'SigGolfCandidate.Hypertree.KeygenLeafCall.execute' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms execute

end SigGolfCandidate.Hypertree.KeygenLeafCall
