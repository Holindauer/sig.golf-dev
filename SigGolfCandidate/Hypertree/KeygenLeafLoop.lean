import SigGolfCandidate.Hypertree.KeygenSecretStart
import SigGolfCandidate.Hypertree.EndpointStore
import SigGolfCandidate.Hypertree.KeygenLeafExecution

namespace SigGolfCandidate.Hypertree.KeygenLeafLoop
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 OracleComp Keygen KeygenSecretStart
set_option maxRecDepth 4096

/-- Memory unaffected by generating all46chain endpoints. -/
def Outside (a : Word) : Prop :=
  a ≠ 0x80430 ∧ KeygenChainLoop.Outside a ∧
    ∀ i : Fin 92, a ≠ Signing.wordAddress 0x80800 i.val

instance (a : Word) : Decidable (Outside a) := inferInstanceAs (Decidable (_ ∧ _ ∧ _))

theorem endpoint_outside_work (chain : Reference.Chain) (i : Fin 2) :
    KeygenChainLoop.Outside (KeygenEndpoint.endpointAddress chain.val i.val) := by
  have hc := chain.isLt
  have hi := i.isLt
  constructor
  · intro eq
    have h := congrArg BitVec.toNat eq
    change (0x80800+16*chain.val+8*i.val)%2^64=0x80438 at h
    omega
  constructor
  · intro j eq
    have hj := j.isLt
    have h := congrArg BitVec.toNat eq
    change (0x80800+16*chain.val+8*i.val)%2^64=(0x80000+8*j.val)%2^64 at h
    omega
  constructor
  · intro j eq
    have hj := j.isLt
    have h := congrArg BitVec.toNat eq
    change (0x80800+16*chain.val+8*i.val)%2^64=(0x80300+8*j.val)%2^64 at h
    omega
  · intro j eq
    have hj := j.isLt
    have h := congrArg BitVec.toNat eq
    change (0x80800+16*chain.val+8*i.val)%2^64=(0x80510+8*j.val)%2^64 at h
    omega

theorem endpoint_ne_chain (chain : Reference.Chain) (i : Fin 2) :
    KeygenEndpoint.endpointAddress chain.val i.val ≠ 0x80430 := by
  intro eq
  have h := congrArg BitVec.toNat eq
  change (0x80800+16*chain.val+8*i.val)%2^64=0x80430 at h
  have := chain.isLt
  have := i.isLt
  omega

theorem endpoint_separate (left right : Reference.Chain) (i j : Fin 2) (ne : left.val≠right.val) :
    KeygenEndpoint.endpointAddress left.val i.val ≠ KeygenEndpoint.endpointAddress right.val j.val := by
  intro eq
  have h := congrArg BitVec.toNat eq
  change (0x80800+16*left.val+8*i.val)%2^64=(0x80800+16*right.val+8*j.val)%2^64 at h
  have := left.isLt
  have := right.isLt
  have := i.isLt
  have := j.isLt
  omega

def Endpoints (hash : Hash) (secretKey : SecretKey) (level tree : Nat) (side : Bool) (n : Nat) (s : MachineState) : Prop :=
  ∀ chain : Reference.Chain, chain.val<n → ∀ i : Fin 2,
    s.getMem (KeygenEndpoint.endpointAddress chain.val i.val) =
      (Reference.endpoint hash secretKey level tree side chain).extractLsb' (64*i.val) 64

/-- One outer iteration derives a secret, performs seven chain rounds, and saves its endpoint. -/
theorem iteration (hash : Hash) (s : MachineState) (pc : s.pc=0x1204)
    (level tree : Nat) (side : Bool) (chain : Reference.Chain) (secretKey : SecretKey)
    (context : Context level tree side secretKey s)
    (counter : s.getMem 0x80430=BitVec.ofNat 64 chain.val)
    (before : Endpoints hash secretKey level tree side chain.val s) :
    ∃ final, Trace hash keygen s 823 879 8 8 final ∧
      final.pc=(if chain.val+1=46 then 0x1548 else 0x1204) ∧
      Context level tree side secretKey final ∧ final.getMem 0x80430=BitVec.ofNat 64 (chain.val+1) ∧
      Endpoints hash secretKey level tree side (chain.val+1) final ∧
      final.getReg .x1=s.getReg .x1 ∧ final.getReg .x2=s.getReg .x2 ∧
      (∀ a, Outside a → final.getMem a=s.getMem a) := by
  obtain ⟨ready,pre,rpc,inv,rra,rsp,rframe⟩ := KeygenSecretStart.prepare hash s pc level tree side chain secretKey context counter
  obtain ⟨ended,rounds,epc,einv,era,esp,eframe⟩ :=
    KeygenChainLoop.run hash 7 ready rpc level tree 0 side chain _ (by decide) inv
  obtain ⟨final,post,fpc,fcounter,words,fra,fsp,fframe⟩ :=
    KeygenEndpoint.store_endpoint keygen 0x14f4 (-832) KeygenEndpoint.keygen_code ended chain
      (Reference.endpoint hash secretKey level tree side chain) epc einv.chainWord einv.valueWords
  have finalFrame (a : Word) (outside : Outside a) : final.getMem a=s.getMem a := by
    rw [fframe a outside.1 (by
      intro i
      have h := outside.2.2 ⟨2*chain.val+i.val,by have := chain.isLt; have := i.isLt; omega⟩
      simpa [Signing.wordAddress,KeygenEndpoint.endpointAddress,Nat.mul_add,← Nat.mul_assoc,Nat.add_assoc] using h),
      eframe a outside.2.1,rframe a outside.2.1]
  refine ⟨final,pre.trans (rounds.trans post.trace),?_,?_,fcounter,?_,fra.trans (era.trans rra),fsp.trans (esp.trans rsp),finalFrame⟩
  · exact fpc
  · constructor
    · rw [finalFrame _ (by decide)]; exact context.levelWord
    · rw [finalFrame _ (by decide)]; exact context.leafWord
    · intro i; rw [finalFrame _ (by fin_cases i <;> decide)]; exact context.indexWords i
    · intro i; rw [finalFrame _ (by fin_cases i <;> decide)]; exact context.secretKeyWords i
    · rw [finalFrame _ (by decide)]; exact context.modeWord
  · intro old lt i
    by_cases eq : old=chain
    · subst old; exact words i
    · have ne : old.val≠chain.val := by intro he; apply eq; exact Fin.ext he
      rw [fframe _ (endpoint_ne_chain old i) (fun j => endpoint_separate old chain i j ne),
        eframe _ (endpoint_outside_work old i),rframe _ (endpoint_outside_work old i)]
      exact before old (by omega) i

/-- All46endpoint slots are populated with their exact reference values. -/
theorem loop (hash : Hash) (count : Nat) (s : MachineState) (n level tree : Nat)
    (side : Bool) (secretKey : SecretKey) (length : n+count=46)
    (pc : s.pc=(if n=46 then 0x1548 else 0x1204))
    (context : Context level tree side secretKey s)
    (counter : s.getMem 0x80430=BitVec.ofNat 64 n)
    (before : Endpoints hash secretKey level tree side n s) :
    ∃ final, Trace hash keygen s (823*count) (879*count) (8*count) (8*count) final ∧
      final.pc=0x1548 ∧ Context level tree side secretKey final ∧
      final.getMem 0x80430=46 ∧ Endpoints hash secretKey level tree side 46 final ∧
      final.getReg .x1=s.getReg .x1 ∧ final.getReg .x2=s.getReg .x2 ∧
      (∀ a, Outside a → final.getMem a=s.getMem a) := by
  induction count generalizing s n with
  | zero =>
    have hn : n=46 := by omega
    subst n
    refine ⟨s,Trace.refl _,?_,context,counter,before,rfl,rfl,fun _ _ => rfl⟩
    simpa using pc
  | succ count ih =>
    have hn : n<46 := by omega
    obtain ⟨next,pre,npc,ncontext,ncounter,nendpoints,nra,nsp,nframe⟩ :=
      iteration hash s (by simpa [show n≠46 by omega] using pc) level tree side ⟨n,hn⟩ secretKey context counter before
    obtain ⟨final,tail,fpc,fcontext,fcounter,fendpoints,fra,fsp,fframe⟩ :=
      ih next (n+1) (by omega) npc ncontext ncounter nendpoints
    refine ⟨final,?_,fpc,fcontext,fcounter,fendpoints,fra.trans nra,fsp.trans nsp,?_⟩
    · simpa [Nat.mul_add,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using pre.trans tail
    · intro a outside; rw [fframe a outside,nframe a outside]

/-- The endpoint invariant is exactly the92-word layout expected by leaf compression. -/
theorem endpoint_words (hash : Hash) (secretKey : SecretKey) (level tree : Nat) (side : Bool) (s : MachineState)
    (all : Endpoints hash secretKey level tree side 46 s) :
    ∀ i : Fin 92, s.getMem (Signing.wordAddress 0x80800 i.val) =
      KeygenLeafHeader.endpointWord (Reference.endpoint hash secretKey level tree side) i := by
  intro i
  have hc : i.val/2<46 := by have := i.isLt; omega
  have hw : i.val%2<2 := by omega
  have h := all ⟨i.val/2,hc⟩ hc ⟨i.val%2,hw⟩
  have addr : KeygenEndpoint.endpointAddress (i.val/2) (i.val%2)=Signing.wordAddress 0x80800 i.val := by
    unfold KeygenEndpoint.endpointAddress Signing.wordAddress
    congr 1
    omega
  rw [addr] at h
  exact h

/-- info: 'SigGolfCandidate.Hypertree.KeygenLeafLoop.loop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms loop

end SigGolfCandidate.Hypertree.KeygenLeafLoop
