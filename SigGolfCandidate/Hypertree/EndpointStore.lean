import SigGolfCandidate.Hypertree.KeygenEndpoint

namespace SigGolfCandidate.Hypertree.KeygenEndpoint
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 Keygen Signing
set_option maxRecDepth 4096

def endpointAddress (chain word : Nat) : Word := BitVec.ofNat 64 (0x80800 + 16*chain + 8*word)

/-- Store a recovered chain endpoint and dispatch the next chain, or the leaf-compression suffix. -/
theorem store_endpoint (image : Image) (base : Word) (offset : BitVec 13) (code : Code image base offset)
    (s : MachineState) (chain : Reference.Chain) (value : Reference.Digest)
    (pc : s.pc = base) (counter : s.getMem 0x80430 = BitVec.ofNat 64 chain.val)
    (valueWords : ∀ i : Fin 2, s.getMem (wordAddress 0x80510 i.val) = value.extractLsb' (64*i.val) 64) :
    ∃ final, OrdinarySteps image s 21 final ∧
      final.pc = (if chain.val+1 = 46 then base+84 else base+80+signExtend13 offset) ∧
      final.getMem 0x80430 = BitVec.ofNat 64 (chain.val+1) ∧
      (∀ i : Fin 2, final.getMem (endpointAddress chain.val i.val) = value.extractLsb' (64*i.val) 64) ∧
      final.getReg .x1 = s.getReg .x1 ∧ final.getReg .x2 = s.getReg .x2 ∧
      (∀ a, a ≠ 0x80430 → (∀ i : Fin 2, a ≠ endpointAddress chain.val i.val) → final.getMem a = s.getMem a) := by
  have safe := KeygenEndpoint.address_safe s chain.val chain.isLt counter
  have addr : KeygenEndpoint.address s = endpointAddress chain.val 0 := by
    simpa only [endpointAddress, Nat.mul_zero, Nat.add_zero] using KeygenEndpoint.address_eq s chain.val counter
  have addr8 : KeygenEndpoint.address s + 8 = endpointAddress chain.val 1 := by
    rw [addr]
    change BitVec.ofNat 64 (0x80800+16*chain.val+8*0) + BitVec.ofNat 64 8 = _
    rw [← BitVec.ofNat_add]
    rfl
  have inc : s.getMem 0x80430 + 1 = BitVec.ofNat 64 (chain.val+1) := by
    rw [counter, BitVec.ofNat_add]; rfl
  have eq : s.getMem 0x80430 + 1 = 46 ↔ chain.val+1 = 46 := by
    rw [inc]
    constructor
    · intro same
      have h := congrArg BitVec.toNat same
      change (chain.val+1) % 2^64 = 46 at h
      have := chain.isLt
      omega
    · intro same; rw [same]; rfl
  have neCounter (i : Fin 2) : endpointAddress chain.val i.val ≠ 0x80430 := by
    intro same
    have h := congrArg BitVec.toNat same
    simp only [endpointAddress, BitVec.toNat_ofNat] at h
    have hc := chain.isLt
    have hi := i.isLt
    have small : 0x80800 + 16*chain.val + 8*i.val < 2^64 := by omega
    change (0x80800 + 16*chain.val + 8*i.val) % 2^64 = 0x80430 at h
    rw [Nat.mod_eq_of_lt small] at h
    omega
  have separate : endpointAddress chain.val 0 ≠ endpointAddress chain.val 1 := by
    intro same
    have h := congrArg BitVec.toNat same
    simp only [endpointAddress, BitVec.toNat_ofNat] at h
    have := chain.isLt
    omega
  refine ⟨KeygenEndpoint.state s offset,
    KeygenEndpoint.block image base offset code s pc safe.1 safe.2, ?_, ?_, ?_,
    (KeygenEndpoint.stack s offset).1, (KeygenEndpoint.stack s offset).2, ?_⟩
  · rw [KeygenEndpoint.pc, pc]
    simp only [eq]
  · rw [KeygenEndpoint.mem, if_pos rfl, inc]
  · intro i
    rw [KeygenEndpoint.mem, if_neg (neCounter i), addr8, addr]
    fin_cases i
    · rw [if_neg separate, if_pos rfl]; exact valueWords 0
    · rw [if_pos rfl]; exact valueWords 1
  · intro a hc outside
    have h0 : a ≠ endpointAddress chain.val 0 := outside 0
    have h1 : a ≠ endpointAddress chain.val 1 := outside 1
    rw [KeygenEndpoint.mem, if_neg hc, addr8, if_neg h1, addr, if_neg h0]

/-- info: 'SigGolfCandidate.Hypertree.KeygenEndpoint.store_endpoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms store_endpoint

end SigGolfCandidate.Hypertree.KeygenEndpoint
