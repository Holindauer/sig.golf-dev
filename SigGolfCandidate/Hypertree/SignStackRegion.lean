import SigGolfCandidate.Hypertree.ControlRegion
import SigGolfCandidate.Hypertree.SignSites
namespace SigGolfCandidate.Hypertree.Signing
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 Keygen
set_option maxRecDepth 4096

theorem tree_enter_region (hash : Hash) (s : MachineState) (pc : s.pc = 0x13c8)
    (stack : accessValid (s.getReg .x2 - 16) 8 = true) :
    RegionTrace (fun st => 0x1004 ≤ st.pc.toNat ∧ st.pc.toNat < 0x1c70)
      hash sign s 2 2 0 0 (enterState s) := by
  exact enter_region (fun p => 0x1004 ≤ p.toNat ∧ p.toNat < 0x1c70) hash sign 0x13c8
    (by decide) (by intro i; fin_cases i <;> decide) s pc stack

theorem leaf_enter_region (hash : Hash) (s : MachineState) (pc : s.pc = 0x154c)
    (stack : accessValid (s.getReg .x2 - 16) 8 = true) :
    RegionTrace (fun st => 0x1004 ≤ st.pc.toNat ∧ st.pc.toNat < 0x1c70)
      hash sign s 2 2 0 0 (enterState s) := by
  exact enter_region (fun p => 0x1004 ≤ p.toNat ∧ p.toNat < 0x1c70) hash sign 0x154c
    (by decide) (by intro i; fin_cases i <;> decide) s pc stack

theorem leaf_return_region (hash : Hash) (s : MachineState) (pc : s.pc = 0x19d0)
    (stack : accessValid (s.getReg .x2) 8 = true) :
    RegionTrace (fun st => 0x1004 ≤ st.pc.toNat ∧ st.pc.toNat < 0x1c70)
      hash sign s 3 3 0 0 (returnState s) := by
  exact return_region (fun p => 0x1004 ≤ p.toNat ∧ p.toNat < 0x1c70) hash sign 0x19d0
    (by decide) (by intro i; fin_cases i <;> decide) s pc stack

theorem bottom_return_region (hash : Hash) (s : MachineState) (pc : s.pc = 0x1c64)
    (stack : accessValid (s.getReg .x2) 8 = true) :
    RegionTrace (fun st => 0x1004 ≤ st.pc.toNat ∧ st.pc.toNat < 0x1c70)
      hash sign s 3 3 0 0 (returnState s) := by
  exact return_region (fun p => 0x1004 ≤ p.toNat ∧ p.toNat < 0x1c70) hash sign 0x1c64
    (by decide) (by intro i; fin_cases i <;> decide) s pc stack

theorem node_return_region (hash : Hash) (s : MachineState) (pc : s.pc = 0x1540)
    (stack : accessValid (s.getReg .x2) 8 = true) :
    RegionTrace (fun st => 0x1004 ≤ st.pc.toNat ∧ st.pc.toNat < 0x1c70)
      hash sign s 3 3 0 0 (returnState s) := by
  exact return_region (fun p => 0x1004 ≤ p.toNat ∧ p.toNat < 0x1c70) hash sign 0x1540
    (by decide) (by intro i; fin_cases i <;> decide) s pc stack

/-- info: 'SigGolfCandidate.Hypertree.Signing.bottom_return_region' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms bottom_return_region
end SigGolfCandidate.Hypertree.Signing
