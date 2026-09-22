import SigGolfCandidate.Hypertree.KeygenBlocks
import SigGolfCandidate.Hypertree.KeygenTrace

namespace SigGolfCandidate.Resources
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 OracleComp

/-- A finite map of known values; omitted entries carry no information. -/
def lookup {α : Type} [DecidableEq α] (key : α) : List (α × Word) → Option Word
  | [] => none
  | (k, v) :: rest => if key = k then some v else lookup key rest

def update {α : Type} [DecidableEq α] (key : α) (value : Option Word)
    (entries : List (α × Word)) : List (α × Word) :=
  let rest := entries.filter fun entry => decide (entry.1 ≠ key)
  match value with
  | none => rest
  | some value => (key, value) :: rest

theorem lookup_filter {α : Type} [DecidableEq α] (key other : α) (entries : List (α × Word)) :
    lookup other (entries.filter fun entry => decide (entry.1 ≠ key)) =
      if other = key then none else lookup other entries := by
  induction entries with
  | nil => simp [lookup]
  | cons entry entries ih =>
    rcases entry with ⟨k,v⟩
    by_cases h : k = key <;> by_cases h' : other = key <;> by_cases h'' : other = k <;>
      simp_all [lookup]

theorem lookup_update {α : Type} [DecidableEq α] (key other : α) (value : Option Word)
    (entries : List (α × Word)) :
    lookup other (update key value entries) = if other = key then value else lookup other entries := by
  cases value <;> simp only [update, lookup, lookup_filter]
  split <;> rfl

/-- Known control data, separated from arbitrary input and oracle-dependent words. -/
structure AbstractState where
  pc : Word
  regs : List (Reg × Word)
  mem : List (Word × Word)
  deriving DecidableEq, Repr

def AbstractState.getReg (a : AbstractState) (r : Reg) : Option Word :=
  if r = .x0 then some 0 else lookup r a.regs

def AbstractState.setReg (a : AbstractState) (r : Reg) (v : Option Word) : AbstractState :=
  { a with regs := update r v a.regs }

def AbstractState.setMem (a : AbstractState) (p : Word) (v : Option Word) : AbstractState :=
  { a with mem := update p v a.mem }

def AbstractState.setPC (a : AbstractState) (p : Word) : AbstractState := { a with pc := p }

def Knows (a : Option Word) (v : Word) : Prop := ∀ w, a = some w → v = w

structure AbstractState.Models (a : AbstractState) (s : MachineState) : Prop where
  pc : s.pc = a.pc
  regs : ∀ r, Knows (a.getReg r) (s.getReg r)
  mem : ∀ p, Knows (lookup p a.mem) (s.getMem p)

theorem Knows.none (v : Word) : Knows none v := by intro w h; cases h

theorem Knows.some (v : Word) : Knows (some v) v := by intro w h; exact Option.some.inj h

theorem Knows.map (f : Word → Word) {v : Option Word} {w : Word} (h : Knows v w) :
    Knows (v.map f) (f w) := by
  cases v with
  | none => exact Knows.none _
  | some v => have hv := h v rfl; subst w; exact Knows.some _

def map₂ (f : Word → Word → Word) (a b : Option Word) : Option Word := do
  return f (← a) (← b)

theorem Knows.map₂ (f : Word → Word → Word) {a b : Option Word} {v w : Word}
    (ha : Knows a v) (hb : Knows b w) : Knows (map₂ f a b) (f v w) := by
  cases a with
  | none => exact Knows.none _
  | some a =>
    cases b with
    | none => exact Knows.none _
    | some b =>
      have h₁ := ha a rfl; have h₂ := hb b rfl
      subst v; subst w; exact Knows.some _

theorem AbstractState.Models.setPC {a : AbstractState} {s : MachineState}
    (h : a.Models s) (p : Word) : (a.setPC p).Models (s.setPC p) := by
  exact ⟨rfl, h.regs, h.mem⟩

theorem AbstractState.Models.setReg {a : AbstractState} {s : MachineState}
    (h : a.Models s) (r : Reg) {v : Option Word} {w : Word} (known : Knows v w) :
    (a.setReg r v).Models (s.setReg r w) := by
  refine ⟨by simpa [AbstractState.setReg] using h.pc, ?_, ?_⟩
  · intro other value eq
    by_cases hz : other = .x0
    · subst other
      simp [AbstractState.getReg] at eq
      subst value
      rfl
    · by_cases hr : other = r
      · subst other
        have hv : v = some value := by
          simpa [AbstractState.getReg, hz, AbstractState.setReg, lookup_update] using eq
        rw [MachineState.getReg_setReg_eq hz]
        exact known value hv
      · have hv : a.getReg other = some value := by
          simpa [AbstractState.getReg, hz, hr, AbstractState.setReg, lookup_update] using eq
        rw [MachineState.getReg_setReg_ne s r other w (Ne.symm hr)]
        exact h.regs other value hv
  · intro p
    simpa only [AbstractState.setReg, MachineState.getMem_setReg] using h.mem p

theorem AbstractState.Models.setMem {a : AbstractState} {s : MachineState}
    (h : a.Models s) (p : Word) {v : Option Word} {w : Word} (known : Knows v w) :
    (a.setMem p v).Models (s.setMem p w) := by
  refine ⟨h.pc, ?_, ?_⟩
  · intro r
    simpa only [AbstractState.setMem, AbstractState.getReg, Hypertree.Expansion.reg_setMem] using h.regs r
  · intro other value eq
    by_cases hp : other = p
    · subst other
      have hv : v = some value := by simpa [AbstractState.setMem, lookup_update] using eq
      rw [Hypertree.Expansion.mem_setMem, if_pos rfl]
      exact known value hv
    · have hv : lookup other a.mem = some value := by
        simpa [AbstractState.setMem, lookup_update, hp] using eq
      rw [Hypertree.Expansion.mem_setMem, if_neg hp]
      exact h.mem other value hv

end SigGolfCandidate.Resources
