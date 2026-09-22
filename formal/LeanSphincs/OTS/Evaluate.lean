import LeanSphincs.OTS.Graph
import Mathlib.Data.List.OfFn

/-! Byte-level execution and worst-case query metering for graph schedules.
This is not yet a signature scheme, a graph correctness theorem or a security
reduction. Invalid/missing-input schedules fail closed. Repeated gates are charged
again, so the bound does not assume the caller supplies a duplicate-free schedule. -/

open OracleComp OracleSpec

namespace LeanSphincs.OTS

open LeanSphincs.Benchmark

abbrev Value := BitVec 128
abbrev Values := Vertex → Option Value

/-- Fixed 16-byte little-endian representation. -/
def valueBytes (value : Value) : Bytes :=
  List.ofFn fun i : Fin 16 => UInt8.ofBitVec (value.extractLsb' (8 * i.val) 8)

@[simp] theorem valueBytes_length (value : Value) : (valueBytes value).length = 16 := by
  simp [valueBytes]

theorem valueBytes_injective : Function.Injective valueBytes := by
  intro x y h
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hbyte := congrFun (List.ofFn_injective h) (⟨i / 8, by omega⟩ : Fin 16)
  have hbits := congrArg (fun byte : UInt8 => byte.toBitVec.getLsbD (i % 8)) hbyte
  have hmod : i % 8 < 8 := by omega
  have hindex : 8 * (i / 8) + i % 8 = i := by omega
  simpa [BitVec.getLsbD_extractLsb', hmod, hindex] using hbits

def inputValues (inputs : List Vertex) (known : Values) : Bytes :=
  inputs.flatMap fun v => valueBytes ((known v).getD 0)

@[simp] theorem inputValues_length (inputs : List Vertex) (known : Values) :
    (inputValues inputs known).length = 16 * inputs.length := by
  induction inputs with
  | nil => simp [inputValues]
  | cons v rest ih => simp_all [inputValues, Nat.mul_add, Nat.add_comm]

def Gate.queryInput (g : Gate) (known : Values) : Bytes :=
  valueBytes (BitVec.ofNat 128 g.address.val) ++ inputValues g.inputs known

@[simp] theorem Gate.queryInput_length (g : Gate) (known : Values) :
    (g.queryInput known).length = 16 + 16 * g.inputs.length := by
  simp [Gate.queryInput]

/-- Different encoded gate addresses cannot alias, regardless of gate values. -/
theorem Gate.queryInput_address (g h : Gate) (left right : Values)
    (heq : g.queryInput left = h.queryInput right) : g.address = h.address := by
  have leadingBytes := congrArg (List.take 16) heq
  have values : valueBytes (BitVec.ofNat 128 g.address.val) =
      valueBytes (BitVec.ofNat 128 h.address.val) := by
    simpa [Gate.queryInput, List.take_append] using leadingBytes
  have numbers := congrArg BitVec.toNat (valueBytes_injective values)
  apply Fin.ext
  simpa [Nat.mod_eq_of_lt g.address.isLt, Nat.mod_eq_of_lt h.address.isLt] using numbers

theorem Gate.queryInput_weight (g : Gate) (known : Values) :
    hashWeight (g.queryInput known) = g.cost := by
  simp [hashWeight, Gate.cost]

/-- The default zero in queryInput is never used for a missing value: the
presence guard returns none before making any oracle call. -/
def Gate.evaluate (g : Gate) (known : Values) : OracleComp HashSpec (Option HashOutput) :=
  if ∀ v ∈ g.inputs, (known v).isSome then do
    let output ← liftM (HashSpec.query (g.queryInput known))
    pure (some output)
  else pure none

theorem Gate.evaluate_cost (g : Gate) (known : Values) :
    HasVerifyCost (g.evaluate known) g.cost := by
  unfold Gate.evaluate
  split
  · have hquery : HasVerifyCost (liftM (HashSpec.query (g.queryInput known))) g.cost := by
      rw [hasVerifyCost_query_iff, Gate.queryInput_weight]
    simpa using hquery.bind (fun output => HasVerifyCost.pure (some output) 0)
  · exact HasVerifyCost.pure none g.cost

def writeOutputs (known : Values) (index : Nat) (output : HashOutput) : Values
  | .source i => known (.source i)
  | .output producer slot =>
      if producer = index then some (output.extractLsb' (128 * slot.val) 128)
      else known (.output producer slot)

def Graph.scheduleCost (g : Graph) : List (Fin g.gates.length) → Nat
  | [] => 0
  | i :: rest => (g.gates.get i).cost + g.scheduleCost rest

theorem Graph.scheduleCost_eq_reconstruction (g : Graph)
    (schedule : List (Fin g.gates.length)) (distinct : schedule.Nodup) :
    g.scheduleCost schedule = g.reconstructionCost schedule.toFinset := by
  induction schedule with
  | nil => simp [Graph.scheduleCost, Graph.reconstructionCost]
  | cons i rest ih =>
    have hnot : i ∉ rest.toFinset := by simpa using (List.nodup_cons.mp distinct).1
    calc
      g.scheduleCost (i :: rest) = (g.gates.get i).cost + g.reconstructionCost rest.toFinset :=
        congrArg (fun cost => (g.gates.get i).cost + cost) (ih (List.nodup_cons.mp distinct).2)
      _ = g.reconstructionCost (i :: rest).toFinset := by
        simp [Graph.reconstructionCost, hnot]

theorem Graph.scheduleCost_le_keygen (g : Graph)
    (schedule : List (Fin g.gates.length)) (distinct : schedule.Nodup) :
    g.scheduleCost schedule ≤ g.keygenCost := by
  rw [g.scheduleCost_eq_reconstruction schedule distinct]
  exact g.reconstructionCost_le _

def Graph.evaluate (g : Graph) (known : Values) :
    List (Fin g.gates.length) → OracleComp HashSpec (Option Value)
  | [] => pure (known g.root)
  | i :: rest => do
      match ← (g.gates.get i).evaluate known with
      | none => pure none
      | some output => g.evaluate (writeOutputs known i.val output) rest

/-- Worst-case block-weighted cost on every oracle response path, including
missing inputs and repeated gates. This is the protected VCVio query predicate,
not just arithmetic about a graph drawing. -/
theorem Graph.evaluate_cost (g : Graph) (known : Values) (schedule : List (Fin g.gates.length)) :
    HasVerifyCost (g.evaluate known schedule) (g.scheduleCost schedule) := by
  induction schedule generalizing known with
  | nil => exact HasVerifyCost.pure _ 0
  | cons i rest ih =>
    apply (Gate.evaluate_cost (g.gates.get i) known).bind
    intro output
    cases output with
    | none => exact HasVerifyCost.pure none (g.scheduleCost rest)
    | some output => exact ih (writeOutputs known i.val output)

end LeanSphincs.OTS
