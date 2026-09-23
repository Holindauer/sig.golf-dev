import SigGolf.Riscv

namespace SigGolf
open OracleComp OracleSpec RiscvZkvm.Rv64

/-- Every algorithm is fixed bytecode and embedded public data. -/
structure Submission where
  sizes : Sizes
  image : Phase → Riscv.Image

def Submission.score (submission : Submission) (cycles : Nat) : Nat :=
  submission.sizes.signature * cycles

def Input (sizes : Sizes) : Phase → Type
  | .keygen => SecretKey
  | .sign => SecretKey × PublicKey × Cache × Message
  | .expand => Message × PublicKey × Bytes sizes.signature
  | .verify => Message × PublicKey × Bytes sizes.witness

def Output (sizes : Sizes) : Phase → Type
  | .keygen => PublicKey × Cache
  | .sign => Bytes sizes.signature
  | .expand => Bytes sizes.witness
  | .verify => Unit

def bytes {n : Nat} (value : Bytes n) : List Byte :=
  (List.range n).map fun i => value.extractLsb' (8 * i) 8

def readBuffer (state : MachineState) (address n : Nat) : Bytes n :=
  BitVec.ofNat (8 * n) ((List.range n).foldl
    (fun acc i => acc + (state.getByte (BitVec.ofNat 64 (address + i))).toNat * 2 ^ (8 * i)) 0)

def inputBuffers (sizes : Sizes) : (phase : Phase) → Input sizes phase → List (Nat × List Byte)
  | .keygen, secretKey => [(0x20, bytes secretKey)]
  | .sign, (secretKey, pk, cache, message) =>
      [(0x20, bytes secretKey), (0x40, bytes pk), (0x60, bytes cache),
        (0, bytes message)]
  | .expand, (message, pk, signature) =>
      [(0, bytes message), (0x40, bytes pk), (Riscv.signatureBase, bytes signature)]
  | .verify, (message, pk, witness) =>
      [(0, bytes message), (0x40, bytes pk), (Riscv.witnessBase sizes, bytes witness)]

/-- Each execution starts with fresh zeroed memory and registers. Only declared inputs are loaded. -/
def initialState (submission : Submission) (phase : Phase) (input : Input submission.sizes phase) :
    Option MachineState :=
  let image := submission.image phase
  if image.Valid submission.sizes then
    let blank : MachineState :=
      { regs := fun _ => 0, mem := fun _ => 0, pc := 0x1000 }
    let withData := blank.writeBytesAsWords (BitVec.ofNat 64 (Riscv.dataBase image)) image.data
    let loaded := (inputBuffers submission.sizes phase input).foldl
      (fun state buffer => state.writeBytesAsWords (BitVec.ofNat 64 buffer.1) buffer.2) withData
    some (loaded.setReg .x2 (BitVec.ofNat 64 (Riscv.dataBase image)))
  else none

def readOutput (sizes : Sizes) : (phase : Phase) → MachineState → Output sizes phase
  | .keygen, state => (readBuffer state 0x40 16, readBuffer state 0x60 CACHE_BYTES)
  | .sign, state => readBuffer state Riscv.signatureBase sizes.signature
  | .expand, state => readBuffer state (Riscv.witnessBase sizes) sizes.witness
  | .verify, _ => ()

structure RunResult (α : Type) where
  value : Option α
  finished : Bool
  cycles : Nat
  hashCalls : Nat
  hashCompressions : Nat

/-- `CYCLE_LIMIT` is sufficient observation depth for the required strict cycle theorem. `finished = false` never counts as termination. -/
def Submission.run (submission : Submission) (phase : Phase) (input : Input submission.sizes phase) :
    OracleComp HashSpec (RunResult (Output submission.sizes phase)) := do
  match initialState submission phase input with
  | none => return ⟨none, true, 0, 0, 0⟩
  | some state =>
    let execution ← Riscv.execute CYCLE_LIMIT (submission.image phase) state
    return ⟨if execution.exit = .success then some (readOutput submission.sizes phase execution.state)
      else none, execution.exit != .unfinished, execution.cycles, execution.hashCalls,
      execution.hashCompressions⟩

/-- Fixed-oracle meaning, used in termination and verification-cycle claims. -/
def Submission.runWith (submission : Submission) (hash : Hash) (phase : Phase)
    (input : Input submission.sizes phase) : RunResult (Output submission.sizes phase) :=
  evalWithAnswerFn hash (submission.run phase input)

structure HonestResult where
  success : Bool
  costs : Phase → Nat
  verificationCycles : Nat

def recordCost (costs : Phase → Nat) (phase : Phase) (cost : Nat) : Phase → Nat :=
  fun other => if other = phase then cost else costs other

/-- One honest pipeline. Failed phases remain charged; phases not reached cost zero. -/
def Submission.honest (submission : Submission) (secretKey : SecretKey) (message : Message) :
    OracleComp HashSpec HonestResult := do
  let mut costs : Phase → Nat := fun _ => 0
  let keygen ← submission.run .keygen secretKey
  costs := recordCost costs .keygen keygen.hashCompressions
  let some (pk, cache) := keygen.value | return ⟨false, costs, 0⟩
  let sign ← submission.run .sign (secretKey, pk, cache, message)
  costs := recordCost costs .sign sign.hashCompressions
  let some signature := sign.value | return ⟨false, costs, 0⟩
  let expand ← submission.run .expand (message, pk, signature)
  costs := recordCost costs .expand expand.hashCompressions
  let some witness := expand.value | return ⟨false, costs, 0⟩
  let verify ← submission.run .verify (message, pk, witness)
  costs := recordCost costs .verify verify.hashCompressions
  return ⟨verify.value.isSome, costs, verify.cycles⟩

/-- Benchmark one independent uniform message against one freshly sampled shared random oracle. -/
noncomputable def Submission.honestWorkload (submission : Submission) (secretKey : SecretKey) :
    ProbComp HonestResult := do
  let message ← ($ᵗ Message : ProbComp Message)
  withRandomOracle (submission.honest secretKey message)

structure HonestSummary where
  allSucceed : Bool := true
  maxCosts : Phase → Nat := fun _ => 0

/-- All messages are evaluated against the same H. The maximum is taken before expectation, not over separate random-oracle experiments. This finite traversal defines a distribution; it is not an executable benchmark. -/
noncomputable def Submission.allMessages (submission : Submission) (secretKey : SecretKey) :
    OracleComp HashSpec HonestSummary :=
  (Finset.univ : Finset Message).toList.foldlM (fun summary message => do
    let result ← submission.honest secretKey message
    return ⟨summary.allSucceed && result.success,
      fun phase => max (summary.maxCosts phase) (result.costs phase)⟩) {}

end SigGolf
