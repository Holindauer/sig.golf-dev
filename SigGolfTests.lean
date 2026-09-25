import SigGolf

namespace SigGolf.Tests
open OracleComp Riscv RiscvZkvm.Rv64

private def blank : MachineState := { regs := fun _ => 0, mem := fun _ => 0, pc := 0x1000 }
private def zeroHash : Hash := fun _ => 0
private def addi (rd rs : Nat) (immediate : Nat) : BitVec 32 :=
  BitVec.ofNat 32 ((immediate % 4096) * 2 ^ 20 + rs * 2 ^ 15 + rd * 2 ^ 7 + 0x13)
private def acceptImage : Image := ⟨[addi 10 0 1, 0x73], []⟩
private def hashImage (bytes : Nat) : Image :=
  ⟨[addi 5 0 1, addi 10 0 0, addi 11 0 bytes, addi 12 0 0, 0x73,
    addi 5 0 0, addi 10 0 1, 0x73], []⟩
private def toy : Submission := ⟨⟨1, 1⟩, standardLayout ⟨1, 1⟩, fun _ => hashImage 72⟩
private def movedLayout : Layout := ⟨0x40000, 0x40020, 0x40040, 0x50000, 0x80000, 0x81000⟩
private def movedToy : Submission := { toy with layout := movedLayout }
private def runSmall (image : Image) (state : MachineState := blank) : Execution :=
  evalWithAnswerFn zeroHash (execute 20 image state)

-- Kernel-checked boundary cases, independent of the compiled evaluator.
example : compressions 0 = 1 ∧ compressions 512 = 1 ∧ compressions 513 = 2 := by decide
example : witnessCycles 0 = 0 ∧ witnessCycles 1 = 1 ∧ witnessCycles 256 = 1 ∧ witnessCycles 257 = 2 := by decide
example : accessValid 0 8 = true ∧ accessValid 1 8 = false := by decide
example : rangeValid 0xfffff8 8 = true ∧ rangeValid 0xfffff8 9 = false := by decide
example : rangeValid 0xffffffffffffffff 2 = false := by decide
example : accessValid 0x100000 8 = true ∧ accessValid 0x1000000 8 = false := by decide
example : MEMORY_BYTES = 16777216 ∧ MAX_IMAGE_BYTES = 1048576 := by decide
example (image : Image) (sizes : Sizes) (h : image.byteSize = MAX_IMAGE_BYTES) :
    ¬ image.Valid sizes (standardLayout sizes) := by
  intro valid
  have bound := valid.1
  omega
example : wordResult .div 0x80000000 0xffffffff = 0x80000000 := by decide
example : wordResult .div 7 0 = 0xffffffff ∧ wordResult .rem 7 0 = 7 := by decide
example : wordResult .sll 1 32 = 1 ∧ wordResult .sra 0x80000000 31 = 0xffffffff := by decide
example : witnessBase ⟨1, 1⟩ = 0x20068 ∧ witnessBase ⟨9, 1⟩ = 0x20070 := by decide
example : (hashImage 72).Valid ⟨1, 1⟩ movedLayout := by decide
example : ¬ (hashImage 72).Valid ⟨1, 1⟩
    { movedLayout with publicKey := movedLayout.message } := by decide
example : ¬ ({ hashImage 72 with data := List.replicate 32 0 } : Image).Valid ⟨1, 1⟩
    { standardLayout ⟨1, 1⟩ with witness := MEMORY_BYTES - 16 } := by decide

private def fixedWorld : QueryImpl World Id
  | .inl n => ⟨0, Nat.zero_lt_succ n⟩
  | .inr _ => (0 : BitVec 256)

private def repeatHasher : Adversary toy.sizes where
  State := Nat
  initial := fun _ _ => 0
  step := fun state => if state < 2 then .hash ⟨0, 0⟩ (fun _ => state + 1)
    else .submit (.witness 8 0)

private def signer : Adversary toy.sizes where
  State := Bool
  initial := fun _ _ => false
  step := fun done => if done then .submit (.witness 8 0)
    else .sign ⟨7, 0⟩ (fun _ => true)

private def cacheEcho : Submission where
  sizes := ⟨1, 1⟩
  layout := standardLayout ⟨1, 1⟩
  image
    | .sign => ⟨(hashImage 72).code.take 5 ++
        [0x00020437, addi 8 8 0x60, 0x06004383, 0x00740023,
          addi 5 0 0, addi 10 0 1, 0x73], []⟩
    | _ => acceptImage

private def failedSign : Submission where
  sizes := ⟨1, 1⟩
  layout := standardLayout ⟨1, 1⟩
  image
    | .sign => ⟨(hashImage 72).code.take 5 ++ [addi 5 0 0, addi 10 0 0, 0x73], []⟩
    | phase => cacheEcho.image phase

private def check (label : String) (condition : Bool) : IO Unit :=
  unless condition do throw (IO.userError label)

-- These are interpreter and game regressions, not a certificate for the deliberately insecure toy programs.
#eval do
  let halted := runSmall acceptImage
  check "HALT is charged" (halted.exit == Exit.success && halted.cycles == 2)
  let one := runSmall (hashImage 64)
  let two := runSmall (hashImage 72)
  check "HASH has no extra ECALL charge" (one.cycles == 15 && two.cycles == 23)
  let partialWord := runSmall (hashImage 65)
  check "HASH rejects partial words" (partialWord.exit == Exit.failure && partialWord.hashCalls == 0)
  check "multiplication and division cost four cycles"
    ((runSmall ⟨[0x020000b3, 0x020040b3, 0x020070bb, 0x000000b3, addi 10 0 1, 0x73], []⟩).cycles == 15)
  check "hash calls differ from compressions" (two.hashCalls == 1 && two.hashCompressions == 2)
  let emptyHash := runSmall (hashImage 0)
  check "empty HASH still costs one compression" (emptyHash.hashCompressions == 1)
  let looping := runSmall ⟨[0x0000006f], []⟩
  check "observation exhaustion is not termination" (looping.exit == Exit.unfinished && looping.cycles == 20)
  check "malformed ECALL encoding fails" (decodeInstruction 0x000000f3 |>.isNone)
  check "CSR instructions are not exposed" (decodeInstruction 0x00002073 |>.isNone)
  check "EBREAK fails" ((runSmall ⟨[0x00100073], []⟩).exit == Exit.failure)
  check "invalid HALT status fails" ((runSmall ⟨[addi 10 0 2, 0x73], []⟩).exit == Exit.failure)
  check "misaligned PC fails" ((runSmall acceptImage { blank with pc := 0x1002 }).exit == Exit.failure)
  check "x0 stays zero" ((blank.setReg .x0 123).getReg .x0 == 0)
  check "all RV64 word operations decode"
    ([0x007302bb, 0x407302bb, 0x007312bb, 0x007352bb, 0x407352bb,
      0x027302bb, 0x027342bb, 0x027352bb, 0x027362bb, 0x027372bb,
      0x0013129b, 0x0013529b, 0x4013529b].all (fun w => (decodeInstruction w).isSome))
  let state := ((blank.setReg .x10 0).setReg .x11 8).setReg .x12 0
  let state := (state.setByte 0 0xa5).setByte 1 0xff
  check "HASH reads little-endian bytes" ((hashInput state).1 == 64 && (hashInput state).2.toNat == 0xffa5)
  let written := writeHash state 0x1234
  check "HASH writes little-endian and preserves registers"
    (written.getByte 0 == 0x34 && written.getByte 1 == 0x12 && written.getReg .x11 == 8 && written.pc == 0x1004)
  check "HASH rejects unaligned input" (!hashArgumentsValid (state.setReg .x10 1))
  check "HASH rejects unaligned output" (!hashArgumentsValid (state.setReg .x12 4))
  check "HASH rejects output crossing memory end" (!hashArgumentsValid (state.setReg .x12 0xfffff8))
  check "HASH rejects lengths that are not whole words" (!hashArgumentsValid (state.setReg .x11 9))
  check "HASH accepts a final in-bounds word" (hashArgumentsValid (state.setReg .x10 0xfffff8))
  check "HASH rejects input crossing memory end"
    (!hashArgumentsValid ((state.setReg .x10 0xfffff8).setReg .x11 16))
  let faulty := runSmall ⟨[0x73], []⟩ ((state.setReg .x5 1).setReg .x12 0xfffff8)
  check "invalid HASH makes no oracle call" (faulty.exit == Exit.failure && faulty.hashCalls == 0)
  check "load at address zero is valid" (memoryArgumentsValid blank (.LD .x1 .x0 0))
  check "load alignment is enforced" (!memoryArgumentsValid blank (.LD .x1 .x0 1))
  let transcript : Transcript toy.sizes := { signed := [(7, 9)], signingRequests := 1, hashCalls := 11 }
  let failed := transcript.record 8 ⟨none, true, 4, 2, 3⟩
  check "failed signing consumes a slot and hash calls"
    (failed.signingRequests == 2 && failed.hashCalls == 13 && failed.signed == [(7, 9)])
  check "witness replays excluded by message" (!transcript.freshMessage 7 && transcript.freshMessage 8)
  check "signature replays excluded by exact pair"
    (!transcript.freshSignature 7 9 && transcript.freshSignature 7 10)
  let witness := evalWithAnswerFn zeroHash (toy.checkForgery 0 transcript (.witness 8 0))
  let signature := evalWithAnswerFn zeroHash (toy.checkForgery 0 transcript (.signature 7 10))
  check "witness final check charged" (witness.won && witness.hashCalls == 12)
  check "expansion and final verification charged" (signature.won && signature.hashCalls == 13)
  let replay := evalWithAnswerFn zeroHash (toy.checkForgery 0 transcript (.signature 7 9))
  check "signature replay loses despite acceptance" (!replay.won && replay.hashCalls == 13)
  let wrongMessage := evalWithAnswerFn zeroHash (toy.checkForgery 0 transcript (.witness 7 0))
  check "signed-message witness loses despite acceptance" (!wrongMessage.won)
  let repeated := evalWithAnswerFn fixedWorld (toy.interact repeatHasher 0 0 3 (repeatHasher.initial 0 0) transcript)
  check "repeated attacker queries still charged" (repeated.won && repeated.hashCalls == 14)
  let observed :=  evalWithAnswerFn fixedWorld (toy.interact repeatHasher 0 0 2 (repeatHasher.initial 0 0) transcript)
  check "no win before final submission" (!observed.won && observed.hashCalls == 13)
  let exhausted := evalWithAnswerFn fixedWorld (toy.interact signer 0 0 3 false
    { transcript with signingRequests := LIFETIME })
  check "signing lifetime enforced before execution" (!exhausted.won && exhausted.hashCalls == 11)
  let initialized := initialState toy .verify (0x34, 0x56, 0x78)
  match initialized with
  | none => throw (IO.userError "admissible image rejected by loader")
  | some state =>
    check "fixed input buffers" (state.getByte 0 == 0x34 && state.getByte 0x40 == 0x56 &&
      state.getByte (BitVec.ofNat 64 (witnessBase toy.sizes)) == 0x78)
    check "undeclared secretKey and cache are zero" (state.getByte 0x20 == 0 && state.getByte 0x60 == 0)
    check "initial registers" (state.pc == 0x1000 && state.getReg .x2 == 0x1000000 && state.getReg .x10 == 0)
  match initialState toy .sign (0x12, 0x9a, 0x34) with
  | none => throw (IO.userError "admissible image rejected by loader")
  | some state =>
    check "sign inputs exclude the public key" (state.getByte 0x20 == 0x12 &&
      state.getByte 0x60 == 0x9a && state.getByte 0 == 0x34 && state.getByte 0x40 == 0)
  match initialState movedToy .verify (0x34, 0x56, 0x78) with
  | none => throw (IO.userError "custom layout rejected by loader")
  | some state =>
    check "custom input offsets" (state.getByte movedLayout.message == 0x34 &&
      state.getByte movedLayout.publicKey == 0x56 && state.getByte movedLayout.witness == 0x78)
    check "former input offsets stay zero" (state.getByte 0x40 == 0 &&
      state.getByte (BitVec.ofNat 64 (witnessBase movedToy.sizes)) == 0)
  let outputState := blank.writeBytesAsWords (BitVec.ofNat 64 movedLayout.signature) [0x5a]
  let output : BitVec 8 := readOutput movedToy.sizes movedToy.layout .sign outputState
  check "custom output offset" (output == 0x5a)
  let signed := evalWithAnswerFn zeroHash (cacheEcho.signingOracle 0 ⟨7, 0xa5⟩)
  check "attacker cache reaches sign" (signed.value == some (0xa5 : BitVec 8) && signed.finished)
  check "all signing work is charged" (signed.hashCalls == 1 && signed.hashCompressions == 2)
  let denied := evalWithAnswerFn zeroHash (failedSign.signingOracle 0 ⟨7, 0xa5⟩)
  check "failed signing retains its cost"
    (denied.value.isNone && denied.finished && denied.hashCalls == 1 && denied.hashCompressions == 2)
  IO.println "RISC-V and security regressions passed."

/-- info: 'SigGolf.Certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SigGolf.Certificate

end SigGolf.Tests
