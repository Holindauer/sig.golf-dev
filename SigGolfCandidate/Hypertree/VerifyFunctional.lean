import SigGolfCandidate.Hypertree.VerifyFunctionalEntry

namespace SigGolfCandidate.Hypertree.Verifying
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 Keygen Signing
set_option maxRecDepth 4096
attribute [local instance] Classical.propDecidable

/-- The complete protected verifier reaches its final root comparison on every typed input. -/
theorem loaded_recovery (hash : Hash) (pk : PublicKey) (message : Message) (witness : Bytes signatureBytes) :
    ∃ initial recovered steps cycles calls blocks,
      initialState submission .verify (message, pk, witness) = some initial ∧
      Trace hash verify initial steps cycles calls blocks recovered ∧
      steps ≤ 5506530 ∧ cycles ≤ 3414004 ∧ calls ≤ 51841 ∧ blocks ≤ 53602 ∧
      recovered.pc = 0x1220 ∧
      (RootMatches recovered ↔ Reference.verify hash pk message (SignatureEncoding.decode witness).toReference) := by
  obtain ⟨initial, ready, loaded, pre, pc, data, preFrame⟩ := loaded_loop_data hash pk message witness
  let index := (Reference.indexOf hash pk message (SignatureEncoding.decode witness).randomizer).toNat
  have indexSmall : index < 2^192 := by
    have h := (Reference.indexOf hash pk message (SignatureEncoding.decode witness).randomizer).isLt
    dsimp [index]
    omega
  obtain ⟨recovered, steps, cycles, calls, blocks, lastIndex, run, hsteps, hcycles, hcalls, hblocks, finalPC, finalData, frame⟩ :=
    verify_layers hash witness 160 0 index ready 0 rfl indexSmall (by simpa using pc) data
  change cycles + 21181 ≤ 21469*160 at hcycles
  have allFrame := preFrame.trans initial ready recovered frame
  have pkWords : ∀ i : Fin 2, recovered.getMem (wordAddress 0x40 i.val) = pk.extractLsb' (64*i.val) 64 := by
    intro i
    have same := allFrame (0x40+8*i.val) (by omega) (by have := i.isLt; omega)
    change recovered.getMem (wordAddress 0x40 i.val) = initial.getMem (wordAddress 0x40 i.val) at same
    rw [same]
    exact loaded_publicKey_word pk message witness initial loaded i
  have matchRoot := root_matches_iff recovered _ pk finalData.currentEq pkWords
  refine ⟨initial, recovered, 130+steps, 145+cycles, 1+calls, 2+blocks,
    loaded, pre.trans run, by omega, by omega, by omega, by omega, finalPC, ?_⟩
  rw [matchRoot, wire_layers_decode]
  have length : (SignatureEncoding.decode witness).toReference.layers.length = 160 := by
    simp [SignatureEncoding.decode, SignatureEncoding.Compact.toReference]
  simp only [Reference.verify, length, true_and]
  rfl

/-- Universal bytecode refinement, including malformed witnesses and exact accept/reject behavior. -/
theorem run_refines (hash : Hash) (pk : PublicKey) (message : Message) (witness : Bytes signatureBytes) :
    ∃ cycles calls blocks, cycles ≤ 3414019 ∧ calls ≤ 51841 ∧ blocks ≤ 53602 ∧
      submission.runWith hash .verify (message, pk, witness) =
        ⟨if Reference.verify hash pk message (SignatureEncoding.decode witness).toReference then some () else none,
          true, cycles, calls, blocks⟩ := by
  classical
  obtain ⟨initial, recovered, steps, cycles, calls, blocks, loaded, run, hsteps, hcycles, hcalls, hblocks, pc, accepted⟩ :=
    loaded_recovery hash pk message witness
  obtain ⟨tailSteps, final, tailBound, tailRun, _⟩ := verify_footer_executes hash recovered pc
  have execution := run.then_executes tailRun
  have actual := runWith_of_executes submission hash .verify (message, pk, witness) initial (steps+tailSteps)
    _ loaded execution (by change steps+tailSteps ≤ 2^32; omega)
  refine ⟨cycles+tailSteps, calls, blocks, by omega, hcalls, hblocks, ?_⟩
  rw [actual]
  by_cases yes : RootMatches recovered
  · have valid := accepted.mp yes
    simp only [if_pos yes, if_pos valid, Execution.charge, Nat.add_zero]
    rfl
  · have invalid : ¬Reference.verify hash pk message (SignatureEncoding.decode witness).toReference :=
      fun h => yes (accepted.mpr h)
    simp only [if_neg yes, if_neg invalid, Execution.charge, Nat.add_zero]
    rfl

/-- info: 'SigGolfCandidate.Hypertree.Verifying.run_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms run_refines

end SigGolfCandidate.Hypertree.Verifying
