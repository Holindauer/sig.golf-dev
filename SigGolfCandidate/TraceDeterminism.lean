import SigGolfCandidate.Hypertree.KeygenTrace

namespace SigGolfCandidate
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64

/-- Equal-length protected traces with the same fixed oracle have the same final state, independently of how their resource indices are presented. -/
theorem Trace.deterministic {hash : Hash} {image : Image} {s t u : MachineState}
    {steps cycles calls blocks otherCycles otherCalls otherBlocks : Nat}
    (first : Trace hash image s steps cycles calls blocks t)
    (second : Trace hash image s steps otherCycles otherCalls otherBlocks u) : t = u := by
  induction first generalizing u otherCycles otherCalls otherBlocks with
  | refl state => cases second; rfl
  | ordinary state next final instruction steps cycles calls blocks hf hs tail ih =>
    cases second with
    | ordinary _ other _ otherInstruction _ _ _ _ hf' hs' tail' =>
      have eq := Option.some.inj (hf.symm.trans hf')
      subst otherInstruction
      have eq := Option.some.inj (hs.symm.trans hs')
      subst other
      exact ih tail'
    | hash _ _ _ _ _ _ hf' _ _ _ =>
      have eq := Option.some.inj (hf.symm.trans hf')
      simp [eq, ordinaryStep] at hs
  | hash state final steps cycles calls blocks hf hs hv tail ih =>
    cases second with
    | ordinary _ other _ otherInstruction _ _ _ _ hf' hs' _ =>
      have eq := Option.some.inj (hf'.symm.trans hf)
      simp [eq, ordinaryStep] at hs'
    | hash _ _ _ _ _ _ _ _ _ tail' => exact ih tail'

/-- info: 'SigGolfCandidate.Trace.deterministic' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Trace.deterministic

end SigGolfCandidate
