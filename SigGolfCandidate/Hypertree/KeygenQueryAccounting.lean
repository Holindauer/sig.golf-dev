import SigGolfCandidate.Hypertree.SecurityVerifyCost

namespace SigGolfCandidate.Hypertree.KeygenQueryAccounting
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 OracleComp SecurityVerifyCost
set_option maxRecDepth 4096

theorem eval_query (hash : Hash) (input : Query) :
    evalWithAnswerFn hash (liftM (HashSpec.query input))=hash input := rfl

theorem calls_query (hash : Hash) (input : Query) :
    calls hash (liftM (HashSpec.query input))=1 := rfl

/-- Recorded interpreter calls count every actual H query, including cached repeats,
failed executions and unfinished observations. -/
theorem execute_calls (hash : Hash) (fuel : Nat) (image : Image) (state : MachineState) :
    calls hash (execute fuel image state) = (evalWithAnswerFn hash (execute fuel image state)).hashCalls := by
  induction fuel generalizing state with
  | zero => simp [execute]
  | succ fuel ih =>
    simp only [execute]
    split
    · simp
    · split
      · simp
      · split
        · simp only [calls_query,calls_bind,calls_pure,evalWithAnswerFn_bind,eval_query,
            evalWithAnswerFn_pure,Execution.charge,ih,Nat.zero_add,Nat.add_comm]
        · simp
    · split
      · simp
      · simp only [calls_map,evalWithAnswerFn_map,Execution.charge,ih,Nat.zero_add]

/-- Generic accounting for the organizer's actual typed loader, interpreter and decoder. -/
theorem run_calls (candidate : Submission) (hash : Hash) (phase : Phase) (input : Input candidate.sizes phase) :
    calls hash (candidate.run phase input) = (candidate.runWith hash phase input).hashCalls := by
  unfold Submission.runWith Submission.run
  split
  · simp
  · simp only [calls_bind,calls_pure,Nat.add_zero,evalWithAnswerFn_bind,evalWithAnswerFn_pure]
    exact execute_calls hash _ _ _

/-- info: 'SigGolfCandidate.Hypertree.KeygenQueryAccounting.run_calls' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms run_calls

end SigGolfCandidate.Hypertree.KeygenQueryAccounting
