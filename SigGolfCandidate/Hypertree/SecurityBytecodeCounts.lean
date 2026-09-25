import SigGolfCandidate.Hypertree.KeygenQueryAccounting

namespace SigGolfCandidate.Hypertree.SecurityBytecodeCounts
open SigGolf OracleComp Reference SecurityVerifyCost
set_option maxRecDepth 4096

@[simp] theorem calls_secret (hash : Hash) (secretKey : SecretKey) (level tree : Nat) (side : Bool) (chain : Chain) :
    calls hash (SecurityReference.secret secretKey level tree side chain)=1 := by
  simp [SecurityReference.secret]

@[simp] theorem calls_endpoint (hash : Hash) (secretKey : SecretKey) (level tree : Nat) (side : Bool) (chain : Chain) :
    calls hash (SecurityReference.endpoint secretKey level tree side chain)=8 := by
  simp [SecurityReference.endpoint,calls_bind,calls_walk]

theorem calls_leafRoot (hash : Hash) (secretKey : SecretKey) (level tree : Nat) (side : Bool) :
    calls hash (SecurityReference.leafRoot secretKey level tree side)=(if level=0 then 2 else 369) := by
  by_cases zero : level=0
  · simp [SecurityReference.leafRoot,zero,calls_bind]
  · simp [SecurityReference.leafRoot,zero,calls_bind,calls_sequenceFin]

theorem calls_treeRoot (hash : Hash) (secretKey : SecretKey) (level tree : Nat) :
    calls hash (SecurityReference.treeRoot secretKey level tree)=(if level=0 then 5 else 739) := by
  by_cases zero : level=0 <;> simp [SecurityReference.treeRoot,calls_bind,calls_leafRoot,zero]

/-- The monadic reference key generator has exactly the machine's 739 H queries. -/
theorem calls_keygen (hash : Hash) (secretKey : SecretKey) : calls hash (SecurityReference.keygen secretKey)=739 := by
  simp [SecurityReference.keygen,calls_treeRoot]

theorem calls_signChain (hash : Hash) (secretKey : SecretKey) (level tree : Nat) (side : Bool)
    (message : Digest) (chain : Chain) :
    calls hash (SecurityReference.signChain secretKey level tree side message chain)=8 := by
  simp only [SecurityReference.signChain,calls_bind,calls_secret,calls_walk,calls_pure,Nat.add_zero]
  have bound := (digit message chain).isLt
  omega

theorem calls_signLayerWithRoot (hash : Hash) (secretKey : SecretKey) (level tree : Nat) (side : Bool) (message : Digest) :
    calls hash (SecurityReference.signLayerWithRoot secretKey level tree side message)=(if level=0 then 5 else 739) := by
  by_cases zero : level=0 <;> cases side <;>
    simp [SecurityReference.signLayerWithRoot,zero,calls_bind,calls_leafRoot,calls_sequenceFin,calls_signChain]

theorem calls_signUpper (hash : Hash) (secretKey : SecretKey) (count level index : Nat) (message : Digest)
    (positive : 0<level) :
    calls hash (SecurityReference.signUpper secretKey count level index message)=739*count := by
  induction count generalizing level index message with
  | zero => simp [SecurityReference.signUpper]
  | succ count ih =>
    simp only [SecurityReference.signUpper,calls_bind,calls_signLayerWithRoot,
      if_neg (by omega : level ≠ 0),calls_pure,Nat.add_zero]
    rw [ih _ _ _ (by omega)]
    omega

theorem calls_randomizedIndex (hash : Hash) (secretKey : SecretKey) (pk : PublicKey) (message : Message) :
    calls hash (SecurityRandomOracle.randomizedIndex secretKey pk message)=2 := by
  simp [SecurityRandomOracle.randomizedIndex,calls_bind,KeygenQueryAccounting.calls_query]

/-- Shared chain work makes the full reference signer match the bytecode's exact H-call count. -/
theorem calls_signCompact (hash : Hash) (secretKey : SecretKey) (pk : PublicKey) (message : Message) :
    calls hash (SecurityReference.signCompact secretKey pk message)=111596 := by
  simp only [SecurityReference.signCompact,calls_bind,calls_randomizedIndex,calls_signLayerWithRoot,
    calls_signUpper hash secretKey 159 1 _ _ (by decide),calls_pure]
  rfl

/-- info: 'SigGolfCandidate.Hypertree.SecurityBytecodeCounts.calls_signCompact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms calls_signCompact

end SigGolfCandidate.Hypertree.SecurityBytecodeCounts
