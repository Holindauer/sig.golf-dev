import SigGolfCandidate.Hypertree.VerifyLayers

namespace SigGolfCandidate.Hypertree.Verifying
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 Keygen Signing
set_option maxRecDepth 4096

theorem wire_layers_upper (witness : Bytes signatureBytes) (count level : Nat) :
    wireLayers witness count (level+1) = (List.range' level count).map (SignatureEncoding.decodeLayer witness) := by
  induction count generalizing level with
  | zero => simp [wireLayers]
  | succ count ih => simp [wireLayers, wireLayer, List.range'_succ, ih]

/-- The bytes consumed by the machine are exactly the canonical decoded reference signature. -/
theorem wire_layers_decode (witness : Bytes signatureBytes) :
    wireLayers witness 160 0 = (SignatureEncoding.decode witness).toReference.layers := by
  change wireLayer witness 0 :: wireLayers witness 159 (0+1) = _
  rw [wire_layers_upper]
  simp only [SignatureEncoding.decode, SignatureEncoding.Compact.toReference, List.range_eq_range']
  rfl

end SigGolfCandidate.Hypertree.Verifying
