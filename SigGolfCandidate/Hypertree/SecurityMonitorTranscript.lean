import SigGolfCandidate.Hypertree.SecurityMonitorView

namespace SigGolfCandidate.Hypertree.SecurityMonitorTranscript
open SigGolf OracleComp OracleSpec Reference SignatureEncoding SecurityExperiment
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

/-- Decode exactly the organizer's successful signing responses. -/
def responses (transcript : Transcript submission.sizes) : SecurityForgery.History :=
  transcript.signed.map (fun entry => (entry.1, decode entry.2))

theorem decode_injective : Function.Injective decode := by
  intro first second same
  apply SecurityPacking.bytes_injective signatureBytes
  calc
    bytes first = (decode first).encode := (decode_encode first).symm
    _ = (decode second).encode := congrArg Compact.encode same
    _ = bytes second := decode_encode second

@[simp] theorem mem_responses (transcript : Transcript submission.sizes) (message : Message) (wire : Bytes signatureBytes) :
    (message, decode wire) ∈ responses transcript ↔ (message,wire) ∈ transcript.signed := by
  rw [responses, List.mem_map]
  constructor
  · rintro ⟨⟨other,encoded⟩, member, same⟩
    have messageSame : other = message := congrArg Prod.fst same
    have wireSame : encoded = wire := decode_injective (congrArg Prod.snd same)
    simpa only [messageSame, wireSame] using member
  · intro member
    exact ⟨(message,wire),member,rfl⟩

theorem fresh_message (transcript : Transcript submission.sizes) (message : Message) (signature : Compact)
    (fresh : transcript.freshMessage message = true) : (message,signature) ∉ responses transcript := by
  intro present
  obtain ⟨entry, member, same⟩ := List.mem_map.mp present
  have messageSame : entry.1 = message := congrArg Prod.fst same
  have all := (List.any_eq_false).mp (show transcript.signed.any (fun entry => entry.1 == message) = false from
    by simpa only [Transcript.freshMessage, Bool.not_eq_true'] using fresh)
  have absent := all entry member
  simp only [messageSame, beq_self_eq_true, not_true_eq_false] at absent

theorem fresh_signature (transcript : Transcript submission.sizes) (message : Message) (wire : Bytes signatureBytes)
    (fresh : transcript.freshSignature message wire = true) : (message,decode wire) ∉ responses transcript := by
  rw [mem_responses]
  intro present
  have contained : transcript.signed.contains (message,wire) = true := List.contains_iff_mem.mpr present
  change (!transcript.signed.contains (message,wire)) = true at fresh
  rw [contained] at fresh
  cases fresh

@[simp] theorem responses_after_signature (transcript : Transcript submission.sizes) (message : Message)
    (wire : Bytes signatureBytes) :
    responses (SecurityExperimentAtomic.afterSign transcript message (some wire)) = (message,decode wire)::responses transcript := rfl

@[simp] theorem responses_after_valid (transcript : Transcript submission.sizes) (message : Message)
    (signature : Compact) (valid : signature.Valid) :
    responses (SecurityExperimentAtomic.afterSign transcript message (serialize signature)) = (message,signature)::responses transcript := by
  rw [serialize_valid signature valid, responses_after_signature, wire_decode]

/-- Both organizer submission forms exclude replay in the decoded response history. -/
def candidate : Forgery submission.sizes → Message × Compact
  | .witness message witness => (message,decode witness)
  | .signature message wire => (message,decode wire)

def fresh (transcript : Transcript submission.sizes) : Forgery submission.sizes → Bool
  | .witness message _ => transcript.freshMessage message
  | .signature message wire => transcript.freshSignature message wire

theorem fresh_candidate (transcript : Transcript submission.sizes) (forgery : Forgery submission.sizes)
    (accepted : fresh transcript forgery = true) : candidate forgery ∉ responses transcript := by
  cases forgery with
  | witness message witness => exact fresh_message transcript message _ accepted
  | signature message wire => exact fresh_signature transcript message wire accepted

/-- This is the actual final checker, with one common continuation for either mode. -/
theorem ofCheck_eq (pk : PublicKey) (transcript : Transcript submission.sizes) (forgery : Forgery submission.sizes) :
    SecurityMonitorView.ofCheck pk transcript forgery =
      SecurityMonitorView.ofHash (SecurityVerify.verifyCompact pk (candidate forgery).1 (candidate forgery).2)
        (fun accepted => .done ⟨accepted && fresh transcript forgery, some (candidate forgery), transcript⟩) := by
  cases forgery <;> rfl

#print axioms fresh_candidate
end SigGolfCandidate.Hypertree.SecurityMonitorTranscript
