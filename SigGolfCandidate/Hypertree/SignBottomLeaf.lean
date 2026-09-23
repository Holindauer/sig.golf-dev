import SigGolfCandidate.Hypertree.SignBottomFrame

namespace SigGolfCandidate.Hypertree.Signing
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 Keygen Verifying
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false

/-- The actual complete bottom-leaf body, including its conditional preimage capture and
protected return. The low-memory equation covers both selected and unselected leaves. -/
theorem sign_bottom_leaf_body (hash : Hash) (s : MachineState) (secretKey : SecretKey) (pointer tree : Nat)
    (side : Bool) (pc : s.pc = 0x19dc) (sp : s.getReg .x2 = 0xffffe0)
    (valid : CapturePointerValid pointer) (ptr : s.getMem 0x80448 = BitVec.ofNat 64 pointer)
    (data : LeafData s secretKey 0 tree side 0) (step : s.getMem 0x80438 = 0) :
    ∃ final instructions cycles, Trace hash sign s instructions cycles 2 2 final ∧
      instructions ≤ 195 ∧ cycles ≤ 209 ∧
      final.pc = s.getMem 0xffffe0 &&& ~~~1#64 ∧ final.getReg .x2 = 0xfffff0 ∧
      (∀ i : Fin 2, final.getMem (KeygenSavePublic.wordAddress side i.val) =
        (Reference.leafRoot hash secretKey 0 tree side).extractLsb' (64*i.val) 64) ∧
      (∀ a, a.toNat < 0x80000 → final.getMem a =
        if s.getMem 0x80440 ≠ 0 ∧ s.getMem 0x80428 = s.getMem 0x80420 then
          if a = BitVec.ofNat 64 pointer + 8 then (Reference.secret hash secretKey 0 tree side 0).extractLsb' 64 64 else
          if a = BitVec.ofNat 64 pointer then (Reference.secret hash secretKey 0 tree side 0).extractLsb' 0 64 else s.getMem a
        else s.getMem a) ∧
      (∀ a, OutsideBottomWork side a → (∀ i : Fin 2, a ≠ wordAddress pointer i.val) → final.getMem a = s.getMem a) := by
  obtain ⟨secret, pre, secretPC, secretWords, secretRA, secretSP, secretFrame⟩ := KeygenSecret.compute sign hash 0x19dc
    sign_bottom_secret_code s pc 0 tree side 0 secretKey data.levelEq data.leafEq data.chainEq data.indexEq data.secretKeyEq
  have secretKeep (a : Word) (outside : OutsideBottomWork side a) : secret.getMem a = s.getMem a :=
    secretFrame a outside.1 outside.2.1 outside.2.2.1
  have secretPtr : secret.getMem 0x80448 = BitVec.ofNat 64 pointer := by
    rw [secretKeep _ (by unfold OutsideBottomWork; cases side <;> decide)]; exact ptr
  have safe := capture_access pointer 0 valid
  have capture := captureBottom_block sign 0x1ae0 sign_bottom_capture_code secret secretPC
    (by rw [secretPtr]; simpa using safe.1)
    (by rw [secretPtr]; simpa [BitVec.ofNat_add] using safe.2)
  let captured := captureBottomState secret
  have capturePC : captured.pc = 0x1b38 := by rw [ captureBottom_pc, secretPC]; rfl
  have captureSP : captured.getReg .x2 = 0xffffe0 :=
    (captureBottom_sp secret).trans (secretSP.trans sp)
  have keep (a : Word) (outside : OutsideBottomWork side a) (high : 0x80000 ≤ a.toNat) :
      captured.getMem a = s.getMem a := by
    rw [ captureBottom_high_frame secret pointer valid secretPtr a high, secretKeep a outside]
  have levelEq : captured.getMem 0x80400 = BitVec.ofNat 64 0 := by
    rw [keep _ (by unfold OutsideBottomWork; cases side <;> decide) (by decide)]; exact data.levelEq
  have leafEq : captured.getMem 0x80428 = BitVec.ofNat 64 (Reference.sideNumber side) := by
    rw [keep _ (by unfold OutsideBottomWork; cases side <;> decide) (by decide)]; exact data.leafEq
  have chainEq : captured.getMem 0x80430 = BitVec.ofNat 64 (0 : Reference.Chain).val := by
    rw [keep _ (by unfold OutsideBottomWork; cases side <;> decide) (by decide)]; exact data.chainEq
  have stepEq : captured.getMem 0x80438 = BitVec.ofNat 64 0 := by
    rw [keep _ (by unfold OutsideBottomWork; cases side <;> decide) (by decide)]; exact step
  have indexEq : ∀ i : Fin 3, captured.getMem (wordAddress 0x80408 i.val) = (BitVec.ofNat 192 tree).extractLsb' (64*i.val) 64 := by
    intro i
    rw [keep _ (by fin_cases i <;> unfold OutsideBottomWork <;> cases side <;> decide) (by fin_cases i <;> decide)]
    exact data.indexEq i
  have valueEq : ∀ i : Fin 2, captured.getMem (wordAddress 0x80510 i.val) =
      (Reference.secret hash secretKey 0 tree side 0).extractLsb' (64*i.val) 64 := by
    intro i
    rw [ captureBottom_high_frame secret pointer valid secretPtr _ (by fin_cases i <;> decide)]
    exact secretWords i
  obtain ⟨hashed, core, hashedPC, root, hashedRA, hashedSP, hashedFrame⟩ := SignBottomHash.compute sign hash 0x1b38
    SignBottomHash.sign_code captured capturePC 0 tree 0 side 0 (Reference.secret hash secretKey 0 tree side 0)
    levelEq leafEq chainEq stepEq indexEq valueEq
  have returnTrace := return_block sign 0x1c64 sign_bottom_return_code hashed hashedPC
    (by rw [hashedSP, captureSP]; decide)
  have frame (a : Word) (outside : OutsideBottomWork side a)
      (captureOutside : ∀ i : Fin 2, a ≠ wordAddress pointer i.val) : (returnState hashed).getMem a = s.getMem a := by
    rw [return_mem, hashedFrame a (fun i => outside.1 ⟨i.val, by omega⟩) outside.2.1 outside.2.2.2,
      captureBottom_frame secret pointer secretPtr a captureOutside, secretKeep a outside]
  refine ⟨returnState hashed, 173 + captureBottomSteps secret, 187 + captureBottomSteps secret,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, frame⟩
  · convert ((pre.trans capture.trace).trans core).trans returnTrace.trace using 1 <;> omega
  · have := captureBottom_steps_le secret; omega
  · have := captureBottom_steps_le secret; omega
  · rw [return_pc, hashedSP, captureSP]
    have stackEq : hashed.getMem 0xffffe0 = s.getMem 0xffffe0 := by
      have h := frame 0xffffe0 (by unfold OutsideBottomWork; cases side <;> decide)
      rw [return_mem] at h
      apply h
      intro i eq
      rcases valid with ⟨lower, upper, aligned⟩
      have ib := i.isLt
      have h := congrArg BitVec.toNat eq
      simp [wordAddress] at h
      omega
    rw [stackEq]
  · rw [return_sp, hashedSP, captureSP]; rfl
  · intro i
    rw [return_mem]
    exact root i
  · intro a low
    have outside := low_outside_bottom side a low
    rw [return_mem, hashedFrame a (fun i => outside.1 ⟨i.val, by omega⟩) outside.2.1 outside.2.2.2, captureBottom_mem,
      secretKeep _ (by unfold OutsideBottomWork; cases side <;> decide),
      secretKeep _ (by unfold OutsideBottomWork; cases side <;> decide),
      secretKeep _ (by unfold OutsideBottomWork; cases side <;> decide), secretPtr,
      show secret.getMem 0x80518 = (Reference.secret hash secretKey 0 tree side 0).extractLsb' 64 64 from secretWords 1,
      show secret.getMem 0x80510 = (Reference.secret hash secretKey 0 tree side 0).extractLsb' 0 64 from secretWords 0,
      secretKeep a outside]

end SigGolfCandidate.Hypertree.Signing
