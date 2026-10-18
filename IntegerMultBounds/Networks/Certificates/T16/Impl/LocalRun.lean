module

public import IntegerMultBounds.Networks.Certificates.T16.Impl.Invocation

/-! The register action of a wrapped invocation. Combining the invocation's framed run with the
exact rational action of the local word, each output register is the image of its own input,
and for a target under the forward word also of its source, under the operator
`post · F_final · F_initial⁻¹ · pre` of the frames and wrappers along the way. -/
@[expose] public section
namespace IntegerMultBounds.Networks.Certificates.T16.Impl

open BinaryWalsh FramedCircuit Pauli Streams

variable {κ : Type} [DecidableEq κ]
variable {S : Type*} [AddCommGroup S] [Module ℂ S] [Module ℚ S] [IsScalarTower ℚ ℂ S]
variable (ρ : Module.End ℂ (Arrays 73) →* Module.End ℂ S)

/-- The operator carrying register `w'`'s input to register `w`'s output through the frames
`a` (entry of `w'`) and `b` (exit of `w`). -/
noncomputable def throughOp (post pre : List Prim) (a b : ℕ) : Module.End ℂ (Arrays 73) :=
  wordLin post * lift9 (nativeRealization b).scalar.toLinearMap *
    lift9 (nativeRealization a).scalar.symm.toLinearMap * wordLin pre

theorem labelFrame_apply (i : ℕ) (z : S) :
    labelFrame ρ i z = ρ (lift9 (nativeRealization i).scalar.toLinearMap) z := rfl

theorem labelFrame_symm_apply (i : ℕ) (z : S) :
    (labelFrame ρ i).symm z = ρ (lift9 (nativeRealization i).scalar.symm.toLinearMap) z := rfl

theorem throughOp_apply (post pre : List Prim) (a b : ℕ) (z : S) :
    ρ (throughOp post pre a b) z =
      ρ (wordLin post) (labelFrame ρ b ((labelFrame ρ a).symm (ρ (wordLin pre) z))) := by
  simp only [throughOp, map_mul, Module.End.mul_apply, labelFrame_apply, labelFrame_symm_apply]

/-- **Forward invocation.** -/
theorem forward_invocation (reg : ℕ → κ) (hinj : ∀ w < 712, ∀ w' < 712, reg w = reg w' → w = w')
    (pre post : ℕ → List Prim) (y : κ → S) :
    (∀ w < 112, runT ρ (invocation reg pre post forwardWord) y (reg w) =
        ρ (throughOp (post w) (pre w) (Trace.forwardInitial.label w) (Trace.forwardFinal.label w))
          (y (reg w))) ∧
      (∀ w, 112 ≤ w → w < 224 → runT ρ (invocation reg pre post forwardWord) y (reg w) =
        ρ (throughOp (post w) (pre (w - 112)) (Trace.forwardInitial.label (w - 112))
            (Trace.forwardFinal.label w)) (y (reg (w - 112))) +
          ρ (throughOp (post w) (pre w) (Trace.forwardInitial.label w)
            (Trace.forwardFinal.label w)) (y (reg w))) ∧
      (∀ w, 224 ≤ w → w < 704 → runT ρ (invocation reg pre post forwardWord) y (reg w) =
        ρ (throughOp (post w) (pre w) (Trace.forwardInitial.label w) (Trace.forwardFinal.label w))
          (y (reg w))) ∧
      ∀ v, (∀ w < 712, reg w ≠ v) → runT ρ (invocation reg pre post forwardWord) y v = y v := by
  obtain ⟨h1, h2⟩ := invocation_run ρ reg hinj pre post forwardWord forwardWord_wires y
  have hw : ∀ w, runT ρ forwardWord (fun w => ρ (wordLin (pre w)) (y (reg w))) w =
      labelFrame ρ (Trace.forwardFinal.label w) (moduleRun Trace.forwardProgram
        (decode (fun i => labelFrame ρ (Trace.forwardInitial.label i))
          (fun w => ρ (wordLin (pre w)) (y (reg w)))) w) := by
    intro w
    rw [forwardWord_run]
    rfl
  refine ⟨fun w hw0 => ?_, fun w hw0 hw1 => ?_, fun w hw0 hw1 => ?_, h2⟩
  · rw [h1 w (by omega), hw, Trace.forward_action]
    simp only [hw0, ↓reduceIte]
    rw [throughOp_apply]
    rfl
  · rw [h1 w (by omega), hw, Trace.forward_action]
    simp only [show ¬ w < 112 by omega, hw1, ↓reduceIte]
    rw [map_add, map_add, throughOp_apply, throughOp_apply]
    rfl
  · rw [h1 w (by omega), hw, Trace.forward_action]
    simp only [show ¬ w < 112 by omega, show ¬ w < 224 by omega, hw1, ↓reduceIte]
    rw [throughOp_apply]
    rfl

/-- **Backward invocation.** -/
theorem backward_invocation (reg : ℕ → κ) (hinj : ∀ w < 712, ∀ w' < 712, reg w = reg w' → w = w')
    (pre post : ℕ → List Prim) (y : κ → S) :
    (∀ w < 112, runT ρ (invocation reg pre post backwardWord) y (reg w) =
        ρ (throughOp (post w) (pre w) (Trace.backwardInitial.label w)
            (Trace.backwardFinal.label w)) (y (reg w)) -
          ρ (throughOp (post w) (pre (w + 112)) (Trace.backwardInitial.label (w + 112))
            (Trace.backwardFinal.label w)) (y (reg (w + 112)))) ∧
      (∀ w, 112 ≤ w → w < 704 → runT ρ (invocation reg pre post backwardWord) y (reg w) =
        ρ (throughOp (post w) (pre w) (Trace.backwardInitial.label w) (Trace.backwardFinal.label w))
          (y (reg w))) ∧
      ∀ v, (∀ w < 712, reg w ≠ v) → runT ρ (invocation reg pre post backwardWord) y v = y v := by
  obtain ⟨h1, h2⟩ := invocation_run ρ reg hinj pre post backwardWord backwardWord_wires y
  have hw : ∀ w, runT ρ backwardWord (fun w => ρ (wordLin (pre w)) (y (reg w))) w =
      labelFrame ρ (Trace.backwardFinal.label w) (moduleRun Trace.backwardProgram
        (decode (fun i => labelFrame ρ (Trace.backwardInitial.label i))
          (fun w => ρ (wordLin (pre w)) (y (reg w)))) w) := by
    intro w
    rw [backwardWord_run]
    rfl
  refine ⟨fun w hw0 => ?_, fun w hw0 hw1 => ?_, h2⟩
  · rw [h1 w (by omega), hw, Trace.backward_action]
    simp only [hw0, ↓reduceIte]
    rw [map_sub, map_sub, throughOp_apply, throughOp_apply]
    rfl
  · rw [h1 w (by omega), hw, Trace.backward_action]
    simp only [show ¬ w < 112 by omega, hw1, ↓reduceIte]
    rw [throughOp_apply]
    rfl

end IntegerMultBounds.Networks.Certificates.T16.Impl
