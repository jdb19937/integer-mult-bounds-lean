module

public import IntegerMultBounds.MathlibTM2.Fast.MainSem
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Bernstein
public import IntegerMultBounds.MathlibTM2.Fast.ConvBox

/-!
# The semantics of the main pipeline for any box convolution

`MainSem` for the pipeline with an arbitrary box convolution `cb` (`Pipeline.srcMapG`,
`oppMapG`, `pipelineCoeffsG`): the computed transforms take grid values, have norm at most `0.51`
on the `1/2`-ball when `cb` has the guarantee `BoxConvSpec`, and the coefficients of the pipeline
are the rounded numerators of the computed opposite transform.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Fast.Main

open IntegerMultBounds IntegerMultBounds.NLogN IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Layer
open IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Src
open IntegerMultBounds.MathlibTM2.Fast.ResampA IntegerMultBounds.MathlibTM2.Fast.ChirpSt
open IntegerMultBounds.MathlibTM2.Fast.ConvSt
open IntegerMultBounds.MathlibTM2.Mult IntegerMultBounds.MathlibTM2.Mult.Sizes
open IntegerMultBounds.MathlibTM2.Mult.Pipeline

variable {n : ℕ}

theorem mn_sourceApproxG_fixed (hd : 0 < d n) (cb : BoxConvOf n)
    (v : ((i : Fin (d n)) → ZMod (s n i)) → ℂ) (k : (i : Fin (d n)) → ZMod (s n i)) :
    IsFixed (p n) (SourceErr.sourceApprox (s n) (t n) (p n) (gamma n) (lineA n) (lineB n)
      (chirpKernel n) cb v k) := by
  simp only [SourceErr.sourceApprox, Pi.smul_apply, smul_eq_mul]
  have h := (mn_tensorZR_fixed (d n) (t n) (s n) (lineB n) (mn_lineB_fixed n) hd
    (bluesteinApproxD (p n) (chirpKernel n) cb
      (tensorZR (d n) (s n) (t n) (lineA n) v)) k).natMul (2 ^ gamma n)
  push_cast at h
  exact h

theorem mn_srcMapG_fixed (hd : 0 < d n) (cb : BoxConvOf n) (u : ZMod (∏ i, s n i) → ℂ)
    (k : (i : Fin (d n)) → ZMod (s n i)) : IsFixed (p n) (srcMapG n cb u k) :=
  mn_sourceApproxG_fixed hd cb _ k

theorem mn_oppMapG_fixed (hd : 0 < d n) (cb : BoxConvOf n)
    (y : ((i : Fin (d n)) → ZMod (s n i)) → ℂ) (k : ZMod (∏ i, s n i)) :
    IsFixed (p n) (oppMapG n cb y k) :=
  cst_isFixed_conj (mn_sourceApproxG_fixed hd cb _ _)

theorem mn_srcMapG_norm (hbig : Big n) (hsmall : 2 * d n * p n ^ 2 ≤ Sizes.T n * logT n)
    (hEs : 9 * (2 : ℝ) ^ gamma n * Sizes.T n * logT n ≤ 2 ^ p n / 100) (cb : BoxConvOf n)
    (hcb : BoxConvSpec n cb) {u : ZMod (∏ i, s n i) → ℂ} (hu : ‖u‖ ≤ 1 / 2) :
    ‖srcMapG n cb u‖ ≤ 51 / 100 := by
  obtain ⟨hF, hG⟩ := source_approxG hbig hsmall hEs cb hcb
  exact (SourceErr.sourceApprox_norm_le hF hG (by linarith)
    ((norm_comp_le_pi_norm _ u).trans hu)).1

theorem mn_oppMapG_norm (hbig : Big n) (hsmall : 2 * d n * p n ^ 2 ≤ Sizes.T n * logT n)
    (hEs : 9 * (2 : ℝ) ^ gamma n * Sizes.T n * logT n ≤ 2 ^ p n / 100) (cb : BoxConvOf n)
    (hcb : BoxConvSpec n cb) {y : ((i : Fin (d n)) → ZMod (s n i)) → ℂ} (hy : ‖y‖ ≤ 1 / 2) :
    ‖oppMapG n cb y‖ ≤ 51 / 100 := by
  obtain ⟨hF, hG⟩ := source_approxG hbig hsmall hEs cb hcb
  have h := (SourceErr.sourceApprox_norm_le hF hG (by linarith) hy).2
  have e : oppMapG n cb y = SourceErr.oppApprox (s n) (t n) (p n) (gamma n) (lineA n) (lineB n)
      (chirpKernel n) cb y ∘ crtPhi (s n) (s_pairwise n) := rfl
  rw [e]
  exact (norm_comp_le_pi_norm _ _).trans h

section Pipeline

open IntegerMultBounds.ExactRecovery (scaledDigits computedConv computed)

/-- The argument of the opposite transform for the box convolution `cb`. -/
noncomputable abbrev mnYG (n : ℕ) (cb : BoxConvOf n) (x y : ℕ) : ((i : Fin (d n)) → ZMod (s n i)) → ℂ :=
  rdV (p n) (srcMapG n cb (mnU n x) * srcMapG n cb (mnU n y))

/-- **The coefficients of the pipeline** for the box convolution `cb` are the rounded numerators
of the computed opposite transform. -/
theorem mn_pipelineCoeffsG_eq (hd : 0 < d n) (cb : BoxConvOf n) (x y : ℕ) :
    pipelineCoeffsG n cb x y = List.ofFn fun i : Fin (∏ i, s n i) =>
      rndCoeff (b n) (∏ i, s n i) (p n)
        (numer (p n) (oppMapG n cb (mnYG n cb x y) ((i : ℕ) : ZMod (∏ i, s n i)))).re := by
  unfold pipelineCoeffsG
  congr 1
  funext i
  rw [← rndCoeff_complex (b n) (∏ i, s n i) (p n) _ _
    (cst_grid_numer (mn_oppMapG_fixed hd cb (mnYG n cb x y) ((i : ℕ) : ZMod (∏ i, s n i)))).symm]
  rfl

end Pipeline

end IntegerMultBounds.MathlibTM2.Fast.Main
