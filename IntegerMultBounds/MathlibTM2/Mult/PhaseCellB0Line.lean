module

public import IntegerMultBounds.MathlibTM2.Mult.ConcreteB0
public import IntegerMultBounds.NLogN.PhaseCellConcreteSolve
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Algebra.Order.Ring.Star

/-! The `B̃₀` line map through the concrete phase-cell solve. The real and imaginary parts of
`v/2` are solved by `pcSolve`, scaled by `2^-j` and rounded to the `p`-grid (`bandJtX`). With
`E = 2^(8p+46) p⁷ s² η` the map satisfies the pipeline interface for the normalized
factorization target `B₀ J / 2^j` (`phase_resampB₀_spec`), the same interface as the banded
line (`concrete_resampB₀_specW`). -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.FastB0

open IntegerMultBounds IntegerMultBounds.NLogN
open ContinuousLinearMap Finset

variable {s t : ℕ} [NeZero s] [NeZero t]

theorem phase_resampB₀_spec (hst : s<t) {α d : ℝ} (hα : 0<α)
    (p u j : ℕ) (hp : 2≤p) (hwidth : 8*p≤2^u) (hαu : α^2=(u : ℝ))
    (hθ : 1/(4*(p : ℝ))≤(t : ℝ)/s-1)
    (hgap : (1 : ℝ)/4≤d*((t : ℝ)/s-1)) (hbudget : α^2*d≤p) (hj : 4*(p : ℝ)≤2^j)
    (I : Finset (ZMod s))
    (hI : ∀ k, k∈I ↔ PhaseCellMatrix.Interior s t (PhaseCellBand.width p u) k)
    (rd : ℝ → ℝ) (η : ℝ) (hrd : ∀ x, |rd x-x|≤η) (hrd0 : rd 0=0) (K : ℕ)
    (hK : (1-1/(32*(p : ℝ))/4/2)^(2^K)≤3*(5*η)/(1/(32*(p : ℝ))/4))
    (hprec : 2^(8*p+46)*(p : ℝ)^7*(s : ℝ)^2*η≤1/2)
    (hsmall : 2*(2^(8*p+46)*(p : ℝ)^7*(s : ℝ)^2*η)+2/2^p+(32*(p : ℝ)^2/(2 : ℝ)^(45*p))/2≤1/2)
    (J : (ZMod s → ℂ) →L[ℂ] (ZMod s → ℂ)) (hJ : J ∘L PhaseCellOperator.exact s t α=1)
    (df : ZMod s → ℝ) (hdf : ∀ ℓ, 2^p*‖rhoC p (df ℓ : ℂ)-(dPrime s t α ℓ : ℂ)‖≤2)
    (hdf1 : ∀ ℓ, ‖rhoC p (df ℓ : ℂ)‖≤1) :
    ApproxMap p (resampB₀Of (t := t) p
        (bandJtX (s := s) p j (PhaseCellMatrix.pcSolve s t p u rd K I)) df)
        (((2 : ℂ)^j)⁻¹ • resampB₀ s t α J)
        (6+2^p*((2*(2^(8*p+46)*(p : ℝ)^7*(s : ℝ)^2*η)+2/2^p)+
          (32*(p : ℝ)^2/(2 : ℝ)^(45*p))/2)) ∧
      ∀ w : ZMod t → ℂ, ‖w‖≤1 → ‖resampB₀Of (t := t) p
        (bandJtX (s := s) p j (PhaseCellMatrix.pcSolve s t p u rd K I)) df w‖≤1 := by
  have hη : 0≤η := le_trans (abs_nonneg _) (hrd 0)
  exact concrete_resampB₀_specX hst hα p u j hp hwidth hαu hθ hgap hbudget hj _ _
    (by positivity) (fun x b hx hb i => PhaseCellMatrix.pcSolve_error s t p u hst hα hp hwidth hαu
      hθ hgap hbudget I hI rd η hrd hrd0 K hK hprec x b hx hb i) hsmall J hJ df hdf hdf1

end IntegerMultBounds.MathlibTM2.Mult.FastB0
