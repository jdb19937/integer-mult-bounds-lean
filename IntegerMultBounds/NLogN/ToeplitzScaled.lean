module

public import IntegerMultBounds.NLogN.ToeplitzRounded
public import IntegerMultBounds.NLogN.ToeplitzDominant

/-! Rounded similarity-scaled interior solve of a dominant symmetric Toeplitz
block. Inputs are scaled by rounded reciprocal weights, passed through the
rounded Gohberg–Semencul convolutions, and rescaled. With weights in
`[δ, 1]` and row mass `ρ ≤ 1/8`, the computed block solve is within an
explicit multiple of the rounding unit `η` of the exact scaled inverse. -/
@[expose] public section
namespace IntegerMultBounds.NLogN.ToeplitzInverse

open scoped BigOperators
open Finset

variable {L : ℕ} {g : ℕ → ℝ} {ρ : ℝ}

theorem col_mass (hg : g 0=1) (hρ : RowMass L g ρ) (hρ1 : ρ<1) (hL : 0<L) :
    ∑ k∈range L, |col (natInv L g) k|≤1/(1-ρ) := by
  have h := isInverse hg hρ hρ1
  have hr := row_abs_sum hg hρ hρ1 0 hL
  simpa only [col, symm h 0] using hr

theorem rev_mass (hg : g 0=1) (hρ : RowMass L g ρ) (hρ1 : ρ<1) (hL : 0<L) :
    ∑ k∈range L, |rev L (natInv L g) k|≤1/(1-ρ) := by
  have h := isInverse hg hρ hρ1
  have hr := row_abs_sum hg hρ hρ1 (L-1) (by omega)
  obtain ⟨L', rfl⟩ : ∃ L', L=L'+1 := ⟨L-1, by omega⟩
  rw [sum_range_succ']
  simp only [rev, abs_zero, add_zero]
  calc ∑ a∈range L', |natInv (L'+1) g a (L'+1-1)|
      ≤∑ a∈range (L'+1), |natInv (L'+1) g (L'+1-1) a| := by
        rw [sum_range_succ]
        have : 0≤|natInv (L'+1) g (L'+1-1) L'| := abs_nonneg _
        have heq : ∑ a∈range L', |natInv (L'+1) g a (L'+1-1)|=
            ∑ a∈range L', |natInv (L'+1) g (L'+1-1) a| :=
          sum_congr rfl fun a _ => by rw [symm h]
        linarith
    _≤_ := hr

/-- Rounded scaling around any inverse application with error `E`. -/
theorem scaled_error (m : ℕ → ℕ → ℝ) (hm : ∀ a<L, ∑ k∈range L, |m a k|≤2)
    (d r c v out y : ℕ → ℝ) (η C E : ℝ) (hη : 0≤η) (hC : 0≤C)
    (hd : ∀ k<L, 0<d k ∧ d k≤1) (hc : ∀ k<L, |c k|≤C)
    (hr : ∀ k<L, |r k-1/d k|≤η) (hv : ∀ k<L, |v k-c k*r k|≤η)
    (hout : ∀ a<L, |out a-∑ k∈range L, m a k*v k|≤E)
    (hy : ∀ a<L, |y a-d a*out a|≤η) (a : ℕ) (ha : a<L) :
    |y a-d a*∑ k∈range L, m a k*(c k/d k)|≤η+E+2*(η+C*η) := by
  obtain ⟨hda, hda1⟩ := hd a ha
  have hvk : ∀ k∈range L, |v k-c k/d k|≤η+C*η := by
    intro k hk
    have hk' := mem_range.mp hk
    have h1 := hv k hk'
    have h2 : |c k*(r k-1/d k)|≤C*η := by
      rw [abs_mul]
      exact mul_le_mul (hc k hk') (hr k hk') (abs_nonneg _) hC
    calc |v k-c k/d k|=|(v k-c k*r k)+c k*(r k-1/d k)| := by ring_nf
      _≤|v k-c k*r k|+|c k*(r k-1/d k)| := abs_add_le _ _
      _≤_ := add_le_add h1 h2
  have hdiff : |∑ k∈range L, m a k*v k-∑ k∈range L, m a k*(c k/d k)|≤2*(η+C*η) := by
    rw [←sum_sub_distrib]
    refine (abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ k∈range L, |m a k*v k-m a k*(c k/d k)|
        ≤∑ k∈range L, |m a k| * (η+C*η) := sum_le_sum fun k hk => by
          rw [←mul_sub, abs_mul]
          exact mul_le_mul_of_nonneg_left (hvk k hk) (abs_nonneg _)
      _=(∑ k∈range L, |m a k|) * (η+C*η) := by rw [sum_mul]
      _≤2*(η+C*η) := mul_le_mul_of_nonneg_right (hm a ha) (by positivity)
  have h1 := hy a ha
  have h2 : |d a*(out a-∑ k∈range L, m a k*v k)|≤E := by
    rw [abs_mul, abs_of_pos hda]
    calc d a*|out a-∑ k∈range L, m a k*v k|≤1*|out a-∑ k∈range L, m a k*v k| :=
          mul_le_mul_of_nonneg_right hda1 (abs_nonneg _)
      _≤E := by rw [one_mul]; exact hout a ha
  have h3 : |d a*(∑ k∈range L, m a k*v k-∑ k∈range L, m a k*(c k/d k))|≤2*(η+C*η) := by
    rw [abs_mul, abs_of_pos hda]
    calc d a*|∑ k∈range L, m a k*v k-∑ k∈range L, m a k*(c k/d k)|
        ≤1*|∑ k∈range L, m a k*v k-∑ k∈range L, m a k*(c k/d k)| :=
          mul_le_mul_of_nonneg_right hda1 (abs_nonneg _)
      _≤_ := by rw [one_mul]; exact hdiff
  calc |y a-d a*∑ k∈range L, m a k*(c k/d k)|
      =|(y a-d a*out a)+d a*(out a-∑ k∈range L, m a k*v k)+
          d a*(∑ k∈range L, m a k*v k-∑ k∈range L, m a k*(c k/d k))| := by ring_nf
    _≤|y a-d a*out a|+|d a*(out a-∑ k∈range L, m a k*v k)|+
          |d a*(∑ k∈range L, m a k*v k-∑ k∈range L, m a k*(c k/d k))| :=
        (abs_add_le _ _).trans (add_le_add_left (abs_add_le _ _) _) |>.trans_eq (by ring)
    _≤η+E+2*(η+C*η) := add_le_add (add_le_add h1 h2) h3

/-- Complete rounded block solve of a dominant Toeplitz block with `ρ ≤ 1/8`:
rounded reciprocal weights, five rounded convolution stages and rounded
rescaling, with input scale `V ≥ 1` bounding the scaled inputs. -/
theorem rounded_block (hg : g 0=1) (hρ : RowMass L g ρ) (hρ8 : ρ≤1/8) (hL : 0<L)
    (xh zh d r c v u₁ u₂ u₃ u₄ out y : ℕ → ℝ) (w η C V : ℝ)
    (hη : 0≤η) (hC : 0≤C) (hV : 1≤V) (hLη : L*η≤1)
    (hd : ∀ k<L, 0<d k ∧ d k≤1) (hc : ∀ k<L, |c k|≤C)
    (hr : ∀ k<L, |r k-1/d k|≤η) (hv : ∀ k<L, |v k-c k*r k|≤η)
    (hvV : ∀ k∈range L, |v k|≤V)
    (hxh : ∀ k∈range L, |xh k-col (natInv L g) k|≤η)
    (hzh : ∀ k∈range L, |zh k-rev L (natInv L g) k|≤η)
    (hw : |w-1/natInv L g 0 0|≤η)
    (hu₁ : ∀ j∈range L, |u₁ j-upper L xh v j|≤η)
    (hu₂ : ∀ i∈range L, |u₂ i-lower xh u₁ i|≤η)
    (hu₃ : ∀ j∈range L, |u₃ j-upper L zh v j|≤η)
    (hu₄ : ∀ i∈range L, |u₄ i-lower zh u₃ i|≤η)
    (hout : ∀ i∈range L, |out i-w*(u₂ i-u₄ i)|≤η)
    (hy : ∀ a<L, |y a-d a*out a|≤η) (a : ℕ) (ha : a<L) :
    |y a-d a*∑ k∈range L, natInv L g a k*(c k/d k)|≤η+64*L*η*V+2*(η+C*η) := by
  have hρ1 : ρ<1 := by linarith
  have hμ : 0<1-ρ := by linarith
  have h87 : 1/(1-ρ)≤2 := by
    rw [div_le_iff₀ hμ]
    linarith
  have hinv := isInverse hg hρ hρ1
  obtain ⟨hx₀, -⟩ := selected hg hρ hρ8 hL
  have hx₀' : natInv L g 0 0≠0 := by linarith
  refine scaled_error (natInv L g) (fun a ha => (row_abs_sum hg hρ hρ1 a ha).trans h87)
    d r c v out y η C _ hη hC hd hc hr hv (fun i hi => ?_) hy a ha
  refine rounded_apply L _ _ xh zh v u₁ u₂ u₃ u₄ out (fun i => ∑ k∈range L, natInv L g i k*v k)
    _ w η V hη hV hLη (by linarith) ((col_mass hg hρ hρ1 hL).trans h87)
    ((rev_mass hg hρ hρ1 hL).trans h87) hxh hzh hw hvV hu₁ hu₂ hu₃ hu₄ hout
    (fun i hi => apply_four hinv hx₀' v i (mem_range.mp hi)) i hi

end IntegerMultBounds.NLogN.ToeplitzInverse
