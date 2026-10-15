module

public import IntegerMultBounds.NLogN.ToeplitzDominant
public import IntegerMultBounds.NLogN.PhaseCellConcreteCoefficients
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Algebra.Order.Field.GeomSum

/-! The shared within-cell kernel of the actual rounded Gaussian matrix is a
symmetric Toeplitz block with unit diagonal and off-diagonal row mass at most
`1/8` once `u ≥ 1`. Every interior block therefore has an actual inverse with
corner at least `6/7` and the Gohberg–Semencul factorization, and the cell
entries are its exact diagonal similarity. -/
@[expose] public section
namespace IntegerMultBounds.NLogN.PhaseCellToeplitz

open Finset
open ToeplitzInverse

/-- Natural-distance coefficients of the shared within-cell kernel. -/
noncomputable def coeff (P s t u w : ℕ) (δ : ℕ) : ℝ :=
  (PhaseCellConcreteCoefficients.kernel P s t u w (δ : ℤ) : ℝ)

variable {P s t u w : ℕ}

theorem coeff_zero : coeff P s t u w 0=1 := by
  simp [coeff, PhaseCellConcreteCoefficients.kernel]

theorem exp_neg_three_le : Real.exp (-3)≤1/20 := by
  have h := Real.exp_one_gt_d9
  have h3 : Real.exp 3=Real.exp 1^3 := by
    rw [←Real.exp_nat_mul]
    norm_num
  rw [Real.exp_neg, ←one_div]
  apply one_div_le_one_div_of_le (by norm_num)
  rw [h3]
  calc (20 : ℝ)≤2.7182818283^3 := by norm_num
    _≤_ := pow_le_pow_left₀ (by norm_num) h.le 3

/-- Off-diagonal coefficients decay at least like `20^-δ`. -/
theorem coeff_le (hP : 13≤P) (hs : 0<s) (hst : s≤t) (hu : 1≤u) (δ : ℕ) (hδ : 1≤δ) :
    0≤coeff P s t u w δ ∧ coeff P s t u w δ≤(1/20)^δ := by
  have hδ0 : (δ : ℤ)≠0 := by omega
  unfold coeff PhaseCellConcreteCoefficients.kernel PhaseCellExecutableCoefficients.kernel
  simp only [hδ0, ↓reduceIte]
  split
  · obtain ⟨h0, hle, -⟩ := (PhaseCellConcreteCoefficients.gaussianArg s t u δ).value_spec P hP
    refine ⟨h0, hle.trans ?_⟩
    unfold PhaseCellConcreteCoefficients.gaussianArg
    rw [PhaseCellConcreteCoefficients.encode_target _
      (PhaseCellRationalArgs.gaussianQ_nonneg s t u δ)]
    have hq : (PhaseCellRationalArgs.gaussianQ s t u δ : ℝ)=u*((t : ℝ)/s)*(δ : ℝ)^2 := by
      simp [PhaseCellRationalArgs.gaussianQ]
    have hσ : (1 : ℝ)≤(t : ℝ)/s := by
      rw [le_div_iff₀ (by exact_mod_cast hs)]
      simpa using (show (s : ℝ)≤t by exact_mod_cast hst)
    have huR : (1 : ℝ)≤u := by exact_mod_cast hu
    have hδR : (1 : ℝ)≤δ := by exact_mod_cast hδ
    have hlow : (δ : ℝ)≤u*((t : ℝ)/s)*(δ : ℝ)^2 := by
      have h1 : (1 : ℝ)≤u*((t : ℝ)/s) := by nlinarith
      nlinarith
    calc Real.exp (-Real.pi*(PhaseCellRationalArgs.gaussianQ s t u δ : ℝ))
        ≤Real.exp (-3*δ) := by
          apply Real.exp_le_exp.mpr
          rw [hq]
          nlinarith [Real.pi_gt_three]
      _=Real.exp (-3)^δ := by rw [←Real.exp_nat_mul]; ring_nf
      _≤(1/20)^δ := pow_le_pow_left₀ (Real.exp_pos _).le exp_neg_three_le δ
  · exact ⟨by simp, by simp only [Rat.cast_zero]; positivity⟩

theorem one_sided (hP : 13≤P) (hs : 0<s) (hst : s≤t) (hu : 1≤u) (L : ℕ) :
    ∑ δ∈Ico 1 L, |coeff P s t u w δ|≤1/16 := by
  calc ∑ δ∈Ico 1 L, |coeff P s t u w δ|≤∑ δ∈Ico 1 L, (1/20 : ℝ)^δ := by
        refine sum_le_sum fun δ hδ => ?_
        have h := coeff_le (w := w) hP hs hst hu δ (mem_Ico.mp hδ).1
        rw [abs_of_nonneg h.1]
        exact h.2
    _≤(1/20 : ℝ)^1/(1-1/20) := geom_sum_Ico_le_of_lt_one (by norm_num) (by norm_num)
    _≤1/16 := by norm_num

theorem rowMass (hP : 13≤P) (hs : 0<s) (hst : s≤t) (hu : 1≤u) (L : ℕ) :
    RowMass L (coeff P s t u w) (1/8) := by
  have h := rowMass_of_sum (L := L) (g := coeff P s t u w) _ (one_sided hP hs hst hu L)
  rwa [show (2 : ℝ)*(1/16)=1/8 by norm_num] at h

/-- Every interior Toeplitz block of length `L` has an actual inverse with
corner at least `6/7` and the Gohberg–Semencul factorization. -/
theorem block_inverse (hP : 13≤P) (hs : 0<s) (hst : s≤t) (hu : 1≤u) (L : ℕ) (hL : 0<L) :
    IsInverse L (coeff P s t u w) (natInv L (coeff P s t u w)) ∧
    6/7≤natInv L (coeff P s t u w) 0 0 ∧ ∀ i j, i<L → j<L →
      natInv L (coeff P s t u w) 0 0*natInv L (coeff P s t u w) i j=
        ∑ k∈range (min i j+1),
          (col (natInv L (coeff P s t u w)) (i-min i j+k)*
              col (natInv L (coeff P s t u w)) (j-min i j+k)-
            rev L (natInv L (coeff P s t u w)) (i-min i j+k)*
              rev L (natInv L (coeff P s t u w)) (j-min i j+k)) :=
  ⟨isInverse coeff_zero (rowMass hP hs hst hu L) (by norm_num),
    selected coeff_zero (rowMass hP hs hst hu L) le_rfl hL⟩

theorem kernel_natAbs (δ : ℤ) :
    PhaseCellConcreteCoefficients.kernel P s t u w δ=
      PhaseCellConcreteCoefficients.kernel P s t u w (δ.natAbs : ℤ) := by
  rcases Int.natAbs_eq δ with h | h
  · rw [←h]
  · conv_lhs => rw [h]
    exact PhaseCellConcreteCoefficients.kernel_neg P s t u w _

/-- Within one cell, the actual entries are the diagonal similarity of the
Toeplitz block, indexed from any physical start `lo`. -/
theorem cell_entry (lo : ℤ) (i k : ℕ)
    (hk : PhaseCellConcreteCoefficients.similarity P s t u (lo+k)≠0) :
    (PhaseCellConcreteCoefficients.entry P s t u w (lo+i) (lo+k) : ℝ)=
      (PhaseCellConcreteCoefficients.similarity P s t u (lo+i) : ℝ)*coeff P s t u w (gap i k)/
        (PhaseCellConcreteCoefficients.similarity P s t u (lo+k) : ℝ) := by
  unfold PhaseCellConcreteCoefficients.entry
  rw [PhaseCellExecutableCoefficients.entry_similarity _ _ _ _ _ _ hk]
  have hgap : ((lo+k-(lo+i) : ℤ).natAbs)=gap i k := by
    unfold gap
    omega
  rw [show PhaseCellExecutableCoefficients.kernel P w (PhaseCellConcreteCoefficients.gaussianArg s t u)
      (lo+k-(lo+i))=PhaseCellConcreteCoefficients.kernel P s t u w (lo+k-(lo+i)) from rfl,
    kernel_natAbs, hgap]
  push_cast
  rfl

end IntegerMultBounds.NLogN.PhaseCellToeplitz
