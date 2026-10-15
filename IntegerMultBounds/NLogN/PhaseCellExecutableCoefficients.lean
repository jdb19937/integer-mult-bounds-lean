module

public import IntegerMultBounds.NLogN.PhaseCellExpSample
public import IntegerMultBounds.NLogN.PhaseCellRoundedError

/-!
# Structured coefficients from the executable corrected exponential samples

The exponent arguments are explicit nonnegative rational pairs with positive
denominators. An argument mapper can supply these directly without changing
the sampling or matrix construction. Equalities tying their real targets to
phase-cell weights and distance Gaussians remain explicit at the accuracy API.
These are unaliased within-cell coefficients; cross-cell entries and periodic
aliases are separate inputs. No floor identity or tape-cost claim is made.
-/

@[expose] public section
namespace IntegerMultBounds.NLogN.PhaseCellExecutableCoefficients

/-- Natural numerator and positive denominator for a nonnegative exponent. -/
structure ExpArg where
  aa : ℕ
  b : ℕ
  denominator_pos : 0 < b

namespace ExpArg

noncomputable def target (arg : ExpArg) : ℝ := Real.exp (-(Real.pi * arg.aa / arg.b))

def value (P : ℕ) (arg : ExpArg) : ℚ := PhaseCellExpSample.sample P arg.aa arg.b

theorem value_spec (P : ℕ) (arg : ExpArg) (hP : 13 ≤ P) :
    0 ≤ (arg.value P : ℝ) ∧ (arg.value P : ℝ) ≤ arg.target ∧
      |(arg.value P : ℝ) - arg.target| ≤ 4 / (2 : ℝ) ^ P :=
  PhaseCellExpSample.sample_spec P arg.aa arg.b hP arg.denominator_pos

theorem target_bounds (arg : ExpArg) : 0 < arg.target ∧ arg.target ≤ 1 := by
  constructor
  · exact Real.exp_pos _
  · apply Real.exp_le_one_iff.mpr
    exact neg_nonpos.mpr (div_nonneg (mul_nonneg Real.pi_pos.le (Nat.cast_nonneg _))
      (Nat.cast_nonneg _))

theorem value_pos (P : ℕ) (arg : ExpArg) (hP : 13 ≤ P)
    (hlarge : 4 / (2 : ℝ) ^ P < arg.target) : 0 < arg.value P :=
  PhaseCellExpSample.sample_pos P arg.aa arg.b hP arg.denominator_pos hlarge

end ExpArg

/-- Shared distance samples, with exact diagonal and literal band truncation. -/
def kernel (P w : ℕ) (gaussianArg : ℤ → ExpArg) (δ : ℤ) : ℚ :=
  if δ = 0 then 1 else if δ.natAbs ≤ w then (gaussianArg δ).value P else 0

def entry (P w : ℕ) (similarityArg gaussianArg : ℤ → ExpArg) (j k : ℤ) : ℚ :=
  if j = k then 1 else (similarityArg j).value P * kernel P w gaussianArg (k-j) /
    (similarityArg k).value P

@[simp] theorem kernel_zero (P w : ℕ) (gaussianArg : ℤ → ExpArg) :
    kernel P w gaussianArg 0 = 1 := by simp [kernel]

@[simp] theorem entry_diag (P w : ℕ) (similarityArg gaussianArg : ℤ → ExpArg) (j : ℤ) :
    entry P w similarityArg gaussianArg j j = 1 := by simp [entry]

/-- Symmetric arguments produce a symmetric shared Toeplitz kernel. -/
theorem kernel_neg (P w : ℕ) (gaussianArg : ℤ → ExpArg)
    (hsym : ∀ δ, gaussianArg (-δ) = gaussianArg δ) (δ : ℤ) :
    kernel P w gaussianArg (-δ) = kernel P w gaussianArg δ := by
  simp [kernel, hsym]

/-- Exact rational diagonal similarity, including the literal unit diagonal. -/
theorem entry_similarity (P w : ℕ) (similarityArg gaussianArg : ℤ → ExpArg) (j k : ℤ)
    (hk : (similarityArg k).value P ≠ 0) :
    entry P w similarityArg gaussianArg j k =
      (similarityArg j).value P * kernel P w gaussianArg (k-j) / (similarityArg k).value P := by
  by_cases hjk : j = k
  · subst k
    simp [hk]
  · simp [entry, hjk]

theorem entry_outside (P w : ℕ) (similarityArg gaussianArg : ℤ → ExpArg) (j k : ℤ)
    (hband : w < (k-j).natAbs) : entry P w similarityArg gaussianArg j k = 0 := by
  have hjk : j ≠ k := by intro h; subst k; simp at hband
  have hδ : k-j ≠ 0 := sub_ne_zero.mpr (Ne.symm hjk)
  simp [entry, hjk, kernel, hδ, not_le.mpr hband]

/-- Explicit assembly seam: the local constructor does not erase other cells
or periodic image contributions. -/
noncomputable def assembledEntry (P s t w : ℕ) (similarityArg gaussianArg : ℤ → ExpArg)
    (crossCell aliases : ℤ → ℤ → ℚ) (j k : ℤ) : ℚ :=
  (if PhaseCell.phase s t j = PhaseCell.phase s t k then entry P w similarityArg gaussianArg j k
   else crossCell j k) + aliases j k

/-- Corrected executable samples give the existing exact normalized coefficient
an entry error of at most `12 eta/r²`. Only the rational-argument identities and
the selected positive weight margin remain as mathematical premises. -/
theorem entry_error {P s t w : ℕ} {α r : ℝ} {j k : ℤ}
    (similarityArg gaussianArg : ℤ → ExpArg) (hP : 13 ≤ P)
    (hst : s < t) (htheta : 0 < (t : ℝ) / s - 1)
    (hphase : PhaseCell.phase s t j = PhaseCell.phase s t k)
    (hjk : j ≠ k) (hband : (k-j).natAbs ≤ w) (hr : 0 < r)
    (hjarg : (similarityArg j).target = PhaseCell.weight s t α j)
    (hkarg : (similarityArg k).target = PhaseCell.weight s t α k)
    (hgarg : (gaussianArg (k-j)).target = PhaseCellRounded.gaussian s t α (k-j))
    (hlower : r + 4 / (2 : ℝ) ^ P ≤ PhaseCell.weight s t α k) :
    |(entry P w similarityArg gaussianArg j k : ℝ) -
      Real.exp (normExp s t α j (k-j))| ≤ 12 * PhaseCellRounded.error P / r ^ 2 := by
  have heps : (0 : ℝ) ≤ 4 / 2 ^ P := by positivity
  have hjvalue := (similarityArg j).value_spec P hP
  have hkvalue := (similarityArg k).value_spec P hP
  have hgvalue := (gaussianArg (k-j)).value_spec P hP
  rw [hjarg] at hjvalue
  rw [hkarg] at hkvalue
  rw [hgarg] at hgvalue
  have hB : r ≤ ((similarityArg k).value P : ℝ) := by
    have := abs_le.mp hkvalue.2.2
    linarith
  have hb : r ≤ PhaseCell.weight s t α k := by linarith
  have hg := PhaseCellRounded.gaussian_bounds s t α (k-j)
  have hG1 : ((gaussianArg (k-j)).value P : ℝ) ≤ 1 := hgvalue.2.1.trans hg.2
  have h := PhaseCellRounded.ratio_error heps hr hb hB
    (PhaseCell.weight_pos s t α j).le (PhaseCell.weight_le_one s t α j htheta)
    (PhaseCell.weight_le_one s t α k htheta) hg.1 hg.2 hgvalue.1 hG1
    hjvalue.2.2 hkvalue.2.2 hgvalue.2.2
  have hδ : k-j ≠ 0 := sub_ne_zero.mpr (Ne.symm hjk)
  have hexact : Real.exp (normExp s t α j (k-j)) =
      PhaseCell.weight s t α j * PhaseCellRounded.gaussian s t α (k-j) /
        PhaseCell.weight s t α k := by
    simpa only [PhaseCellRounded.gaussian, Int.cast_sub] using
      PhaseCell.coefficient_eq s t hst α j k hphase
  rw [hexact]
  have hconstant : 3 * (4 / (2 : ℝ) ^ P) / r ^ 2 =
      12 * PhaseCellRounded.error P / r ^ 2 := by unfold PhaseCellRounded.error; ring
  rw [hconstant] at h
  simpa [entry, hjk, kernel, hδ, hband] using h

end IntegerMultBounds.NLogN.PhaseCellExecutableCoefficients
