module

public import IntegerMultBounds.NLogN.PhaseCell

/-!
# Rational rounded within-cell coefficients

Specification of the structured rounding in `downstream-phase-cell-inverse.md`,
"A structured rounded matrix", selected input bcd4ebde8692383539f8a48734e5fbf3a18a32c2.
The P-grid floor below is an exact, noncomputable rounding specification; it is
not an implementation of the corrected exponential evaluator. Shared Gaussian
distance samples, rational similarity ratios, literal unit diagonal and band
zeros are built into the constructor. This is the unaliased within-cell block.
Cross-cell entries and periodic aliases must be supplied separately.
-/

@[expose] public section
namespace IntegerMultBounds.NLogN.PhaseCellRounded

noncomputable section

/-- Exact downward P-grid specification, with a rational result. -/
def down (P : ℕ) (x : ℝ) : ℚ := (⌊(2 : ℝ) ^ P * x⌋ : ℚ) / (2 : ℚ) ^ P

def error (P : ℕ) : ℝ := 1 / (2 : ℝ) ^ P

theorem down_bounds (P : ℕ) (x : ℝ) :
    (down P x : ℝ) ≤ x ∧ x - (down P x : ℝ) < error P := by
  have hpow : (0 : ℝ) < 2 ^ P := by positivity
  have hlo := Int.floor_le ((2 : ℝ) ^ P * x)
  have hhi := Int.lt_floor_add_one ((2 : ℝ) ^ P * x)
  have heq : (down P x : ℝ) = (⌊(2 : ℝ) ^ P * x⌋ : ℝ) / 2 ^ P := by
    simp [down]
  rw [heq]
  constructor
  · apply (div_le_iff₀ hpow).mpr
    nlinarith
  · unfold error
    apply (mul_lt_mul_iff_right₀ hpow).mp
    field_simp
    nlinarith

theorem down_nonneg (P : ℕ) {x : ℝ} (hx : 0 ≤ x) : 0 ≤ down P x := by
  unfold down
  apply div_nonneg _ (by positivity)
  exact_mod_cast Int.floor_nonneg.mpr (mul_nonneg (by positivity) hx)

theorem down_error (P : ℕ) (x : ℝ) : |(down P x : ℝ) - x| ≤ error P := by
  rw [abs_of_nonpos (sub_nonpos.mpr (down_bounds P x).1)]
  linarith [(down_bounds P x).2]

/-- A lower weight bound with one grid unit of slack ensures positivity. -/
theorem down_lower (P : ℕ) {x a : ℝ} (ha : a + error P ≤ x) :
    a ≤ (down P x : ℝ) := by linarith [(down_bounds P x).2]

def similarity (P s t : ℕ) (α : ℝ) (j : ℤ) : ℚ := down P (PhaseCell.weight s t α j)

def gaussian (s t : ℕ) (α : ℝ) (δ : ℤ) : ℝ :=
  Real.exp (-Real.pi * (α ^ 2 * ((t : ℝ) / s) * (δ : ℝ) ^ 2))

/-- One shared rational coefficient for each signed distance. -/
def kernel (P s t w : ℕ) (α : ℝ) (δ : ℤ) : ℚ :=
  if δ = 0 then 1 else if δ.natAbs ≤ w then down P (gaussian s t α δ) else 0

/-- The rational within-cell block. Diagonal entries are literally one. -/
def entry (P s t w : ℕ) (α : ℝ) (j k : ℤ) : ℚ :=
  if j = k then 1 else similarity P s t α j * kernel P s t w α (k-j) /
    similarity P s t α k

@[simp] theorem kernel_zero (P s t w : ℕ) (α : ℝ) : kernel P s t w α 0 = 1 := by
  simp [kernel]

@[simp] theorem entry_diag (P s t w : ℕ) (α : ℝ) (j : ℤ) : entry P s t w α j j = 1 := by
  simp [entry]

theorem kernel_neg (P s t w : ℕ) (α : ℝ) (δ : ℤ) :
    kernel P s t w α (-δ) = kernel P s t w α δ := by
  simp [kernel, gaussian]

/-- Exact diagonal similarity to the shared, symmetric banded Toeplitz kernel. -/
theorem entry_similarity (P s t w : ℕ) (α : ℝ) (j k : ℤ)
    (hk : similarity P s t α k ≠ 0) :
    entry P s t w α j k =
      similarity P s t α j * kernel P s t w α (k-j) / similarity P s t α k := by
  by_cases hjk : j = k
  · subst k
    simp [hk]
  · simp [entry, hjk]

theorem entry_outside (P s t w : ℕ) (α : ℝ) (j k : ℤ) (hband : w < (k-j).natAbs) :
    entry P s t w α j k = 0 := by
  have hjk : j ≠ k := by intro h; subst k; simp at hband
  have hδ : k-j ≠ 0 := sub_ne_zero.mpr (Ne.symm hjk)
  simp [entry, hjk, kernel, hδ, not_le.mpr hband]

/-- Cross-cell coefficients and periodic aliases are explicit inputs, never
silently removed by the within-cell constructor. -/
def assembledEntry (P s t w : ℕ) (α : ℝ)
    (crossCell aliases : ℤ → ℤ → ℚ) (j k : ℤ) : ℚ :=
  (if PhaseCell.phase s t j = PhaseCell.phase s t k then entry P s t w α j k
   else crossCell j k) + aliases j k

theorem gaussian_bounds (s t : ℕ) (α : ℝ) (δ : ℤ) :
    0 ≤ gaussian s t α δ ∧ gaussian s t α δ ≤ 1 := by
  constructor
  · exact (Real.exp_pos _).le
  · apply Real.exp_le_one_iff.mpr
    have : 0 ≤ α ^ 2 * ((t : ℝ) / s) * (δ : ℝ) ^ 2 := by positivity
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr Real.pi_pos.le) this

/-- Explicit rational samples inherit the actual grid rounding error. -/
theorem kernel_error (P s t w : ℕ) (α : ℝ) (δ : ℤ) (hband : δ.natAbs ≤ w) :
    |(kernel P s t w α δ : ℝ) - gaussian s t α δ| ≤ error P := by
  by_cases hδ : δ = 0
  · subst δ
    simp [gaussian, show 0 ≤ error P by unfold error; positivity]
  · simpa [kernel, hδ, hband] using down_error P (gaussian s t α δ)

/-- Positive similarity samples from the exact Gaussian weight lower bound. -/
theorem similarity_pos (P s t : ℕ) (α : ℝ) (j : ℤ)
    (hj : error P < PhaseCell.weight s t α j) : 0 < similarity P s t α j := by
  have h := (down_bounds P (PhaseCell.weight s t α j)).2
  change 0 < down P (PhaseCell.weight s t α j)
  exact_mod_cast (show (0 : ℝ) < down P (PhaseCell.weight s t α j) by linarith)

end
end IntegerMultBounds.NLogN.PhaseCellRounded
