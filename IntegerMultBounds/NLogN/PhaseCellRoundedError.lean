module

public import IntegerMultBounds.NLogN.PhaseCellRounded

/-! Entrywise accuracy of the actual rational within-cell constructor.
The lower similarity-weight bound is explicit. Converting these estimates to
an operator row bound still requires cross-cell approximation, periodic aliases,
band-tail bounds, and a count of retained entries. -/

@[expose] public section
namespace IntegerMultBounds.NLogN.PhaseCellRounded

noncomputable section

/-- Entrywise perturbation bound reusable by certified exponential samplers. -/
theorem ratio_error {a b g A B G eps r : ℝ}
    (heps : 0 ≤ eps) (hr : 0 < r) (hb : r ≤ b) (hB : r ≤ B)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hb1 : b ≤ 1)
    (hg0 : 0 ≤ g) (hg1 : g ≤ 1) (hG0 : 0 ≤ G) (hG1 : G ≤ 1)
    (hAerr : |A-a| ≤ eps) (hBerr : |B-b| ≤ eps) (hGerr : |G-g| ≤ eps) :
    |A * G / B - a * g / b| ≤ 3 * eps / r ^ 2 := by
  have hb0 : 0 < b := hr.trans_le hb
  have hB0 : 0 < B := hr.trans_le hB
  have hnum : |(A-a)*G*b + a*(G-g)*b + a*g*(b-B)| ≤ 3 * eps := by
    have h1 : |(A-a)*G*b| ≤ eps := by
      calc _ = |A-a| * |G| * |b| := by rw [abs_mul, abs_mul]
           _ ≤ eps * 1 * 1 := by
             gcongr
             · simpa [abs_of_nonneg hG0] using hG1
             · simpa [abs_of_pos hb0] using hb1
           _ = eps := by ring
    have h2 : |a*(G-g)*b| ≤ eps := by
      calc _ = |a| * |G-g| * |b| := by rw [abs_mul, abs_mul]
           _ ≤ 1 * eps * 1 := by
             gcongr
             · simpa [abs_of_nonneg ha0] using ha1
             · simpa [abs_of_pos hb0] using hb1
           _ = eps := by ring
    have h3 : |a*g*(b-B)| ≤ eps := by
      calc _ = |a| * |g| * |b-B| := by rw [abs_mul, abs_mul]
           _ ≤ 1 * 1 * eps := by
             gcongr
             · simpa [abs_of_nonneg ha0] using ha1
             · simpa [abs_of_nonneg hg0] using hg1
             · simpa [abs_sub_comm] using hBerr
           _ = eps := by ring
    calc _ ≤ |(A-a)*G*b + a*(G-g)*b| + |a*g*(b-B)| := abs_add_le _ _
         _ ≤ (|(A-a)*G*b| + |a*(G-g)*b|) + |a*g*(b-B)| :=
           by linarith [abs_add_le ((A-a)*G*b) (a*(G-g)*b)]
         _ ≤ 3 * eps := by linarith
  have heq : A * G / B - a * g / b =
      ((A-a)*G*b + a*(G-g)*b + a*g*(b-B)) / (B*b) := by
    field_simp
    ring
  rw [heq, abs_div, abs_of_pos (mul_pos hB0 hb0)]
  calc _ ≤ (3 * eps) / (B*b) := by gcongr
       _ ≤ (3 * eps) / r ^ 2 := by
         apply div_le_div_of_nonneg_left (by positivity) (sq_pos_of_pos hr)
         nlinarith [mul_le_mul hB hb hr.le hB0.le]

/-- Actual P-grid similarity and Gaussian samples approximate the existing
unaliased coefficient on any retained off-diagonal edge inside one phase cell.
A positive lower bound `r` for the denominator sample costs at most `3 eta/r²`.
The rounding specification itself supplies every sample-error premise. -/
theorem entry_error {P s t w : ℕ} {α : ℝ} {j k : ℤ} {r : ℝ}
    (hst : s < t) (htheta : 0 < (t : ℝ) / s - 1)
    (hphase : PhaseCell.phase s t j = PhaseCell.phase s t k)
    (hjk : j ≠ k) (hband : (k-j).natAbs ≤ w) (hr : 0 < r)
    (hlower : r + error P ≤ PhaseCell.weight s t α k) :
    |(entry P s t w α j k : ℝ) - Real.exp (normExp s t α j (k-j))| ≤
      3 * error P / r ^ 2 := by
  have heps : 0 ≤ error P := by unfold error; positivity
  have hb : r ≤ PhaseCell.weight s t α k := by linarith
  have hB : r ≤ (similarity P s t α k : ℝ) := down_lower P hlower
  have ha0 := (PhaseCell.weight_pos s t α j).le
  have ha1 := PhaseCell.weight_le_one s t α j htheta
  have hb1 := PhaseCell.weight_le_one s t α k htheta
  have hg := gaussian_bounds s t α (k-j)
  have hδ : k-j ≠ 0 := sub_ne_zero.mpr (Ne.symm hjk)
  have hG0 : (0 : ℝ) ≤ kernel P s t w α (k-j) := by
    simpa [kernel, hδ, hband] using
      (show (0 : ℝ) ≤ down P (gaussian s t α (k-j)) by
        exact_mod_cast down_nonneg P hg.1)
  have hG1 : (kernel P s t w α (k-j) : ℝ) ≤ 1 := by
    simpa [kernel, hδ, hband] using (down_bounds P (gaussian s t α (k-j))).1.trans hg.2
  have h := ratio_error heps hr hb hB ha0 ha1 hb1 hg.1 hg.2 hG0 hG1
    (down_error P (PhaseCell.weight s t α j))
    (down_error P (PhaseCell.weight s t α k)) (kernel_error P s t w α (k-j) hband)
  have hexact : Real.exp (normExp s t α j (k-j)) =
      PhaseCell.weight s t α j * gaussian s t α (k-j) / PhaseCell.weight s t α k := by
    simpa only [gaussian, Int.cast_sub] using PhaseCell.coefficient_eq s t hst α j k hphase
  rw [hexact]
  simpa only [entry, ite_eq_right hjk, Rat.cast_div, Rat.cast_mul, similarity] using h

/-- The literal diagonal has zero entry error against the exact unaliased
normalized lattice diagonal, without any rounding premise. -/
theorem entry_diag_error (P s t w : ℕ) (α : ℝ) (j : ℤ) :
    (entry P s t w α j j : ℝ) = Real.exp (normExp s t α j 0) := by
  simp [normExp]

end
end IntegerMultBounds.NLogN.PhaseCellRounded
