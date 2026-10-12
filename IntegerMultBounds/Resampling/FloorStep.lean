module

public import IntegerMultBounds.Resampling.TabledMaps

/-! Flooring to the `p`-bit grid between axes. The tape `Ã` produces values on
the grid `2^-(p+1)`; before the next axis reads them as `p`-bit words they are
floored to the grid `2^-p` (on words: drop the lowest bit). Flooring moves each
coordinate by less than `2^-p`, so it adds at most `2` to a scaled error
(`approxMap_floorV`), and the floored tabled `Ã` still approximates `A` with
error below `p²` and maps the unit disk to itself (`floorA_tabled`). -/

@[expose] public section

namespace IntegerMultBounds.Resampling.FloorStep

open IntegerMultBounds.NLogN
open IntegerMultBounds.Resampling.WindowSum (termW)

/-- A complex number floored to the grid `2^-p` in both coordinates. -/
noncomputable def floorC (p : ℕ) (z : ℂ) : ℂ :=
  ⟨(⌊2 ^ p * z.re⌋ : ℝ) / 2 ^ p, (⌊2 ^ p * z.im⌋ : ℝ) / 2 ^ p⟩

/-- Coordinatewise `floorC`. -/
noncomputable def floorV {ι : Type*} (p : ℕ) (x : ι → ℂ) : ι → ℂ := fun i => floorC p (x i)

theorem floor_div_sub_le (p : ℕ) (x : ℝ) : |(⌊2 ^ p * x⌋ : ℝ) / 2 ^ p - x| ≤ 1 / 2 ^ p := by
  have hp : (0 : ℝ) < 2 ^ p := by positivity
  have h1 := Int.floor_le (2 ^ p * x)
  have h2 := Int.lt_floor_add_one (2 ^ p * x)
  have e : (⌊2 ^ p * x⌋ : ℝ) / 2 ^ p - x = ((⌊2 ^ p * x⌋ : ℝ) - 2 ^ p * x) / 2 ^ p := by
    field_simp
  rw [e, abs_div, abs_of_pos hp]
  gcongr
  rw [abs_le]; constructor <;> linarith

theorem norm_floorC_sub_le (p : ℕ) (z : ℂ) : ‖floorC p z - z‖ ≤ 2 / 2 ^ p := by
  calc ‖floorC p z - z‖ ≤ |(floorC p z - z).re| + |(floorC p z - z).im| := Complex.norm_le_abs_re_add_abs_im _
    _ ≤ 1 / 2 ^ p + 1 / 2 ^ p := by
      gcongr
      · simpa [floorC] using floor_div_sub_le p z.re
      · simpa [floorC] using floor_div_sub_le p z.im
    _ = 2 / 2 ^ p := by ring

theorem norm_floorV_sub_le {ι : Type*} [Fintype ι] (p : ℕ) (x : ι → ℂ) : ‖floorV p x - x‖ ≤ 2 / 2 ^ p :=
  (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun i => norm_floorC_sub_le p (x i)

/-- Flooring the output adds at most `2` to a scaled error. -/
theorem approxMap_floorV {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] {ι : Type*} [Fintype ι]
    {p : ℕ} {A' : V → ι → ℂ} {A : V →L[ℂ] (ι → ℂ)} {ε : ℝ} (h : ApproxMap p A' A ε) :
    ApproxMap p (fun v => floorV p (A' v)) A (ε + 2) := by
  intro v hv
  have hp : (0 : ℝ) < 2 ^ p := by positivity
  have h1 := h v hv
  have h2 : 2 ^ p * ‖floorV p (A' v) - A' v‖ ≤ 2 := by
    have := norm_floorV_sub_le p (A' v)
    calc 2 ^ p * ‖floorV p (A' v) - A' v‖ ≤ 2 ^ p * (2 / 2 ^ p) := by gcongr
      _ = 2 := by field_simp
  calc 2 ^ p * ‖floorV p (A' v) - A v‖ ≤ 2 ^ p * (‖floorV p (A' v) - A' v‖ + ‖A' v - A v‖) := by
        gcongr; exact norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ = 2 ^ p * ‖floorV p (A' v) - A' v‖ + 2 ^ p * ‖A' v - A v‖ := by ring
    _ ≤ ε + 2 := by linarith

variable {s t : ℕ} [NeZero s] [NeZero t] {α : ℝ}

/-- The floored tabled `Ã`: error below `p²` against `A`, and the unit disk maps to itself. -/
theorem floorA_tabled (hα : 2 ≤ α) {p m : ℕ} (hαp : α ^ 2 ≤ p)
    (hm : (p : ℝ) * α ^ 2 ≤ (m : ℝ) ^ 2) (hm1 : 1 ≤ m) (hmp : m ≤ p) (hp : 13 ≤ p)
    (WA : ZMod t → ℤ → ℤ) (hWA : ∀ k j, |(WA k j : ℝ) - 2 ^ p * resampWeight s t α k j| ≤ 2) :
    ApproxMap p (fun u => floorV p (resampANum s t m (termW p fun k j => (WA k j : ℝ) / 2 ^ p) u))
        (resampA s t α) (errA m + 2) ∧
      errA m + 2 < (p : ℝ) ^ 2 ∧
      ∀ u : ZMod s → ℂ, ‖u‖ ≤ 1 →
        ‖floorV p (resampANum s t m (termW p fun k j => (WA k j : ℝ) / 2 ^ p) u)‖ ≤ 1 := by
  have hA := TabledMaps.approxMap_resampANumW (s := s) (t := t) (by linarith) hαp hm hm1 _
    (fun k j => TabledMaps.tol_of_int p _ _ (hWA k j))
  have hAx : ApproxMap p (fun u => floorV p (resampANum s t m (termW p fun k j => (WA k j : ℝ) / 2 ^ p) u))
      (resampA s t α) (errA m + 2) := approxMap_floorV hA
  have hmr : (m : ℝ) ≤ p := by exact_mod_cast hmp
  have hpr : (13 : ℝ) ≤ p := by exact_mod_cast hp
  have hε : errA m + 2 < (p : ℝ) ^ 2 := by
    have e : errA m = (4 * (2 * (m : ℝ) + 1) + 3) / 2 := rfl
    rw [e]; nlinarith
  have hpow : (4 : ℝ) * (p : ℝ) ^ 2 ≤ 2 ^ p := by exact_mod_cast four_sq_le_pow p hp
  have h4 : 4 * (errA m + 2) ≤ (2 : ℝ) ^ p := by linarith
  have hA34 := opNorm_resampA_le_three_quarters (s := s) (t := t) hα
  exact ⟨hAx, hε, fun u hu => ball_of_approx hA34 hAx h4 u hu⟩

end IntegerMultBounds.Resampling.FloorStep
