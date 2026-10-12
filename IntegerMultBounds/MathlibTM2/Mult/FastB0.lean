module

public import IntegerMultBounds.Resampling.TabledMaps

/-!
# `B̃₀` with few Neumann steps and a window of width `√p / α`

Paper §7, proof of `lem:no-sort-resampling`: the numerical map `B̃₀ = D̃' J̃' C`. The tabled
map `Resampling.TabledMaps.resampB₀NumW p m` runs `p` Horner–Neumann steps. Since
`‖N - 1‖ ≤ 2^{-α² θ}`, `K` steps with `α² θ K ≥ p` reach the same error; and the factor
`exp (-π α² |h| (|h| - 1))` in the `h`-th off-diagonal term makes the window
`0 < |h| ≤ m` with `p ≤ 4 α² m²` sufficient.

## Maps

* `resampJNumK p K m ef`: halve and round the input, then `K` rounded Horner steps with the
  off-diagonal sum `offDiagNum m (offTermW p ef)` over `0 < |h| ≤ m` with supplied weights.
* `resampB₀NumK p K m ef df = diagW p df ∘ resampJNumK p K m ef ∘ rowSelect s t`.
  `resampB₀NumW p m` is `resampB₀NumK p p m`.

## Results

* `opNorm_offDiagCLM_le_rpow`: `‖E‖ ≤ 2^{-α² θ}` when `α² θ ≥ 1`.
  `two_pow_mul_opNorm_pow_le`: `2^p ‖E‖^K ≤ 1` once `p ≤ α² θ K`.
* `inverse_approx_unit_steps`: Lemma 4.12 on the unit disk with `K` steps and scaled error
  `2 (εE + ρ) + 1`, given `2^p ‖E‖^K ≤ 1`.
* `exponent_ge_full`, `offDiag_term_le_gauss_alpha`: for `h ≠ 0` the `h`-th term of `E u`
  (with `‖u‖ ≤ 1`) is at most `exp (-2π (|h| - 1/2)²) · exp (-π α² |h| (|h| - 1))`.
* `offDiag_trunc_err_alpha`: truncating `E` to `0 < |h| ≤ m` loses at most
  `3 exp (-π α² m²)`, hence at most `3 / 2^p` when `p ≤ 4 α² m²`
  (`offDiag_trunc_err_alpha_pow`).
* `offDiagW_err_alpha`: the tabled `Ẽ` has scaled error `8 m + 3` on the unit disk.
* `resampJNumK_err`, `resampB₀NumK_ball`, `approxMap_resampB₀NumK`: the error and the
  unit-disk bound for any scaled error `εE ≤ 2^p / 25` of `Ẽ`.
  `approxMap_resampB₀NumK_window`: scaled error `16 m + 21` for `B̃₀`.
* `resampB₀NumK_spec`: with `p ≥ 13` and `3 m ≤ p`, the error is at most `p²` and the unit
  disk maps into itself: the hypotheses `hB'` and `hB'1` of
  `SourceErr.sourceErr_of_components`. `resampB₀NumK_tabled`: the same for integer weight
  tables within two units.
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2.Mult.FastB0

open IntegerMultBounds IntegerMultBounds.NLogN
open IntegerMultBounds.Resampling.OffDiagSum (offTermW)
open ContinuousLinearMap Real

section Generic

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

/-- `‖(-E)^K‖ ≤ ‖E‖^K` for every `K`, including `K = 0`. -/
theorem norm_neg_pow_le_pow (E : V →L[ℂ] V) (K : ℕ) : ‖(-E) ^ K‖ ≤ ‖E‖ ^ K := by
  rcases Nat.eq_zero_or_pos K with rfl | hK
  · simpa using norm_one_clm_le (V := V)
  · calc ‖(-E) ^ K‖ ≤ ‖-E‖ ^ K := norm_pow_le' _ hK
      _ = ‖E‖ ^ K := by rw [norm_neg]

/-- The truncated Neumann series is within `‖E‖^K ‖J‖` of a right inverse `J` of `1 + E`. -/
theorem norm_neumannPartial_sub_inv_le {E J : V →L[ℂ] V} (hJ : (1 + E) ∘L J = 1) (K : ℕ) :
    ‖neumannPartial E K - J‖ ≤ ‖E‖ ^ K * ‖J‖ := by
  have key : neumannPartial E K - J = -((-E) ^ K * J) := by
    have h1 : neumannPartial E K * (1 + E) * J = neumannPartial E K := by
      rw [mul_assoc, mul_def (1 + E) J, hJ, mul_one]
    calc neumannPartial E K - J = (neumannPartial E K * (1 + E) - 1) * J := by
          rw [sub_mul, one_mul, h1]
      _ = -((-E) ^ K * J) := by rw [neumannPartial_mul]; noncomm_ring
  rw [key, norm_neg]
  calc ‖(-E) ^ K * J‖ ≤ ‖(-E) ^ K‖ * ‖J‖ := norm_mul_le _ _
    _ ≤ ‖E‖ ^ K * ‖J‖ := by gcongr; exact norm_neg_pow_le_pow E K

variable {E : V →L[ℂ] V} {E' rd : V → V} {v : V} {p : ℕ} {εE ρ : ℝ}

/-- Lemma 4.12 on the unit disk with `K` Horner steps: if `2^p ‖E‖^K ≤ 1`, then `K`
rounded steps from an input of norm at most one half approximate `J v` with scaled error
at most `2 (εE + ρ) + 1`. -/
theorem inverse_approx_unit_steps {J : V →L[ℂ] V} {K : ℕ} (hE : ‖E‖ ≤ 23 / 50)
    (hEK : 2 ^ p * ‖E‖ ^ K ≤ 1) (hJ : (1 + E) ∘L J = 1)
    (hE' : ∀ y, ‖y‖ ≤ 1 → 2 ^ p * ‖E' y - E y‖ ≤ εE) (hroom : 25 * εE ≤ 2 ^ p)
    (hrd : ∀ x, 2 ^ p * ‖rd x - x‖ ≤ ρ) (hrdball : ∀ x, ‖rd x‖ ≤ ‖x‖)
    (hv : ‖v‖ ≤ 1 / 2) :
    2 ^ p * ‖hornerNeumannR rd E' v K - J v‖ ≤ 2 * (εE + ρ) + 1 := by
  have hE2 : ‖E‖ ≤ 1 / 2 := hE.trans (by norm_num)
  have h1 := (hornerNeumannR_err_unit hE hE' hroom hrd hrdball hv K).2
  have hJ2 := norm_inv_le_two hE2 hJ
  have hp : (0 : ℝ) < 2 ^ p := by positivity
  have h2 : 2 ^ p * ‖hornerNeumann E v K - J v‖ ≤ 1 := by
    rw [hornerNeumann_eq_partial, ← sub_apply]
    have hb : ‖(neumannPartial E (K + 1) - J) v‖ ≤ ‖E‖ ^ K * (1 / 2) * 2 * (1 / 2) := by
      calc ‖(neumannPartial E (K + 1) - J) v‖
          ≤ ‖neumannPartial E (K + 1) - J‖ * ‖v‖ := le_opNorm _ _
        _ ≤ (‖E‖ ^ (K + 1) * ‖J‖) * ‖v‖ := by
            gcongr; exact norm_neumannPartial_sub_inv_le hJ (K + 1)
        _ = ‖E‖ ^ K * ‖E‖ * ‖J‖ * ‖v‖ := by rw [pow_succ]
        _ ≤ ‖E‖ ^ K * (1 / 2) * 2 * (1 / 2) := by gcongr
    have hEK0 : 0 ≤ 2 ^ p * ‖E‖ ^ K := by positivity
    calc 2 ^ p * ‖(neumannPartial E (K + 1) - J) v‖
        ≤ 2 ^ p * (‖E‖ ^ K * (1 / 2) * 2 * (1 / 2)) := by gcongr
      _ = (2 ^ p * ‖E‖ ^ K) / 2 := by ring
      _ ≤ 1 := by linarith
  calc 2 ^ p * ‖hornerNeumannR rd E' v K - J v‖
      ≤ 2 ^ p * (‖hornerNeumannR rd E' v K - hornerNeumann E v K‖ +
          ‖hornerNeumann E v K - J v‖) := by
        gcongr
        exact norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ = 2 ^ p * ‖hornerNeumannR rd E' v K - hornerNeumann E v K‖ +
          2 ^ p * ‖hornerNeumann E v K - J v‖ := by ring
    _ ≤ 2 * (εE + ρ) + 1 := add_le_add h1 h2

end Generic

section Norm

variable {s t : ℕ} [NeZero s] [NeZero t] {α : ℝ}

/-- Lemma 4.6 as an operator-norm bound: `‖E‖ ≤ 2.01 e^{-π α² θ / 2}`. -/
theorem opNorm_offDiagCLM_le_exp (hst : s < t) (hα : 0 < α)
    (hθ : 1 ≤ α ^ 2 * ((t : ℝ) / s - 1)) :
    ‖offDiagCLM s t α‖ ≤ 2.01 * Real.exp (-π * α ^ 2 * ((t : ℝ) / s - 1) / 2) := by
  refine opNorm_le_of_unit_norm (by positivity) fun u hu => ?_
  rw [pi_norm_le_iff_of_nonneg (by positivity), offDiagCLM_apply s t hst hα]
  intro ℓ
  refine norm_offDiag_le s t hst hα hθ u (fun j => ?_) ℓ
  rw [← hu]; exact norm_le_pi_norm u j

/-- `2.01 e^{-π y / 2} ≤ 2^{-y}` for `y ≥ 1`. -/
theorem exp_bound_le_rpow {y : ℝ} (hy : 1 ≤ y) :
    2.01 * Real.exp (-π * y / 2) ≤ (2 : ℝ) ^ (-y) := by
  rw [Real.rpow_def_of_pos (by norm_num)]
  have hl := Real.log_two_lt_d9
  have hπ := Real.pi_gt_d2
  have hpi := exp_half_pi_ge
  have h1 : π / 2 - Real.log 2 ≤ π * y / 2 - y * Real.log 2 := by nlinarith
  have h2 : Real.exp (π / 2 - Real.log 2) = Real.exp (π / 2) / 2 := by
    rw [Real.exp_sub, Real.exp_log (by norm_num)]
  have h3 : Real.exp (π / 2 - Real.log 2) ≤ Real.exp (π * y / 2 - y * Real.log 2) :=
    Real.exp_le_exp.mpr h1
  have e : Real.exp (Real.log 2 * -y) =
      Real.exp (-π * y / 2) * Real.exp (π * y / 2 - y * Real.log 2) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [e]
  have h0 := Real.exp_pos (-π * y / 2)
  have h4 : 2.01 ≤ Real.exp (π * y / 2 - y * Real.log 2) := by linarith
  nlinarith

/-- The paper's estimate `‖N - 1‖ ≤ 2^{-α² θ}`. -/
theorem opNorm_offDiagCLM_le_rpow (hst : s < t) (hα : 0 < α)
    (hθ : 1 ≤ α ^ 2 * ((t : ℝ) / s - 1)) :
    ‖offDiagCLM s t α‖ ≤ (2 : ℝ) ^ (-(α ^ 2 * ((t : ℝ) / s - 1))) := by
  refine (opNorm_offDiagCLM_le_exp hst hα hθ).trans ?_
  have := exp_bound_le_rpow hθ
  convert this using 3
  ring

/-- `K` Neumann steps suffice once `α² θ K ≥ p`: `2^p ‖E‖^K ≤ 1`. -/
theorem two_pow_mul_opNorm_pow_le (hst : s < t) (hα : 0 < α)
    (hθ : 1 ≤ α ^ 2 * ((t : ℝ) / s - 1)) {p K : ℕ}
    (hK : (p : ℝ) ≤ α ^ 2 * ((t : ℝ) / s - 1) * K) :
    2 ^ p * ‖offDiagCLM s t α‖ ^ K ≤ 1 := by
  set y := α ^ 2 * ((t : ℝ) / s - 1) with hy
  have h1 : ‖offDiagCLM s t α‖ ^ K ≤ ((2 : ℝ) ^ (-y)) ^ K :=
    pow_le_pow_left₀ (norm_nonneg _) (opNorm_offDiagCLM_le_rpow hst hα hθ) K
  rw [← Real.rpow_mul_natCast (by norm_num)] at h1
  have h2 : (2 : ℝ) ^ (-y * K) ≤ (2 : ℝ) ^ (-(p : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  have h3 : (2 : ℝ) ^ (p : ℕ) * (2 : ℝ) ^ (-(p : ℝ)) = 1 := by
    rw [Real.rpow_neg (by norm_num), Real.rpow_natCast, mul_inv_cancel₀ (by positivity)]
  have hp : (0 : ℝ) ≤ 2 ^ p := by positivity
  calc 2 ^ p * ‖offDiagCLM s t α‖ ^ K ≤ 2 ^ p * (2 : ℝ) ^ (-(p : ℝ)) := by
        gcongr; exact h1.trans h2
    _ = 1 := h3

end Norm

section Tail

variable (s t : ℕ) [NeZero s] [NeZero t]

omit [NeZero t] in
/-- The exponent inequality of Lemma 4.6 with the `α`-dependent remainder kept: for
`h ≠ 0`, `(th/s + b)² - b'² ≥ 2θ (|h| - 1/2)² + ((|h| - 1/2)² - 1/4)`. -/
theorem exponent_ge_full (hst : s < t) (b b' : ℝ) (hb : |b| ≤ 1 / 2) (hb' : |b'| ≤ 1 / 2)
    (h : ℤ) (hh : h ≠ 0) :
    2 * ((t : ℝ) / s - 1) * (|(h : ℝ)| - 1 / 2) ^ 2 + ((|(h : ℝ)| - 1 / 2) ^ 2 - 1 / 4) ≤
      ((t : ℝ) * h / s + b) ^ 2 - b' ^ 2 := by
  have hs : (0 : ℝ) < s := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne s)
  have hx : (1 : ℝ) ≤ (t : ℝ) / s := by
    rw [le_div_iff₀ hs, one_mul]
    exact_mod_cast hst.le
  have hm : (1 : ℝ) ≤ |(h : ℝ)| := by
    have := Int.one_le_abs hh
    exact_mod_cast this
  set x : ℝ := (t : ℝ) / s with hxdef
  set m : ℝ := |(h : ℝ)| with hmdef
  have hxh : (t : ℝ) * h / s = x * h := by
    rw [hxdef]
    ring
  rw [hxh]
  have habs : x * m - 1 / 2 ≤ |x * h + b| := by
    have h1 : |x * h + b| ≥ |x * h| - |b| := by
      have := abs_sub_abs_le_abs_sub (x * h) (-b)
      rw [abs_neg, sub_neg_eq_add] at this
      linarith
    have h2 : |x * (h : ℝ)| = x * m := by
      rw [abs_mul, abs_of_pos (by linarith : 0 < x)]
    linarith
  have hpos : 0 ≤ x * m - 1 / 2 := by nlinarith
  have hsq : (x * m - 1 / 2) ^ 2 ≤ (x * h + b) ^ 2 := by
    rw [← sq_abs (x * h + b)]
    gcongr
  have hb'2 : b' ^ 2 ≤ 1 / 4 := by
    have h2 : |b'| ^ 2 ≤ (1 / 2) ^ 2 := by gcongr
    rw [sq_abs] at h2
    linarith
  have hy : 1 / 2 ≤ m - 1 / 2 := by linarith
  have hθ : 0 ≤ x - 1 := by linarith
  have hid : (x * m - 1 / 2) ^ 2 - 1 / 4 - 2 * (x - 1) * (m - 1 / 2) ^ 2 -
      ((m - 1 / 2) ^ 2 - 1 / 4) =
      (x - 1) ^ 2 * (m - 1 / 2) ^ 2 + (x - 1) * (m - 1 / 2) +
        (x - 1) ^ 2 * (m - 1 / 2) + (x - 1) ^ 2 / 4 := by ring
  have h2 : 0 ≤ (x - 1) ^ 2 * (m - 1 / 2) ^ 2 := by positivity
  have h3 : 0 ≤ (x - 1) * (m - 1 / 2) := by positivity
  have h4 : 0 ≤ (x - 1) ^ 2 * (m - 1 / 2) := by positivity
  have h5 : 0 ≤ (x - 1) ^ 2 / 4 := by positivity
  nlinarith

omit [NeZero t] in
/-- Under `α² θ ≥ 1`, the `h`-th off-diagonal term is at most
`exp (-2π (|h| - 1/2)²) · exp (-π α² |h| (|h| - 1))`. -/
theorem offDiag_term_le_gauss_alpha (hst : s < t) {α : ℝ} (hα : 0 < α)
    (hθ : 1 ≤ α ^ 2 * ((t : ℝ) / s - 1)) (u : ZMod s → ℂ) (hu : ∀ j, ‖u j‖ ≤ 1)
    (ℓ : ZMod s) (h : ℤ) (hh : h ≠ 0) :
    ‖(Real.exp (normExp s t α ℓ.val h) : ℂ) * u (ℓ + h)‖ ≤
      Real.exp (-2 * π * ((h.natAbs : ℝ) - 1 / 2) ^ 2) *
        Real.exp (-π * α ^ 2 * (((h.natAbs : ℝ) - 1 / 2) ^ 2 - 1 / 4)) := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  calc Real.exp (normExp s t α ℓ.val h) * ‖u (ℓ + h)‖
      ≤ Real.exp (normExp s t α ℓ.val h) * 1 := by
        gcongr
        exact hu _
    _ = Real.exp (normExp s t α ℓ.val h) := mul_one _
    _ ≤ _ := ?_
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hexp := exponent_ge_full s t hst (beta s t ℓ.val) (beta s t (ℓ.val + h))
    (abs_beta_le s t _) (abs_beta_le s t _) h hh
  unfold normExp
  rw [Nat.cast_natAbs, Int.cast_abs]
  set θ : ℝ := (t : ℝ) / s - 1
  set y : ℝ := |(h : ℝ)| - 1 / 2
  have hπ : 0 < π := Real.pi_pos
  have hy : 0 ≤ y ^ 2 := sq_nonneg y
  have hπα : 0 ≤ π * α ^ 2 := by positivity
  have h1 := mul_le_mul_of_nonneg_left hexp hπα
  have h2 : 2 * π * y ^ 2 ≤ 2 * π * (α ^ 2 * θ) * y ^ 2 := by
    have : 0 ≤ 2 * π * y ^ 2 := by positivity
    nlinarith
  nlinarith

/-- Truncation error of `E` to the window `0 < |h| ≤ m`, Gaussian in `α m`:
at most `3 exp (-π α² m²)`. -/
theorem offDiag_trunc_err_alpha (hst : s < t) {α : ℝ} (hα : 0 < α)
    (hθ : 1 ≤ α ^ 2 * ((t : ℝ) / s - 1)) (u : ZMod s → ℂ) (hu : ∀ j, ‖u j‖ ≤ 1)
    (m : ℕ) (ℓ : ZMod s) :
    ‖offDiag s t α u ℓ - offDiagTrunc s t α m u ℓ‖ ≤
      3 * Real.exp (-π * α ^ 2 * (m : ℝ) ^ 2) := by
  set C : ℝ := Real.exp (-π * α ^ 2 * (m : ℝ) ^ 2) with hC
  set A : ℝ := Real.exp (-2 * π * ((m : ℝ) + 1 / 2) ^ 2) with hA
  set q : ℝ := Real.exp (-2 * π) with hq
  have hq0 : 0 ≤ q := (Real.exp_pos _).le
  have hqpos : 0 < q := Real.exp_pos _
  have hq3 : q ≤ 1 / 3 := exp_neg_two_pi_le
  have hq1 : q < 1 := by linarith
  have hA0 : 0 ≤ A := (Real.exp_pos _).le
  have hC0 : 0 ≤ C := (Real.exp_pos _).le
  have hA1 : A ≤ 1 := by
    rw [hA, Real.exp_le_one_iff]
    have := Real.pi_pos
    have : 0 ≤ ((m : ℝ) + 1 / 2) ^ 2 := sq_nonneg _
    nlinarith
  set g : ℤ → ℂ := fun h => (Real.exp (normExp s t α ℓ.val h) : ℂ) * u (ℓ + h) with hg
  set f : ℤ → ℂ := fun h => if h = 0 then 0 else g h with hf
  have hfsum : Summable f := by
    have := (summable_normN_term s t hα u ℓ).update 0 0
    convert this using 1
    funext h
    rw [Function.update_apply]
  set S := offDiagWindow m with hS
  set f₁ : ℤ → ℂ := fun h => if h ∈ S then f h else 0 with hf₁
  set f₂ : ℤ → ℂ := fun h => if h ∈ S then 0 else f h with hf₂
  have hf₁sum : Summable f₁ :=
    summable_of_ne_finset_zero (s := S) (fun h hh => by simp [hf₁, hh])
  have hsplit : f = fun h => f₁ h + f₂ h := by
    funext h
    show f h = (if h ∈ S then f h else 0) + (if h ∈ S then 0 else f h)
    split_ifs <;> simp
  have hf₂sum : Summable f₂ := by
    have : f₂ = fun h => f h - f₁ h := by
      funext h
      show (if h ∈ S then 0 else f h) = f h - (if h ∈ S then f h else 0)
      split_ifs <;> simp
    rw [this]
    exact hfsum.sub hf₁sum
  have htsum : offDiag s t α u ℓ = ∑ h ∈ S, f h + ∑' h, f₂ h := by
    have h1 : offDiag s t α u ℓ = ∑' h, f h := rfl
    have h2 : ∑' h, f h = ∑' h, (f₁ h + f₂ h) := congrArg tsum hsplit
    rw [h1, h2, hf₁sum.tsum_add hf₂sum, tsum_eq_sum (s := S) (fun h hh => by simp [hf₁, hh])]
    congr 1
    exact Finset.sum_congr rfl (fun h hh => by simp [hf₁, hh])
  have htrunc : offDiagTrunc s t α m u ℓ = ∑ h ∈ S, f h := by
    unfold offDiagTrunc
    refine Finset.sum_congr rfl (fun h hh => ?_)
    have : h ≠ 0 := (mem_offDiagWindow.mp hh).1
    simp [hf, hg, this]
  rw [htsum, htrunc, add_sub_cancel_left]
  set A' : ℝ := C * A / q ^ m with hA'
  have hcomp := hasSum_tail_comparison A' q hq0 hq1 m
  have hbound : ‖∑' h, f₂ h‖ ≤ A' * q ^ m * (1 - q)⁻¹ + A' * q ^ m * (1 - q)⁻¹ := by
    refine tsum_of_norm_bounded hcomp (fun h => ?_)
    by_cases hh : h ∈ S
    · have e : f₂ h = 0 := by
        show (if h ∈ S then 0 else f h) = 0
        simp [hh]
      rw [e, norm_zero]
      split_ifs
      · positivity
      · exact le_rfl
    · have hh' := mt mem_offDiagWindow.mpr hh
      by_cases h0 : h = 0
      · subst h0
        have e : f₂ 0 = 0 := by
          show (if (0 : ℤ) ∈ S then 0 else (if (0 : ℤ) = 0 then (0 : ℂ) else g 0)) = 0
          simp
        rw [e, norm_zero]
        simp
      · have hm : m < h.natAbs := by
          by_contra hcon
          exact hh' ⟨h0, not_lt.mp hcon⟩
        have e : f₂ h = g h := by
          show (if h ∈ S then 0 else (if h = 0 then (0 : ℂ) else g h)) = g h
          simp [hh, h0]
        rw [e]
        simp only [hm, ↓reduceIte]
        refine (offDiag_term_le_gauss_alpha s t hst hα hθ u hu ℓ h h0).trans ?_
        set n : ℕ := h.natAbs - m - 1 with hn
        have hcast : (h.natAbs : ℝ) - 1 / 2 = (m : ℝ) + 1 / 2 + n := by
          rw [hn, Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
          push_cast
          ring
        rw [hcast]
        have hpow : q ^ (h.natAbs - 1) = q ^ m * q ^ n := by
          rw [← pow_add]
          congr 1
          omega
        have hCle : Real.exp (-π * α ^ 2 * (((m : ℝ) + 1 / 2 + n) ^ 2 - 1 / 4)) ≤ C := by
          rw [hC]
          apply Real.exp_le_exp.mpr
          have hn0 : (0 : ℝ) ≤ n := by positivity
          have hm0 : (0 : ℝ) ≤ m := by positivity
          have hk : (m : ℝ) ^ 2 ≤ ((m : ℝ) + 1 / 2 + n) ^ 2 - 1 / 4 := by nlinarith
          have hπα : 0 ≤ π * α ^ 2 := by positivity
          nlinarith [mul_le_mul_of_nonneg_left hk hπα]
        calc Real.exp (-2 * π * ((m : ℝ) + 1 / 2 + n) ^ 2) *
              Real.exp (-π * α ^ 2 * (((m : ℝ) + 1 / 2 + n) ^ 2 - 1 / 4))
            ≤ (A * q ^ n) * C := by
              apply mul_le_mul (gauss_half_le_geom m n) hCle (Real.exp_pos _).le
              positivity
          _ = A' * q ^ (h.natAbs - 1) := by
              rw [hpow, hA']
              field_simp
  calc ‖∑' h, f₂ h‖ ≤ A' * q ^ m * (1 - q)⁻¹ + A' * q ^ m * (1 - q)⁻¹ := hbound
    _ = 2 * (C * A) / (1 - q) := by
        rw [hA']
        field_simp
        ring
    _ ≤ 3 * (C * A) := by
        rw [div_le_iff₀ (by linarith)]
        have : 0 ≤ C * A := by positivity
        nlinarith
    _ ≤ 3 * C := by
        have : C * A ≤ C * 1 := by gcongr
        linarith

/-- With `α² θ ≥ 1` and `p ≤ 4 α² m²`, the truncation error is below `3 / 2^p`:
a window of order `√p / α`. -/
theorem offDiag_trunc_err_alpha_pow (hst : s < t) {α : ℝ} (hα : 0 < α)
    (hθ : 1 ≤ α ^ 2 * ((t : ℝ) / s - 1)) (u : ZMod s → ℂ) (hu : ∀ j, ‖u j‖ ≤ 1)
    {p m : ℕ} (hm : (p : ℝ) ≤ 4 * α ^ 2 * (m : ℝ) ^ 2) (ℓ : ZMod s) :
    ‖offDiag s t α u ℓ - offDiagTrunc s t α m u ℓ‖ ≤ 3 / 2 ^ p := by
  refine (offDiag_trunc_err_alpha s t hst hα hθ u hu m ℓ).trans ?_
  have hπ := Real.pi_gt_d2
  have hlog := Real.log_two_lt_d9
  have hp0 : (0 : ℝ) ≤ p := by positivity
  have hexp : Real.exp (-π * α ^ 2 * (m : ℝ) ^ 2) ≤ 1 / 2 ^ p := by
    have h1 : Real.exp (-π * α ^ 2 * (m : ℝ) ^ 2) ≤ Real.exp (-(p : ℝ) * Real.log 2) := by
      apply Real.exp_le_exp.mpr
      -- `p log 2 ≤ 0.6932 p < (π / 4) p ≤ π α² m²`
      have h2 : (p : ℝ) * Real.log 2 ≤ (p : ℝ) * 0.6931471808 :=
        mul_le_mul_of_nonneg_left hlog.le hp0
      have h3 : π * (p : ℝ) ≤ π * (4 * α ^ 2 * (m : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_left hm Real.pi_pos.le
      nlinarith
    have h2 : Real.exp (-(p : ℝ) * Real.log 2) = 1 / 2 ^ p := by
      rw [neg_mul, Real.exp_neg, Real.exp_nat_mul, Real.exp_log (by norm_num), inv_eq_one_div]
    rw [h2] at h1
    exact h1
  calc 3 * Real.exp (-π * α ^ 2 * (m : ℝ) ^ 2) ≤ 3 * (1 / 2 ^ p) := by gcongr
    _ = 3 / 2 ^ p := by ring

/-- Lemma 4.11 with the window `p ≤ 4 α² m²`: evaluating the `2m` retained terms with
per-term scaled error `c` approximates `E` with scaled error `2 m c + 3`. -/
theorem offDiag_approx_err_alpha (hst : s < t) {α : ℝ} (hα : 0 < α)
    (hθ : 1 ≤ α ^ 2 * ((t : ℝ) / s - 1)) (u : ZMod s → ℂ) (hu : ∀ j, ‖u j‖ ≤ 1)
    {p m : ℕ} (hm : (p : ℝ) ≤ 4 * α ^ 2 * (m : ℝ) ^ 2) (ℓ : ZMod s) {c : ℝ} (z' : ℤ → ℂ)
    (hz : ∀ h ∈ offDiagWindow m,
      (2 : ℝ) ^ p * ‖z' h - (Real.exp (normExp s t α ℓ.val h) : ℂ) * u (ℓ + h)‖ ≤ c) :
    (2 : ℝ) ^ p * ‖∑ h ∈ offDiagWindow m, z' h - offDiag s t α u ℓ‖ ≤ c * (2 * m) + 3 := by
  have hsum := offDiag_sum_err hz
  rw [card_offDiagWindow] at hsum
  have htr := offDiag_trunc_err_alpha_pow s t hst hα hθ u hu hm ℓ
  have hp : (0 : ℝ) < 2 ^ p := by positivity
  have htr' : (2 : ℝ) ^ p * ‖offDiagTrunc s t α m u ℓ - offDiag s t α u ℓ‖ ≤ 3 := by
    rw [norm_sub_rev]
    calc (2 : ℝ) ^ p * ‖offDiag s t α u ℓ - offDiagTrunc s t α m u ℓ‖
        ≤ 2 ^ p * (3 / 2 ^ p) := by gcongr
      _ = 3 := by field_simp
  calc (2 : ℝ) ^ p * ‖∑ h ∈ offDiagWindow m, z' h - offDiag s t α u ℓ‖
      = 2 ^ p * ‖(∑ h ∈ offDiagWindow m, z' h - offDiagTrunc s t α m u ℓ) +
          (offDiagTrunc s t α m u ℓ - offDiag s t α u ℓ)‖ := by
        congr 2
        abel
    _ ≤ 2 ^ p * (‖∑ h ∈ offDiagWindow m, z' h - offDiagTrunc s t α m u ℓ‖ +
          ‖offDiagTrunc s t α m u ℓ - offDiag s t α u ℓ‖) := by
        gcongr
        exact norm_add_le _ _
    _ = 2 ^ p * ‖∑ h ∈ offDiagWindow m, z' h - offDiagTrunc s t α m u ℓ‖ +
          2 ^ p * ‖offDiagTrunc s t α m u ℓ - offDiag s t α u ℓ‖ := by ring
    _ ≤ c * (2 * m) + 3 := by
        have e : (∑ h ∈ offDiagWindow m, (Real.exp (normExp s t α ℓ.val h) : ℂ) * u (ℓ + h)) =
            offDiagTrunc s t α m u ℓ := rfl
        rw [e] at hsum
        push_cast at hsum
        linarith

end Tail

section Maps

open IntegerMultBounds.Resampling.TabledMaps (diagW diagW_err)

variable {s t : ℕ} [NeZero s] [NeZero t] {α : ℝ}

omit [NeZero t] in
/-- An off-diagonal term with a weight within two grid units has scaled error at most
four on the unit disk. -/
theorem offTermW_err_unit (p : ℕ) (ef : ZMod s → ℤ → ℝ) {u : ZMod s → ℂ} (hu : ‖u‖ ≤ 1)
    (ℓ : ZMod s) (h : ℤ)
    (hef : 2 ^ p * ‖rhoC p (ef ℓ h : ℂ) - (Real.exp (normExp s t α ℓ.val h) : ℂ)‖ ≤ 2) :
    2 ^ p * ‖offTermW p ef u ℓ h - offDiagTerm s t α u ℓ h‖ ≤ 4 := by
  have hw := rhoC_mul_err p hef ((norm_le_pi_norm u (ℓ + h)).trans hu)
  unfold offTermW offDiagTerm
  linarith

/-- Lemma 4.11 packaged on the unit disk with the window `p ≤ 4 α² m²`. -/
theorem approxMap_offDiagNum_alpha (hst : s < t) (hα : 0 < α)
    (hθ : 1 ≤ α ^ 2 * ((t : ℝ) / s - 1)) {p m : ℕ} (hm : (p : ℝ) ≤ 4 * α ^ 2 * (m : ℝ) ^ 2)
    {c : ℝ} {z' : (ZMod s → ℂ) → ZMod s → ℤ → ℂ}
    (hz : ∀ u : ZMod s → ℂ, ‖u‖ ≤ 1 → ∀ ℓ, ∀ h ∈ offDiagWindow m,
      2 ^ p * ‖z' u ℓ h - offDiagTerm s t α u ℓ h‖ ≤ c) :
    ApproxMap p (offDiagNum m z') (offDiagCLM s t α) (c * (2 * m) + 3) := by
  refine approxMap_of_pointwise fun u hu ℓ => ?_
  rw [offDiagCLM_apply s t hst hα]
  exact offDiag_approx_err_alpha s t hst hα hθ u (fun j => (norm_le_pi_norm u j).trans hu) hm ℓ
    (z' u ℓ) (hz u hu ℓ)

/-- The off-diagonal map with supplied weights and the window `p ≤ 4 α² m²`: scaled
error `8 m + 3` on the unit disk. -/
theorem offDiagW_err_alpha (hst : s < t) (hα : 0 < α) (hθ : 1 ≤ α ^ 2 * ((t : ℝ) / s - 1))
    {p m : ℕ} (hm : (p : ℝ) ≤ 4 * α ^ 2 * (m : ℝ) ^ 2) (ef : ZMod s → ℤ → ℝ)
    (hef : ∀ ℓ h, 2 ^ p * ‖rhoC p (ef ℓ h : ℂ) - (Real.exp (normExp s t α ℓ.val h) : ℂ)‖ ≤ 2)
    (y : ZMod s → ℂ) (hy : ‖y‖ ≤ 1) :
    2 ^ p * ‖offDiagNum m (offTermW p ef) y - offDiagCLM s t α y‖ ≤ 8 * m + 3 := by
  have h := approxMap_offDiagNum_alpha hst hα hθ hm
    (fun _ hu ℓ h _ => offTermW_err_unit (t := t) p ef hu ℓ h (hef ℓ h)) y hy
  have e : (4 : ℝ) * (2 * m) + 3 = 8 * m + 3 := by ring
  rwa [e] at h

/-- `J̃'` with supplied off-diagonal weights, `K` Horner steps and window `m`. -/
noncomputable def resampJNumK (p K m : ℕ) (ef : ZMod s → ℤ → ℝ) (v : ZMod s → ℂ) : ZMod s → ℂ :=
  hornerNeumannR (rdV p) (offDiagNum m (offTermW p ef)) (rdV p ((1 / 2 : ℂ) • v)) K

/-- `J̃'` with `K` steps stays in the unit disk and approximates `J (v/2)` with scaled
error `2 (εE + 2) + 5` once `α² θ K ≥ p`. -/
theorem resampJNumK_err (hst : s < t) (hα : 0 < α)
    (hθ : 1 ≤ α ^ 2 * ((t : ℝ) / s - 1)) {p K m : ℕ}
    (hK : (p : ℝ) ≤ α ^ 2 * ((t : ℝ) / s - 1) * K) (ef : ZMod s → ℤ → ℝ) {εE : ℝ}
    (hE' : ∀ y : ZMod s → ℂ, ‖y‖ ≤ 1 →
      2 ^ p * ‖offDiagNum m (offTermW p ef) y - offDiagCLM s t α y‖ ≤ εE)
    (hroom : 25 * εE ≤ 2 ^ p)
    {J : (ZMod s → ℂ) →L[ℂ] (ZMod s → ℂ)} (hJ : (1 + offDiagCLM s t α) ∘L J = 1)
    {v : ZMod s → ℂ} (hv : ‖v‖ ≤ 1) :
    ‖resampJNumK p K m ef v‖ ≤ 1 ∧
      2 ^ p * ‖resampJNumK p K m ef v - J ((1 / 2 : ℂ) • v)‖ ≤ 2 * (εE + 2) + 5 := by
  have hE := opNorm_offDiagCLM_le_unit hst hα hθ
  have hEK := two_pow_mul_opNorm_pow_le hst hα hθ hK
  set v0 := rdV p ((1 / 2 : ℂ) • v) with hv0
  have hhalf : ‖(1 / 2 : ℂ) • v‖ ≤ 1 / 2 := by
    rw [norm_smul, norm_div, norm_one, RCLike.norm_two]; linarith
  have hv0b : ‖v0‖ ≤ 1 / 2 := (norm_rdV_le p _).trans hhalf
  refine ⟨(hornerNeumannR_err_unit hE hE' hroom (norm_rdV_sub_le p) (norm_rdV_le p) hv0b K).1, ?_⟩
  have h1 := inverse_approx_unit_steps hE hEK hJ hE' hroom (norm_rdV_sub_le p) (norm_rdV_le p) hv0b
  have hJ2 := norm_inv_le_two (hE.trans (by norm_num)) hJ
  have h2 : 2 ^ p * ‖J v0 - J ((1 / 2 : ℂ) • v)‖ ≤ 4 := by
    rw [← map_sub]
    calc 2 ^ p * ‖J (v0 - (1 / 2 : ℂ) • v)‖ ≤ 2 ^ p * (‖J‖ * ‖v0 - (1 / 2 : ℂ) • v‖) := by
          gcongr; exact le_opNorm _ _
      _ = ‖J‖ * (2 ^ p * ‖v0 - (1 / 2 : ℂ) • v‖) := by ring
      _ ≤ 2 * 2 := by
          gcongr
          exact norm_rdV_sub_le p _
      _ = 4 := by norm_num
  unfold resampJNumK
  rw [← hv0]
  calc 2 ^ p * ‖hornerNeumannR (rdV p) (offDiagNum m (offTermW p ef)) v0 K - J ((1 / 2 : ℂ) • v)‖
      ≤ 2 ^ p * (‖hornerNeumannR (rdV p) (offDiagNum m (offTermW p ef)) v0 K - J v0‖ +
          ‖J v0 - J ((1 / 2 : ℂ) • v)‖) := by
        gcongr
        exact norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ = 2 ^ p * ‖hornerNeumannR (rdV p) (offDiagNum m (offTermW p ef)) v0 K - J v0‖ +
          2 ^ p * ‖J v0 - J ((1 / 2 : ℂ) • v)‖ := by ring
    _ ≤ (2 * (εE + 2) + 1) + 4 := add_le_add h1 h2
    _ = 2 * (εE + 2) + 5 := by ring

/-- `B̃₀ = D̃' J̃' C` with supplied weights, `K` Horner steps and window `m`. -/
noncomputable def resampB₀NumK (p K m : ℕ) (ef : ZMod s → ℤ → ℝ) (df : ZMod s → ℝ)
    (w : ZMod t → ℂ) : ZMod s → ℂ :=
  diagW p df (resampJNumK p K m ef (rowSelect s t w))

omit [NeZero t] in
/-- The tabled `B̃₀` of `TabledMaps` is the case `K = p`. -/
theorem resampB₀NumW_eq (p m : ℕ) (ef : ZMod s → ℤ → ℝ) (df : ZMod s → ℝ) :
    Resampling.TabledMaps.resampB₀NumW (t := t) p m ef df = resampB₀NumK p p m ef df := rfl

theorem resampB₀NumK_ball (hst : s < t) (hα : 0 < α)
    (hθ : 1 ≤ α ^ 2 * ((t : ℝ) / s - 1)) {p K m : ℕ}
    (hK : (p : ℝ) ≤ α ^ 2 * ((t : ℝ) / s - 1) * K) (ef : ZMod s → ℤ → ℝ) (df : ZMod s → ℝ)
    {εE : ℝ}
    (hE' : ∀ y : ZMod s → ℂ, ‖y‖ ≤ 1 →
      2 ^ p * ‖offDiagNum m (offTermW p ef) y - offDiagCLM s t α y‖ ≤ εE)
    (hroom : 25 * εE ≤ 2 ^ p) (hdf1 : ∀ ℓ, ‖rhoC p (df ℓ : ℂ)‖ ≤ 1)
    {J : (ZMod s → ℂ) →L[ℂ] (ZMod s → ℂ)}
    (hJ : (1 + offDiagCLM s t α) ∘L J = 1) (w : ZMod t → ℂ) (hw : ‖w‖ ≤ 1) :
    ‖resampB₀NumK p K m ef df w‖ ≤ 1 := by
  have hv1 : ‖rowSelect s t w‖ ≤ 1 := (norm_rowSelect_le _).trans hw
  have hy := (resampJNumK_err hst hα hθ hK ef hE' hroom hJ hv1).1
  rw [pi_norm_le_iff_of_nonneg zero_le_one]
  intro ℓ
  unfold resampB₀NumK diagW
  refine (norm_rhoC_le p _).trans ?_
  rw [norm_mul]
  calc ‖rhoC p (df ℓ : ℂ)‖ * ‖resampJNumK p K m ef (rowSelect s t w) ℓ‖ ≤ 1 * 1 :=
        mul_le_mul (hdf1 ℓ) ((norm_le_pi_norm _ ℓ).trans hy) (norm_nonneg _) zero_le_one
    _ = 1 := one_mul 1

theorem approxMap_resampB₀NumK (hst : s < t) (hα : 0 < α)
    (hθ : 1 ≤ α ^ 2 * ((t : ℝ) / s - 1)) {p K m : ℕ}
    (hK : (p : ℝ) ≤ α ^ 2 * ((t : ℝ) / s - 1) * K) (ef : ZMod s → ℤ → ℝ) (df : ZMod s → ℝ)
    {εE : ℝ}
    (hE' : ∀ y : ZMod s → ℂ, ‖y‖ ≤ 1 →
      2 ^ p * ‖offDiagNum m (offTermW p ef) y - offDiagCLM s t α y‖ ≤ εE)
    (hroom : 25 * εE ≤ 2 ^ p)
    (hdf : ∀ ℓ, 2 ^ p * ‖rhoC p (df ℓ : ℂ) - (dPrime s t α ℓ : ℂ)‖ ≤ 2)
    {J : (ZMod s → ℂ) →L[ℂ] (ZMod s → ℂ)} (hJ : (1 + offDiagCLM s t α) ∘L J = 1) :
    ApproxMap p (resampB₀NumK p K m ef df) (resampB₀ s t α J) (6 + (2 * (εE + 2) + 5)) := by
  refine approxMap_of_pointwise fun w hw ℓ => ?_
  set v := rowSelect s t w with hv
  have hv1 : ‖v‖ ≤ 1 := (norm_rowSelect_le _).trans hw
  set y := resampJNumK p K m ef v with hy
  obtain ⟨hy1, hyJ⟩ := resampJNumK_err hst hα hθ hK ef hE' hroom hJ hv1
  have hB : resampB₀ s t α J w ℓ = (dPrime s t α ℓ : ℂ) * J ((1 / 2 : ℂ) • v) ℓ := by
    rw [resampB₀_apply, map_smul, Pi.smul_apply, smul_eq_mul]; ring
  have hBN : resampB₀NumK p K m ef df w ℓ = diagW p df y ℓ := rfl
  rw [hB, hBN]
  have hD := diagW_err (t := t) (α := α) p df (hy1.trans one_le_two) ℓ (hdf ℓ)
  have hJℓ : 2 ^ p * ‖y ℓ - J ((1 / 2 : ℂ) • v) ℓ‖ ≤ 2 * (εE + 2) + 5 := by
    have hk : ‖y ℓ - J ((1 / 2 : ℂ) • v) ℓ‖ ≤ ‖y - J ((1 / 2 : ℂ) • v)‖ :=
      norm_le_pi_norm (y - J ((1 / 2 : ℂ) • v)) ℓ
    have hp : (0 : ℝ) ≤ 2 ^ p := by positivity
    calc 2 ^ p * ‖y ℓ - J ((1 / 2 : ℂ) • v) ℓ‖ ≤ 2 ^ p * ‖y - J ((1 / 2 : ℂ) • v)‖ := by gcongr
      _ ≤ _ := hyJ
  have hd1 : ‖(dPrime s t α ℓ : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (dPrime_nonneg ℓ)]
    exact dPrime_le_one ℓ
  have hsplit : diagW p df y ℓ - (dPrime s t α ℓ : ℂ) * J ((1 / 2 : ℂ) • v) ℓ =
      (diagW p df y ℓ - (dPrime s t α ℓ : ℂ) * y ℓ) +
        (dPrime s t α ℓ : ℂ) * (y ℓ - J ((1 / 2 : ℂ) • v) ℓ) := by ring
  rw [hsplit]
  calc 2 ^ p * ‖(diagW p df y ℓ - (dPrime s t α ℓ : ℂ) * y ℓ) +
        (dPrime s t α ℓ : ℂ) * (y ℓ - J ((1 / 2 : ℂ) • v) ℓ)‖
      ≤ 2 ^ p * (‖diagW p df y ℓ - (dPrime s t α ℓ : ℂ) * y ℓ‖ +
          ‖(dPrime s t α ℓ : ℂ)‖ * ‖y ℓ - J ((1 / 2 : ℂ) • v) ℓ‖) := by
        gcongr
        rw [← norm_mul]
        exact norm_add_le _ _
    _ = 2 ^ p * ‖diagW p df y ℓ - (dPrime s t α ℓ : ℂ) * y ℓ‖ +
          ‖(dPrime s t α ℓ : ℂ)‖ * (2 ^ p * ‖y ℓ - J ((1 / 2 : ℂ) • v) ℓ‖) := by ring
    _ ≤ 6 + 1 * (2 * (εE + 2) + 5) := by gcongr
    _ = 6 + (2 * (εE + 2) + 5) := by ring

/-- `B̃₀` with `K` steps and window `m` under `α² θ K ≥ p` and `p ≤ 4 α² m²`: scaled
error `16 m + 21`. -/
theorem approxMap_resampB₀NumK_window (hst : s < t) (hα : 0 < α)
    (hθ : 1 ≤ α ^ 2 * ((t : ℝ) / s - 1)) {p K m : ℕ}
    (hK : (p : ℝ) ≤ α ^ 2 * ((t : ℝ) / s - 1) * K) (hm : (p : ℝ) ≤ 4 * α ^ 2 * (m : ℝ) ^ 2)
    (hroom : 25 * (8 * (m : ℝ) + 3) ≤ 2 ^ p) (ef : ZMod s → ℤ → ℝ) (df : ZMod s → ℝ)
    (hef : ∀ ℓ h, 2 ^ p * ‖rhoC p (ef ℓ h : ℂ) - (Real.exp (normExp s t α ℓ.val h) : ℂ)‖ ≤ 2)
    (hdf : ∀ ℓ, 2 ^ p * ‖rhoC p (df ℓ : ℂ) - (dPrime s t α ℓ : ℂ)‖ ≤ 2)
    {J : (ZMod s → ℂ) →L[ℂ] (ZMod s → ℂ)} (hJ : (1 + offDiagCLM s t α) ∘L J = 1) :
    ApproxMap p (resampB₀NumK p K m ef df) (resampB₀ s t α J) (16 * m + 21) := by
  have h := approxMap_resampB₀NumK hst hα hθ hK ef df (offDiagW_err_alpha hst hα hθ hm ef hef)
    hroom hdf hJ
  have e : (6 : ℝ) + (2 * ((8 * m + 3) + 2) + 5) = 16 * m + 21 := by ring
  rwa [e] at h

/-- The room condition and the error budget for `3 m ≤ p`, `p ≥ 13`. -/
theorem room_and_budget {p m : ℕ} (hp : 13 ≤ p) (hmp : 3 * m ≤ p) :
    25 * (8 * (m : ℝ) + 3) ≤ 2 ^ p ∧ 16 * (m : ℝ) + 21 ≤ (p : ℝ) ^ 2 := by
  have h := pow_room p hp
  have h' : ((300 * p + 150 : ℕ) : ℝ) ≤ ((2 ^ p : ℕ) : ℝ) := by exact_mod_cast h
  push_cast at h'
  have hm : 3 * (m : ℝ) ≤ p := by exact_mod_cast hmp
  have hp' : (13 : ℝ) ≤ p := by exact_mod_cast hp
  refine ⟨by nlinarith, by nlinarith⟩

/-- The hypotheses `hB'` and `hB'1` of `SourceErr.sourceErr_of_components` for `B̃₀` with
`K` Horner steps and window `m`, under `α² θ K ≥ p`, `p ≤ 4 α² m²`, `3 m ≤ p` and `p ≥ 13`. -/
theorem resampB₀NumK_spec (hst : s < t) (hα : 0 < α)
    (hθ : 1 ≤ α ^ 2 * ((t : ℝ) / s - 1)) {p K m : ℕ}
    (hK : (p : ℝ) ≤ α ^ 2 * ((t : ℝ) / s - 1) * K) (hm : (p : ℝ) ≤ 4 * α ^ 2 * (m : ℝ) ^ 2)
    (hp : 13 ≤ p) (hmp : 3 * m ≤ p) (ef : ZMod s → ℤ → ℝ) (df : ZMod s → ℝ)
    (hef : ∀ ℓ h, 2 ^ p * ‖rhoC p (ef ℓ h : ℂ) - (Real.exp (normExp s t α ℓ.val h) : ℂ)‖ ≤ 2)
    (hdf : ∀ ℓ, 2 ^ p * ‖rhoC p (df ℓ : ℂ) - (dPrime s t α ℓ : ℂ)‖ ≤ 2)
    (hdf1 : ∀ ℓ, ‖rhoC p (df ℓ : ℂ)‖ ≤ 1)
    {J : (ZMod s → ℂ) →L[ℂ] (ZMod s → ℂ)} (hJ : (1 + offDiagCLM s t α) ∘L J = 1) :
    ApproxMap p (resampB₀NumK p K m ef df) (resampB₀ s t α J) ((p : ℝ) ^ 2) ∧
      ∀ w : ZMod t → ℂ, ‖w‖ ≤ 1 → ‖resampB₀NumK p K m ef df w‖ ≤ 1 := by
  obtain ⟨hroom, hbud⟩ := room_and_budget hp hmp
  refine ⟨fun w hw => ?_, fun w hw => ?_⟩
  · exact (approxMap_resampB₀NumK_window hst hα hθ hK hm hroom ef df hef hdf hJ w hw).trans hbud
  · exact resampB₀NumK_ball hst hα hθ hK ef df (offDiagW_err_alpha hst hα hθ hm ef hef) hroom
      hdf1 hJ w hw

end Maps

section Tables

open IntegerMultBounds.Resampling.TabledMaps (tol_of_int)

variable {s t : ℕ} [NeZero s] [NeZero t] {α : ℝ}

/-- `resampB₀NumK_spec` for integer weight tables within two units at scale `2^p`, with
`0 ≤ WD ≤ 2^p`, as in `TabledMaps.permuted_numeric_tabled`. -/
theorem resampB₀NumK_tabled (hst : s < t) (hα : 0 < α)
    (hθ : 1 ≤ α ^ 2 * ((t : ℝ) / s - 1)) {p K m : ℕ}
    (hK : (p : ℝ) ≤ α ^ 2 * ((t : ℝ) / s - 1) * K) (hm : (p : ℝ) ≤ 4 * α ^ 2 * (m : ℝ) ^ 2)
    (hp : 13 ≤ p) (hmp : 3 * m ≤ p) (WE : ZMod s → ℤ → ℤ) (WD : ZMod s → ℤ)
    (hWE : ∀ ℓ h, |(WE ℓ h : ℝ) - 2 ^ p * Real.exp (normExp s t α ℓ.val h)| ≤ 2)
    (hWD : ∀ ℓ, |(WD ℓ : ℝ) - 2 ^ p * dPrime s t α ℓ| ≤ 2) (hWD1 : ∀ ℓ, 0 ≤ WD ℓ ∧ WD ℓ ≤ 2 ^ p)
    {J : (ZMod s → ℂ) →L[ℂ] (ZMod s → ℂ)} (hJ : (1 + offDiagCLM s t α) ∘L J = 1) :
    ApproxMap p (resampB₀NumK p K m (fun ℓ h => (WE ℓ h : ℝ) / 2 ^ p) fun ℓ => (WD ℓ : ℝ) / 2 ^ p)
        (resampB₀ s t α J) ((p : ℝ) ^ 2) ∧
      ∀ w : ZMod t → ℂ, ‖w‖ ≤ 1 →
        ‖resampB₀NumK p K m (fun ℓ h => (WE ℓ h : ℝ) / 2 ^ p) (fun ℓ => (WD ℓ : ℝ) / 2 ^ p) w‖ ≤ 1 := by
  have hdf1 : ∀ ℓ, ‖rhoC p ((((WD ℓ : ℝ) / 2 ^ p : ℝ)) : ℂ)‖ ≤ 1 := by
    intro ℓ
    have hp' : (0 : ℝ) < 2 ^ p := by positivity
    rw [Resampling.WindowSum.rhoC_real, mul_div_cancel₀ _ hp'.ne', Resampling.NeumannWords.rho0_int,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (div_nonneg (by exact_mod_cast (hWD1 ℓ).1) hp'.le),
      div_le_one hp']
    exact_mod_cast (hWD1 ℓ).2
  exact resampB₀NumK_spec hst hα hθ hK hm hp hmp _ _ (fun ℓ h => tol_of_int p _ _ (hWE ℓ h))
    (fun ℓ => tol_of_int p _ _ (hWD ℓ)) hdf1 hJ

end Tables

end IntegerMultBounds.MathlibTM2.Mult.FastB0
