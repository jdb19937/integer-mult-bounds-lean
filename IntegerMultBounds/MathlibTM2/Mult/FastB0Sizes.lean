module

public import IntegerMultBounds.MathlibTM2.Mult.FastB0
public import IntegerMultBounds.MathlibTM2.Mult.SourceErr
public import IntegerMultBounds.MathlibTM2.Mult.Sizes

/-!
# `B̃₀` with few Neumann steps for the parameters of `Mult/Sizes.lean`

## Assembly

* `permuted_numeric_tabled_fast`: `TabledMaps.permuted_numeric_tabled` with
  `resampB₀NumK p K m'` for `B̃₀`, under `p ≤ α² θ K`, `p ≤ 4 α² m'²` and `3 m' ≤ p`.
* `sourceErr_of_tables_fast`: `SourceErr.sourceErr_of_tables` with `resampB₀NumK p K m'` on
  every axis.

## Parameters

* `steps_ceil`: `K = ⌈p / (α² θ)⌉₊` satisfies `p ≤ α² θ K`. `steps_alpha_sq`: so does
  `K = α²` when `p s < α⁴ (t - s)`; `ceil_steps_le_alpha_sq`: then `⌈p / (α² θ)⌉₊ ≤ α²`.
* `fastWindow p α = ⌊√p⌋ / (2α) + 1`; `fastWindow_sq`: `p ≤ 4 α² m'²`;
  `fastWindow_le_third`: `3 m' ≤ p` for `α ≥ 2`, `p ≥ 13`.
* `fastB0_conditions`: in the regime `Big n` every axis satisfies the step and window
  conditions with `K = α²` and `m' = fastWindow p α`. `resampB₀NumK_spec_big`: the
  hypotheses `hB'` and `hB'1` of `SourceErr.sourceErr_of_components` on each axis.
* `fastB0_count`: `K (2 m' + 1) ≤ 4 α ⌊√p⌋` and `(K (2 m' + 1))⁴ ≤ 8192 d² p³`; per line
  the `B̃₀` term products number `K · s · (2 m' + 1) ≤ 4 s α ⌊√p⌋`, which is
  `O(s · d^{1/2} · p^{3/4})`. `resampB₀NumW p (sqrtWindow p)` uses
  `p · s · (2 ⌊√p⌋ + 3)`.
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2.Mult.FastB0

open IntegerMultBounds IntegerMultBounds.NLogN
open ContinuousLinearMap Real

section Assembly

open IntegerMultBounds.Resampling.WindowSum (termW)
open IntegerMultBounds.Resampling.TabledMaps (tol_of_int approxMap_resampANumW)

variable {s t : ℕ} [NeZero s] [NeZero t] {α : ℝ}

/-- `TabledMaps.permuted_numeric_tabled` with `B̃₀` built from `K` Horner steps and the
window `m'`: the factorization, the contraction bounds, the errors below `p²` and the
unit-disk bounds. -/
theorem permuted_numeric_tabled_fast (hst : s < t) (hcop : Nat.Coprime s t) (hα : 2 ≤ α)
    (hθ : 1 ≤ α ^ 2 * ((t : ℝ) / s - 1)) {p m K m' : ℕ} (hαp : α ^ 2 ≤ p)
    (hm : (p : ℝ) * α ^ 2 ≤ (m : ℝ) ^ 2) (hm1 : 1 ≤ m) (hmp : m ≤ p) (hp : 13 ≤ p)
    (hK : (p : ℝ) ≤ α ^ 2 * ((t : ℝ) / s - 1) * K) (hm' : (p : ℝ) ≤ 4 * α ^ 2 * (m' : ℝ) ^ 2)
    (hm'p : 3 * m' ≤ p)
    (WA : ZMod t → ℤ → ℤ) (WE : ZMod s → ℤ → ℤ) (WD : ZMod s → ℤ)
    (hWA : ∀ k j, |(WA k j : ℝ) - 2 ^ p * resampWeight s t α k j| ≤ 2)
    (hWE : ∀ ℓ h, |(WE ℓ h : ℝ) - 2 ^ p * Real.exp (normExp s t α ℓ.val h)| ≤ 2)
    (hWD : ∀ ℓ, |(WD ℓ : ℝ) - 2 ^ p * dPrime s t α ℓ| ≤ 2) (hWD1 : ∀ ℓ, 0 ≤ WD ℓ ∧ WD ℓ ≤ 2 ^ p) :
    ∃ J : (ZMod s → ℂ) →L[ℂ] (ZMod s → ℂ),
      permSCLM t ∘L dftCLM s = ((2 : ℂ) ^ (2 * ⌈α ^ 2⌉₊ + 2)) •
        (resampB₀ s t α J ∘L permTCLM s ∘L dftCLM t ∘L resampA s t α) ∧
      ‖resampA s t α‖ ≤ 1 ∧ ‖resampB₀ s t α J‖ ≤ 1 ∧
      ApproxMap p (resampANum s t m (termW p fun k j => (WA k j : ℝ) / 2 ^ p)) (resampA s t α)
        (errA m) ∧
      ApproxMap p (resampB₀NumK p K m' (fun ℓ h => (WE ℓ h : ℝ) / 2 ^ p) fun ℓ => (WD ℓ : ℝ) / 2 ^ p)
        (resampB₀ s t α J) ((p : ℝ) ^ 2) ∧
      errA m < (p : ℝ) ^ 2 ∧
      (∀ u : ZMod s → ℂ, ‖u‖ ≤ 1 →
        ‖resampANum s t m (termW p fun k j => (WA k j : ℝ) / 2 ^ p) u‖ ≤ 1) ∧
      (∀ w : ZMod t → ℂ, ‖w‖ ≤ 1 →
        ‖resampB₀NumK p K m' (fun ℓ h => (WE ℓ h : ℝ) / 2 ^ p) (fun ℓ => (WD ℓ : ℝ) / 2 ^ p) w‖
          ≤ 1) := by
  have hα0 : (0 : ℝ) < α := by linarith
  obtain ⟨J, hJ, hJ', hJn⟩ := exists_left_inverse hst hα0 hθ
  obtain ⟨heq, hA, -⟩ := resampling_factorization_explicit hst hcop (by linarith) hθ J hJ
  have hAx := approxMap_resampANumW (s := s) (t := t) (by linarith) hαp hm hm1 _
    (fun k j => tol_of_int p _ _ (hWA k j))
  have hεA : errA m < (p : ℝ) ^ 2 := errA_lt_sq' hmp (by omega)
  have hpow : (4 : ℝ) * (p : ℝ) ^ 2 ≤ 2 ^ p := by exact_mod_cast four_sq_le_pow p hp
  have h4 : 4 * errA m ≤ 2 ^ p := by linarith
  have hA34 := opNorm_resampA_le_three_quarters (s := s) (t := t) hα
  have hAb : ∀ u : ZMod s → ℂ, ‖u‖ ≤ 1 →
      ‖resampANum s t m (termW p fun k j => (WA k j : ℝ) / 2 ^ p) u‖ ≤ 1 :=
    fun u hu => ball_of_approx hA34 hAx h4 u hu
  obtain ⟨hBx, hBb⟩ := resampB₀NumK_tabled hst hα0 hθ hK hm' hp hm'p WE WD hWE hWD hWD1 hJ'
  refine ⟨J, ?_, hA, opNorm_resampB₀_le J hJn, hAx, hBx, hεA, hAb, hBb⟩
  rw [resampB_eq hcop J] at heq
  rw [← permSEquiv_coe hcop, heq]
  ext u j
  simp only [comp_apply, smul_apply, map_smul, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.apply_symm_apply]

end Assembly

section SourceTables

open IntegerMultBounds.Resampling.WindowSum (termW)
open IntegerMultBounds.MathlibTM2.Mult.SourceErr (ApproxOn sourceApprox oppApprox sourceErr_of_components)

variable {d : ℕ} {s t : Fin d → ℕ} [∀ i, NeZero (s i)] [∀ i, NeZero (t i)]

/-- `SourceErr.sourceErr_of_tables` with `B̃₀` built from `K` Horner steps and the window
`m'` on every axis. -/
theorem sourceErr_of_tables_fast (hst : ∀ i, s i < t i) (hcop : ∀ i, Nat.Coprime (s i) (t i))
    (heven : ∀ i, 2 ∣ t i) {α : ℝ} (hα : 2 ≤ α)
    (hθ : ∀ i, 1 ≤ α ^ 2 * ((t i : ℝ) / s i - 1)) {p m L K m' : ℕ} (hαp : α ^ 2 ≤ p)
    (hm : (p : ℝ) * α ^ 2 ≤ (m : ℝ) ^ 2) (hm1 : 1 ≤ m) (hmp : m ≤ p) (hp : 13 ≤ p)
    (hK : ∀ i, (p : ℝ) ≤ α ^ 2 * ((t i : ℝ) / s i - 1) * K)
    (hm' : (p : ℝ) ≤ 4 * α ^ 2 * (m' : ℝ) ^ 2) (hm'p : 3 * m' ≤ p)
    (WA : ∀ i, ZMod (t i) → ℤ → ℤ) (WE : ∀ i, ZMod (s i) → ℤ → ℤ) (WD : ∀ i, ZMod (s i) → ℤ)
    (hWA : ∀ i k j, |(WA i k j : ℝ) - 2 ^ p * resampWeight (s i) (t i) α k j| ≤ 2)
    (hWE : ∀ i ℓ h, |(WE i ℓ h : ℝ) - 2 ^ p * Real.exp (normExp (s i) (t i) α ℓ.val h)| ≤ 2)
    (hWD : ∀ i ℓ, |(WD i ℓ : ℝ) - 2 ^ p * dPrime (s i) (t i) α ℓ| ≤ 2)
    (hWD1 : ∀ i ℓ, 0 ≤ WD i ℓ ∧ WD i ℓ ≤ 2 ^ p)
    {a' : ((i : Fin d) → ZMod (t i)) → ℂ}
    (ha' : ∀ j, 2 ^ p * ‖a' j - starRingEnd ℂ (chirpW t s j)‖ ≤ 2 ∧ ‖a' j‖ ≤ 1)
    {M' : (((i : Fin d) → ZMod (t i)) → ℂ) → (((i : Fin d) → ZMod (t i)) → ℂ) →
      (((i : Fin d) → ZMod (t i)) → ℂ)}
    (hM' : ∀ f g, ‖f‖ ≤ 1 → ‖g‖ ≤ 7 / 10 →
      2 ^ p * ‖M' f g - convNormD t f g‖ ≤ 6 * ((∏ i, t i : ℕ) : ℝ) * L ∧
        ‖M' f g‖ ≤ 701 / 1000)
    (hd : 0 < d) (hsmall : 2 * d * p ^ 2 ≤ (∏ i, t i) * L)
    (hEs : 9 * (2 : ℝ) ^ (d * (2 * ⌈α ^ 2⌉₊ + 2)) * ((∏ i, t i : ℕ) : ℝ) * L ≤ 2 ^ p / 100) :
    ApproxOn p (sourceApprox s t p (d * (2 * ⌈α ^ 2⌉₊ + 2))
        (fun i => resampANum (s i) (t i) m (termW p fun k j => (WA i k j : ℝ) / 2 ^ p))
        (fun i => resampB₀NumK p K m' (fun ℓ h => (WE i ℓ h : ℝ) / 2 ^ p)
          fun ℓ => (WD i ℓ : ℝ) / 2 ^ p) a' M')
        (permRCLM s t ∘L dftDCLM s) (1 / 2)
        (9 * (2 : ℝ) ^ (d * (2 * ⌈α ^ 2⌉₊ + 2)) * ((∏ i, t i : ℕ) : ℝ) * L) ∧
      ApproxOn p (oppApprox s t p (d * (2 * ⌈α ^ 2⌉₊ + 2))
        (fun i => resampANum (s i) (t i) m (termW p fun k j => (WA i k j : ℝ) / 2 ^ p))
        (fun i => resampB₀NumK p K m' (fun ℓ h => (WE i ℓ h : ℝ) / 2 ^ p)
          fun ℓ => (WD i ℓ : ℝ) / 2 ^ p) a' M')
        (permRCLM s t ∘L dftDPlusCLM s) (1 / 2)
        (9 * (2 : ℝ) ^ (d * (2 * ⌈α ^ 2⌉₊ + 2)) * ((∏ i, t i : ℕ) : ℝ) * L) := by
  choose J hJ hAn hBn hA' hB' hεA hA'1 hB'1 using fun i =>
    permuted_numeric_tabled_fast (hst i) (hcop i) hα (hθ i) hαp hm hm1 hmp hp (hK i) hm' hm'p
      (WA i) (WE i) (WD i) (hWA i) (hWE i) (hWD i) (hWD1 i)
  exact sourceErr_of_components heven J hJ hAn hBn
    (fun i v hv => (hA' i v hv).trans (hεA i).le) hA'1 hB' hB'1 ha' hM' hd (by omega) hsmall hEs

end SourceTables

/-! ### The parameters of `Mult/Sizes.lean` -/

section Params

/-- Steps: `α² θ K ≥ p` holds with `K = ⌈p / (α² θ)⌉₊`. -/
theorem steps_ceil {p : ℕ} {y : ℝ} (hy : 0 < y) : (p : ℝ) ≤ y * (⌈(p : ℝ) / y⌉₊ : ℕ) := by
  have h := Nat.le_ceil ((p : ℝ) / y)
  rw [div_le_iff₀ hy] at h
  linarith

/-- Steps: under the manuscript's `p s < α⁴ (t - s)`, i.e. `α⁴ θ > p`, the step count
`K = α²` satisfies `α² θ K ≥ p`. -/
theorem steps_alpha_sq {s t p a : ℕ} (hs : 0 < s) (hst : s < t) (hps : p * s < a ^ 4 * (t - s)) :
    (p : ℝ) ≤ (a : ℝ) ^ 2 * ((t : ℝ) / s - 1) * ((a ^ 2 : ℕ) : ℝ) := by
  have hs' : (0 : ℝ) < s := by exact_mod_cast hs
  have hps' : (p : ℝ) * s ≤ (a : ℝ) ^ 4 * ((t : ℝ) - s) := by
    have h := hps.le
    have : ((p * s : ℕ) : ℝ) ≤ ((a ^ 4 * (t - s) : ℕ) : ℝ) := by exact_mod_cast h
    push_cast [Nat.cast_sub hst.le] at this
    exact this
  have e : (a : ℝ) ^ 2 * ((t : ℝ) / s - 1) * ((a ^ 2 : ℕ) : ℝ) = (a : ℝ) ^ 4 * ((t : ℝ) - s) / s := by
    push_cast
    field_simp
  rw [e, le_div_iff₀ hs']
  exact hps'

/-- Steps: the same hypothesis bounds the ceiling count by `α²`. -/
theorem ceil_steps_le_alpha_sq {s t p a : ℕ} (hs : 0 < s) (hst : s < t) (ha : 0 < a)
    (hps : p * s < a ^ 4 * (t - s)) :
    ⌈(p : ℝ) / ((a : ℝ) ^ 2 * ((t : ℝ) / s - 1))⌉₊ ≤ a ^ 2 := by
  have hs' : (0 : ℝ) < s := by exact_mod_cast hs
  have hθ : 0 < (t : ℝ) / s - 1 := by
    rw [sub_pos, one_lt_div hs']; exact_mod_cast hst
  have ha' : (0 : ℝ) < a := by exact_mod_cast ha
  have hy : 0 < (a : ℝ) ^ 2 * ((t : ℝ) / s - 1) := by positivity
  rw [Nat.ceil_le, div_le_iff₀ hy]
  have := steps_alpha_sq hs hst hps
  push_cast at this ⊢
  linarith

/-- The window `m' = ⌊√p⌋ / (2α) + 1`. -/
def fastWindow (p a : ℕ) : ℕ := Nat.sqrt p / (2 * a) + 1

/-- The window condition `p ≤ 4 α² m'²`. -/
theorem fastWindow_sq (p a : ℕ) (ha : 1 ≤ a) :
    (p : ℝ) ≤ 4 * (a : ℝ) ^ 2 * (fastWindow p a : ℝ) ^ 2 := by
  have h1 : Nat.sqrt p + 1 ≤ 2 * a * fastWindow p a := by
    unfold fastWindow
    exact Nat.lt_mul_div_succ _ (by omega)
  have h2 := Nat.lt_succ_sqrt' p
  have h3 : p ≤ 4 * a ^ 2 * fastWindow p a ^ 2 := by
    have : (Nat.sqrt p + 1) ^ 2 ≤ (2 * a * fastWindow p a) ^ 2 := Nat.pow_le_pow_left h1 2
    rw [Nat.succ_eq_add_one] at h2
    nlinarith
  exact_mod_cast h3

theorem fastWindow_le_third {p a : ℕ} (ha : 2 ≤ a) (hp : 13 ≤ p) : 3 * fastWindow p a ≤ p := by
  unfold fastWindow
  have h1 : Nat.sqrt p / (2 * a) ≤ Nat.sqrt p / 4 := Nat.div_le_div_left (by omega) (by norm_num)
  have h2 := Nat.sqrt_le_self p
  omega

/-- The step-window product: `α² (2 m' + 1) ≤ 4 α ⌊√p⌋` when `α² ≤ p`. -/
theorem steps_mul_window_le {p a : ℕ} (hap : a ^ 2 ≤ p) :
    a ^ 2 * (2 * fastWindow p a + 1) ≤ 4 * a * Nat.sqrt p := by
  have hx : a ≤ Nat.sqrt p := Nat.le_sqrt'.mpr hap
  have hq : Nat.sqrt p / (2 * a) * (2 * a) ≤ Nat.sqrt p := Nat.div_mul_le_self _ _
  unfold fastWindow
  set q := Nat.sqrt p / (2 * a)
  set x := Nat.sqrt p
  have e : a ^ 2 * (2 * (q + 1) + 1) = a * (q * (2 * a)) + 3 * (a * a) := by ring
  rw [e]
  have h1 : a * (q * (2 * a)) ≤ a * x := Nat.mul_le_mul_left _ hq
  have h2 : a * a ≤ a * x := Nat.mul_le_mul_left _ hx
  nlinarith

open Sizes in
/-- Our parameters satisfy the step and window conditions with `K = α²` and
`m' = ⌊√p⌋ / (2α) + 1`, together with `3 m' ≤ p` and `p ≥ 13`. -/
theorem fastB0_conditions {n : ℕ} (h : Big n) (i : Fin (d n)) :
    (p n : ℝ) ≤ (alpha n : ℝ) ^ 2 * ((t n i : ℝ) / s n i - 1) * ((alpha n ^ 2 : ℕ) : ℝ) ∧
      (p n : ℝ) ≤ 4 * (alpha n : ℝ) ^ 2 * (fastWindow (p n) (alpha n) : ℝ) ^ 2 ∧
      3 * fastWindow (p n) (alpha n) ≤ p n ∧ 13 ≤ p n := by
  have hg := h.good
  have ha := two_le_alpha h.1
  exact ⟨steps_alpha_sq (hg.odd i).pos (hg.lt i) (h.p_mul_s_lt i), fastWindow_sq _ _ (by omega),
    fastWindow_le_third ha h.thirteen_le_p, h.thirteen_le_p⟩

open Sizes in
/-- The hypotheses `hB'` and `hB'1` of `SourceErr.sourceErr_of_components` for our
parameters, on axis `i`, with `K = α²` Horner steps and the window
`m' = ⌊√p⌋ / (2α) + 1`. -/
theorem resampB₀NumK_spec_big {n : ℕ} (h : Big n) (i : Fin (d n)) [NeZero (s n i)]
    [NeZero (t n i)] (ef : ZMod (s n i) → ℤ → ℝ) (df : ZMod (s n i) → ℝ)
    (hef : ∀ ℓ k, 2 ^ p n * ‖rhoC (p n) (ef ℓ k : ℂ) -
      (Real.exp (normExp (s n i) (t n i) (alpha n) ℓ.val k) : ℂ)‖ ≤ 2)
    (hdf : ∀ ℓ, 2 ^ p n * ‖rhoC (p n) (df ℓ : ℂ) - (dPrime (s n i) (t n i) (alpha n) ℓ : ℂ)‖ ≤ 2)
    (hdf1 : ∀ ℓ, ‖rhoC (p n) (df ℓ : ℂ)‖ ≤ 1)
    {J : (ZMod (s n i) → ℂ) →L[ℂ] (ZMod (s n i) → ℂ)}
    (hJ : (1 + offDiagCLM (s n i) (t n i) (alpha n)) ∘L J = 1) :
    ApproxMap (p n) (resampB₀NumK (t := t n i) (p n) (alpha n ^ 2) (fastWindow (p n) (alpha n)) ef df)
        (resampB₀ (s n i) (t n i) (alpha n) J) ((p n : ℝ) ^ 2) ∧
      ∀ w : ZMod (t n i) → ℂ, ‖w‖ ≤ 1 →
        ‖resampB₀NumK (p n) (alpha n ^ 2) (fastWindow (p n) (alpha n)) ef df w‖ ≤ 1 := by
  obtain ⟨hK, hm, hmp, hp⟩ := fastB0_conditions h i
  have hα : (0 : ℝ) < alpha n := by
    have := two_le_alpha h.1
    exact_mod_cast (by omega : 0 < alpha n)
  exact FastB0.resampB₀NumK_spec ((h.good).lt i) hα (h.one_le_alpha_sq_theta i) hK hm hp hmp ef df
    hef hdf hdf1 hJ

open Sizes in
/-- Per-line step-window counts for our parameters, with `K = α²` and
`m' = ⌊√p⌋ / (2α) + 1`: `K (2 m' + 1) ≤ 4 α ⌊√p⌋`, `(K (2 m' + 1))⁴ ≤ 8192 d² p³`, and on
axis `i` the `K · s · (2 m' + 1)` term products of `B̃₀` number at most `4 s α ⌊√p⌋`,
which is `O(s · α · √p) = O(s · d^{1/2} · p^{3/4})`. -/
theorem fastB0_count {n : ℕ} (h : Big n) :
    alpha n ^ 2 * (2 * fastWindow (p n) (alpha n) + 1) ≤ 4 * alpha n * Nat.sqrt (p n) ∧
      (alpha n ^ 2 * (2 * fastWindow (p n) (alpha n) + 1)) ^ 4 ≤ 8192 * d n ^ 2 * p n ^ 3 ∧
      ∀ i : Fin (d n), alpha n ^ 2 * s n i * (2 * fastWindow (p n) (alpha n) + 1) ≤
        4 * s n i * alpha n * Nat.sqrt (p n) := by
  have hap := h.alpha_sq_le_p
  have h1 := steps_mul_window_le hap
  refine ⟨h1, ?_, fun i => ?_⟩
  · have h4 := alpha_pow_four_le h.1
    have hx : Nat.sqrt (p n) ^ 2 ≤ p n := Nat.sqrt_le' _
    have hx4 : Nat.sqrt (p n) ^ 4 ≤ p n ^ 2 := by
      calc Nat.sqrt (p n) ^ 4 = (Nat.sqrt (p n) ^ 2) ^ 2 := by ring
        _ ≤ p n ^ 2 := Nat.pow_le_pow_left hx 2
    have hp6 : p n = 6 * b n := rfl
    calc (alpha n ^ 2 * (2 * fastWindow (p n) (alpha n) + 1)) ^ 4
        ≤ (4 * alpha n * Nat.sqrt (p n)) ^ 4 := Nat.pow_le_pow_left h1 4
      _ = 256 * alpha n ^ 4 * Nat.sqrt (p n) ^ 4 := by ring
      _ ≤ 256 * (192 * d n ^ 2 * b n) * p n ^ 2 := by
          apply Nat.mul_le_mul (Nat.mul_le_mul_left _ h4) hx4
      _ = 8192 * d n ^ 2 * p n ^ 3 := by rw [hp6]; ring
  · calc alpha n ^ 2 * s n i * (2 * fastWindow (p n) (alpha n) + 1)
        = s n i * (alpha n ^ 2 * (2 * fastWindow (p n) (alpha n) + 1)) := by ring
      _ ≤ s n i * (4 * alpha n * Nat.sqrt (p n)) := Nat.mul_le_mul_left _ h1
      _ = 4 * s n i * alpha n * Nat.sqrt (p n) := by ring

end Params

end IntegerMultBounds.MathlibTM2.Mult.FastB0
