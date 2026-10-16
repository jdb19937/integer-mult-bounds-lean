module

public import IntegerMultBounds.Schoenhage.ConvTarget
public import IntegerMultBounds.Schoenhage.RingPointwiseTarget
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Analysis.SpecialFunctions.Log.Base

/-! The convolution program's steps beyond its three transforms are within a
constant times the paper's convolution cost for all large `p`
(`convExtra_le_cost`): the pointwise products cost `O(T p log (r p) log log (r p))`
and the `log log` factor is absorbed by `ℓ d^λ'` once `p` is large; scaling,
the header and data movement are `O(T p + p² + H)`, with `H = O(p)` and `p ≤ T`. -/

@[expose] public section

namespace IntegerMultBounds.Schoenhage

open Machine Strm Tp Schedule Spec.SignedRingProduct

/-! ### Word lengths -/

theorem length_gamma_le (v : ℕ) : (gamma v).length ≤ 2 * v + 1 := by
  rcases Nat.eq_zero_or_pos v with rfl | hv
  · simp [gamma, msbBits]
  · rw [length_gamma hv]; have := size_le_self v; omega

theorem length_gamma_pow (e : ℕ) : (gamma (2 ^ e)).length = 2 * e + 1 := by
  rw [length_gamma Nat.one_le_two_pow, Nat.size_pow]; omega

theorem length_axes_le {d ℓ : ℕ} {ts : List ℕ} (h : AxisLengths d ℓ ts) :
    (ts.flatMap gamma).length ≤ (2 * ℓ + 1) * ts.length := by
  have : ∀ t ∈ ts, (gamma t).length ≤ 2 * ℓ + 1 := fun t ht => by
    rcases h.2 t ht with rfl | rfl <;> rw [length_gamma_pow] <;> omega
  clear h
  induction ts with
  | nil => simp
  | cons t ts ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    have h1 := this t (by simp)
    have h2 := ih (fun x hx => this x (by simp [hx]))
    nlinarith

theorem length_header_le {p d ℓ K w : ℕ} {ts : List ℕ} (h : AxisLengths d ℓ ts) :
    (transformHeader p d (2 ^ ℓ) K w ts).length ≤ 2 * (p + d + K + w) + 4 + (2 * ℓ + 1) * (d + 1) := by
  simp only [transformHeader, List.length_append, length_gamma_pow]
  have h1 := length_gamma_le p
  have h2 := length_gamma_le d
  have h3 := length_gamma_le K
  have h4 := length_gamma_le w
  have h5 := length_axes_le h
  have hl : ts.length ≤ d := by rw [h.1]; omega
  have : (2 * ℓ + 1) * ts.length + (2 * ℓ + 1) ≤ (2 * ℓ + 1) * (d + 1) := by nlinarith
  omega

theorem prod_le_pow {d ℓ : ℕ} {ts : List ℕ} (h : AxisLengths d ℓ ts) : ts.prod ≤ 2 ^ (ℓ * ts.length) := by
  have : ∀ t ∈ ts, t ≤ 2 ^ ℓ := fun t ht => by
    rcases h.2 t ht with rfl | rfl
    · exact Nat.pow_le_pow_right (by norm_num) (Nat.sub_le ℓ 1)
    · exact le_rfl
  clear h
  induction ts with
  | nil => simp
  | cons t ts ih =>
    rw [List.prod_cons, List.length_cons, Nat.mul_succ, pow_add, Nat.mul_comm (2 ^ (ℓ * ts.length))]
    exact Nat.mul_le_mul (this t (by simp)) (ih fun x hx => this x (by simp [hx]))

theorem log_prod_le {d ℓ : ℕ} {ts : List ℕ} (h : AxisLengths d ℓ ts) : Nat.log 2 ts.prod ≤ ℓ * d := by
  have h1 := Nat.log_mono_right (b := 2) (prod_le_pow h)
  rw [Nat.log_pow (by norm_num)] at h1
  have : ℓ * ts.length ≤ ℓ * d := Nat.mul_le_mul_left _ (by rw [h.1]; omega)
  omega

/-! ### The remainder in closed form -/

theorem pwCost_le_pointwiseTime {Cw p d ℓ K w H M : ℕ} (hwC : w ≤ Cw * p) :
    pwCost p d ℓ K w H M (2 * 2 ^ ℓ * w * M) ≤ pointwiseTime Cw (2 ^ ℓ * M) p (2 ^ ℓ) H := by
  unfold pointwiseTime
  let g := fun w' => pwCost p 0 (Nat.log 2 (2 ^ ℓ)) 0 w' H (2 ^ ℓ * M / 2 ^ ℓ) (2 * (2 ^ ℓ * M) * w') +
    4 * (H + 3 * (2 * (2 ^ ℓ * M) * w')) + 60
  have hle : g w ≤ (Finset.range (Cw * p + 1)).sup g := Finset.le_sup (Finset.mem_range.mpr (by omega))
  refine le_trans ?_ hle
  have e : pwCost p 0 (Nat.log 2 (2 ^ ℓ)) 0 w H (2 ^ ℓ * M / 2 ^ ℓ) (2 * (2 ^ ℓ * M) * w) =
      pwCost p d ℓ K w H M (2 * 2 ^ ℓ * w * M) := by
    rw [Nat.log_pow (by norm_num), Nat.mul_div_cancel_left _ (by positivity),
      show 2 * (2 ^ ℓ * M) * w = 2 * 2 ^ ℓ * w * M by ring]
    rfl
  simp only [g, e]
  omega

theorem convExtra_le {p d ℓ K w H M : ℕ} :
    convExtra p d ℓ K w H M ≤ pwCost p d ℓ K w H M (2 * 2 ^ ℓ * w * M) + 600 * H +
      70 * (2 * 2 ^ ℓ * w * M) + 2 * 2 ^ ℓ * M * (4 * Nat.log 2 M + 60) + 8 * (2 ^ ℓ * (w + Nat.log 2 M) * M) +
      42 * (p * (2 * p + 10) + (ℓ + 1) * (ℓ + 1 + 2 ^ ℓ + 10) + w * (2 * w + 10)) +
      300 * (p + w + Nat.log 2 M + 2 ^ ℓ) + 10000 := by
  have hsp : Nat.size p * (Nat.size p + p + 10) ≤ p * (2 * p + 10) := by
    have := size_le_self p; nlinarith
  have hsw : Nat.size w * (Nat.size w + w + 10) ≤ w * (2 * w + 10) := by
    have := size_le_self w; nlinarith
  have hsr : Nat.size (2 ^ ℓ) = ℓ + 1 := Nat.size_pow
  have hg := length_gamma_le (w + Nat.log 2 M)
  unfold convExtra convScaleCost headerCost coreExtra
  rw [hsr]
  generalize Nat.size p * (Nat.size p + p + 10) = A at *
  generalize Nat.size w * (Nat.size w + w + 10) = B at *
  generalize pwCost p d ℓ K w H M (2 * 2 ^ ℓ * w * M) = Q
  generalize 2 * 2 ^ ℓ * w * M = X
  ring_nf
  ring_nf at hsp hsw hg
  omega

/-! ### Large `p` -/

open Filter in
/-- `log₂ p + c ≤ A p^s` for all large `p`. -/
theorem eventually_logb_le {A s : ℝ} (hA : 0 < A) (hs : 0 < s) (c : ℝ) :
    ∃ N : ℕ, ∀ p : ℕ, N ≤ p → Real.logb 2 p + c ≤ A * (p : ℝ) ^ s := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have ho := (isLittleO_log_rpow_atTop hs).def (c := A * Real.log 2 / 2) (by positivity)
  have ht : Tendsto (fun x : ℝ => x ^ s) atTop atTop := tendsto_rpow_atTop hs
  have hb := ht.eventually_ge_atTop (2 * (|c| + 1) / A)
  have hp := eventually_ge_atTop (1 : ℝ)
  have hall := (ho.and (hb.and hp))
  obtain ⟨N, hN⟩ := (tendsto_natCast_atTop_atTop.eventually hall).exists_forall_of_atTop
  refine ⟨N, fun p hpN => ?_⟩
  obtain ⟨h1, h2, h3⟩ := hN p hpN
  have hx : (0 : ℝ) ≤ (p : ℝ) ^ s := Real.rpow_nonneg (by positivity) _
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hx] at h1
  have hlog : Real.log p ≤ A * Real.log 2 / 2 * (p : ℝ) ^ s := le_trans (le_abs_self _) h1
  have hlb : Real.logb 2 p ≤ A / 2 * (p : ℝ) ^ s := by
    rw [Real.logb, div_le_iff₀ hl2]
    nlinarith
  have hc : c ≤ A / 2 * (p : ℝ) ^ s := by
    have := mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ A / 2)
    have e : A / 2 * (2 * (|c| + 1) / A) = |c| + 1 := by field_simp
    rw [e] at this
    linarith [le_abs_self c]
  linarith

theorem natLog_le_logb (p : ℕ) (hp : 1 ≤ p) : (Nat.log 2 p : ℝ) ≤ Real.logb 2 p := by
  rw [Real.le_logb_iff_rpow_le (by norm_num) (by exact_mod_cast hp), Real.rpow_natCast]
  exact_mod_cast Nat.pow_log_le_self 2 (by omega)

theorem log_two_pow_mul_le (ℓ p : ℕ) (hp : 1 ≤ p) : Nat.log 2 (2 ^ ℓ * p) ≤ ℓ + Nat.log 2 p := by
  have h := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) p
  have h2 : 2 ^ ℓ * p < 2 ^ (ℓ + Nat.log 2 p + 1) := by
    rw [show ℓ + Nat.log 2 p + 1 = ℓ + (Nat.log 2 p).succ by omega, pow_add]
    exact Nat.mul_lt_mul_of_pos_left h (by positivity)
  have := Nat.log_lt_of_lt_pow (by positivity) h2
  omega

theorem log_two_mul (p : ℕ) (hp : 1 ≤ p) : Nat.log 2 (2 * p) = Nat.log 2 p + 1 := by
  rw [Nat.mul_comm, Nat.log_mul_base (by norm_num) (by omega)]

theorem rest_bound {T p w k H l r2 CwR Cl CH : ℝ} (hp : 2 ≤ p) (hpT : p ≤ T) (hw0 : 0 ≤ w) (_hk0 : 0 ≤ k)
    (hl0 : 0 ≤ l) (hwp : w ≤ CwR * p) (hkp : k ≤ Cl * p) (hlp : l + 1 ≤ p) (hH : H ≤ CH * p) (hr : r2 ≤ T)
    (hr0 : 0 ≤ r2) (hCw : 0 ≤ CwR) (hCl : 0 ≤ Cl) (hCH : 0 ≤ CH) :
    600 * H + 70 * (2 * T * w) + 2 * T * (4 * k + 60) + 8 * (T * (w + k)) +
      42 * (p * (2 * p + 10) + (l + 1) * (l + 1 + r2 + 10) + w * (2 * w + 10)) + 300 * (p + w + k + r2) + 10000 ≤
    (600 * CH + 140 * CwR + 8 * Cl + 60 + 8 * (CwR + Cl) + 630 + 42 * (2 * CwR ^ 2 + 5 * CwR) +
      300 * (2 + CwR + Cl) + 2500) * (T * p) := by
  have hT0 : 0 ≤ T := by linarith
  have hp0 : 0 ≤ p := by linarith
  have hpp : p * p ≤ T * p := mul_le_mul_of_nonneg_right hpT hp0
  have hTp2 : 2 * T ≤ T * p := by have := mul_le_mul_of_nonneg_left hp hT0; linarith
  have hpTp : 2 * p ≤ T * p := by have := mul_le_mul_of_nonneg_right (le_trans hp hpT) hp0; linarith
  have hTp4 : 4 ≤ T * p := by
    linarith only [mul_le_mul hp hp (by norm_num) hp0, hpp]
  have hpTp1 : p ≤ T * p := by linarith
  have b1 : 600 * H ≤ 600 * CH * (T * p) := by
    have := mul_le_mul_of_nonneg_left hpTp1 hCH
    linarith only [hH, this]
  have b2 : 70 * (2 * T * w) ≤ 140 * CwR * (T * p) := by
    have := mul_le_mul_of_nonneg_left hwp hT0
    linarith only [this]
  have b3 : 2 * T * (4 * k + 60) ≤ (8 * Cl + 60) * (T * p) := by
    have := mul_le_mul_of_nonneg_left hkp hT0
    linarith only [this, hTp2]
  have b4 : 8 * (T * (w + k)) ≤ 8 * (CwR + Cl) * (T * p) := by
    have hTw := mul_le_mul_of_nonneg_left hwp hT0
    have hTk := mul_le_mul_of_nonneg_left hkp hT0
    linarith only [hTw, hTk]
  have b5 : 42 * (p * (2 * p + 10) + (l + 1) * (l + 1 + r2 + 10)) ≤ 630 * (T * p) := by
    have hphase : (l + 1) * (l + 1 + r2 + 10) ≤ p * (p + T + 10) :=
      mul_le_mul hlp (by linarith) (by positivity) hp0
    linarith only [hphase, hpp, hpTp, hTp4]
  have b6 : 42 * (w * (2 * w + 10)) ≤ 42 * (2 * CwR ^ 2 + 5 * CwR) * (T * p) := by
    have hww : w * w ≤ (CwR * p) * (CwR * p) := mul_le_mul hwp hwp hw0 (by positivity)
    have h1 : (CwR * p) * (CwR * p) ≤ CwR ^ 2 * (T * p) := by
      have := mul_le_mul_of_nonneg_left hpp (sq_nonneg CwR)
      linarith only [this]
    have h2 : w * 10 ≤ 5 * CwR * (T * p) := by
      have := mul_le_mul_of_nonneg_left hpTp hCw
      linarith only [this, hwp]
    linarith only [hww, h1, h2]
  have b7 : 300 * (p + w + k + r2) ≤ 300 * (2 + CwR + Cl) * (T * p) := by
    have hCwp := mul_le_mul_of_nonneg_left hpTp1 hCw
    have hClp := mul_le_mul_of_nonneg_left hpTp1 hCl
    have hTTp : T ≤ T * p := by linarith only [hTp2, hT0]
    linarith only [hpTp1, hwp, hkp, hr, hCwp, hClp, hTTp]
  linarith only [b1, b2, b3, b4, b5, b6, b7, hTp4]

/-- The convolution program's remainder is within a constant times the paper's cost for large `p`. -/
theorem convExtra_le_cost (P : TransformParams) (hε0 : 0 < P.ε) (hε1 : P.ε < 1) (hlam : 0 < P.lam')
    (had : 0 < P.ad) (har : 0 < P.ar) (hbd : 0 < P.bd) :
    ∃ (p₂ : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ p d ℓ K w ts, p₂ ≤ p → Admissible P p d ℓ K w ts →
      (convExtra p d ℓ K w (transformHeader p d (2 ^ ℓ) K w ts).length ts.prod : ℝ) ≤
        C * convolutionCost P p d ℓ K ts := by
  set Cw := max P.Cw 2
  obtain ⟨Cp, hCp⟩ := pointwiseTime_le Cw (le_max_right _ _)
  obtain ⟨N1, hN1⟩ := eventually_logb_le (A := P.ar / P.bd) (s := 1 - P.ε) (by positivity) (by linarith) 2
  obtain ⟨N2, hN2⟩ := eventually_logb_le (A := P.ad ^ P.lam') (s := P.ε * P.lam')
    (Real.rpow_pos_of_pos had _) (by positivity) 3
  set Cl := max P.Cl 0
  set CwR : ℝ := (Cw : ℝ)
  set CH : ℝ := 10 + 2 * CwR + 5 * Cl
  set Rc : ℝ := 600 * CH + 140 * CwR + 8 * Cl + 60 + 8 * (CwR + Cl) + 630 + 42 * (2 * CwR ^ 2 + 5 * CwR) +
    300 * (2 + CwR + Cl) + 2500
  have hCw0 : (0 : ℝ) ≤ CwR := by positivity
  have hCl0 : (0 : ℝ) ≤ Cl := le_max_right _ _
  have hCH0 : 0 ≤ CH := by positivity
  have hRc0 : 0 ≤ Rc := by positivity
  refine ⟨max (max N1 N2) 2, 2 * Cp + Cp * CH + Rc, by positivity, ?_⟩
  intro p d ℓ K w ts hp hadm
  obtain ⟨hdlo, hdhi, hrlo, -, hd2, hℓ2, hℓp, hdl, -, hK1, hKℓ, hax, hpw, hwC⟩ := hadm
  have hp2 : 2 ≤ p := le_trans (le_max_right _ _) hp
  have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hp2
  have hp0 : (0 : ℝ) < p := by linarith
  set M := ts.prod
  have hM1 : 1 ≤ M := prod_pos_of_axes hax
  set T := 2 ^ ℓ * M
  set H := (transformHeader p d (2 ^ ℓ) K w ts).length
  set k := Nat.log 2 M
  set L := Nat.log 2 (2 ^ ℓ * p)
  set LL := Nat.log 2 (L + 1)
  -- the axis length
  have hd2R : (2 : ℝ) ≤ d := by exact_mod_cast hd2
  have hd0 : (0 : ℝ) < d := by linarith
  have hlow : P.ar * p / d ≤ ℓ := by
    have h := hrlo
    rw [← Real.rpow_natCast 2 ℓ] at h
    exact (Real.rpow_le_rpow_left_iff (by norm_num : (1 : ℝ) < 2)).mp h
  have hpe : (0 : ℝ) < (p : ℝ) ^ P.ε := Real.rpow_pos_of_pos hp0 _
  have hpow1 : (p : ℝ) ^ (1 - P.ε) = p / (p : ℝ) ^ P.ε := by
    rw [Real.rpow_sub hp0, Real.rpow_one]
  have hℓbig : P.ar / P.bd * (p : ℝ) ^ (1 - P.ε) ≤ ℓ := by
    rw [hpow1]
    calc P.ar / P.bd * (p / (p : ℝ) ^ P.ε) = P.ar * p / (P.bd * (p : ℝ) ^ P.ε) := by field_simp
      _ ≤ P.ar * p / d := by
          apply div_le_div_of_nonneg_left (by positivity) hd0 hdhi
      _ ≤ ℓ := hlow
  have h1 := hN1 p (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hp)
  have hlogp := natLog_le_logb p (by omega)
  have hlogℓ : (Nat.log 2 p : ℝ) + 2 ≤ ℓ := by linarith
  have hlogℓN : Nat.log 2 p + 2 ≤ ℓ := by exact_mod_cast hlogℓ
  -- `L`, `LL`
  have hL : L ≤ ℓ + Nat.log 2 p := log_two_pow_mul_le ℓ p (by omega)
  have hL1 : L + 1 ≤ 2 * ℓ := by omega
  have hLL : LL ≤ Nat.log 2 p + 1 := by
    have : LL ≤ Nat.log 2 (2 * p) := Nat.log_mono_right (by omega)
    rw [log_two_mul p (by omega)] at this; exact this
  have hdlam : P.ad ^ P.lam' * (p : ℝ) ^ (P.ε * P.lam') ≤ (d : ℝ) ^ P.lam' := by
    rw [Real.rpow_mul hp0.le, ← Real.mul_rpow had.le hpe.le]
    exact Real.rpow_le_rpow (by positivity) hdlo hlam.le
  have h2 := hN2 p (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hp)
  have hLLd : (LL : ℝ) + 1 ≤ (d : ℝ) ^ P.lam' := by
    have : (LL : ℝ) ≤ Nat.log 2 p + 1 := by exact_mod_cast hLL
    linarith
  -- `p ≤ T`
  have hpT : p ≤ T := by
    have h3 := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) p
    have h4 : 2 ^ (Nat.log 2 p).succ ≤ 2 ^ ℓ := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h5 : 2 ^ ℓ ≤ T := Nat.le_mul_of_pos_right _ hM1
    omega
  have hrT : 2 ^ ℓ ≤ T := Nat.le_mul_of_pos_right _ hM1
  have hTR : (p : ℝ) ≤ T := by exact_mod_cast hpT
  have hT0 : (0 : ℝ) < T := by linarith
  -- the cost
  have hdK : (0 : ℝ) ≤ d * K + p * (K : ℝ) ^ (P.τ - 1) := by
    have := Real.rpow_nonneg (Nat.cast_nonneg K) (P.τ - 1); positivity
  have hdl0 : (0 : ℝ) ≤ (d : ℝ) ^ P.lam' := Real.rpow_nonneg hd0.le _
  have htc_eq : transformCost P p d ℓ K ts =
      (T : ℝ) * p * (d * K + p * (K : ℝ) ^ (P.τ - 1) + ℓ * (d : ℝ) ^ P.lam') := rfl
  have htc : (T : ℝ) * p * (ℓ * (d : ℝ) ^ P.lam') ≤ transformCost P p d ℓ K ts := by
    rw [htc_eq]
    have : (0 : ℝ) ≤ (T : ℝ) * p * (d * K + p * (K : ℝ) ^ (P.τ - 1)) := by positivity
    linarith only [this]
  have hconv : convolutionCost P p d ℓ K ts = transformCost P p d ℓ K ts + (T : ℝ) * p * (L + 1) := rfl
  have hTp : (T : ℝ) * p ≤ convolutionCost P p d ℓ K ts := by
    rw [hconv]
    have : (0 : ℝ) ≤ transformCost P p d ℓ K ts := le_trans (by positivity) htc
    have hL0 : (0 : ℝ) ≤ (T : ℝ) * p * L := by positivity
    have e : (T : ℝ) * p * (L + 1) = T * p * L + T * p := by ring
    linarith
  have htc_le : transformCost P p d ℓ K ts ≤ convolutionCost P p d ℓ K ts := by
    rw [hconv]; have : (0 : ℝ) ≤ (T : ℝ) * p * (L + 1) := by positivity
    linarith
  -- the pointwise products
  have hpw' : pwCost p d ℓ K w H M (2 * 2 ^ ℓ * w * M) ≤
      Cp * (T * p * (L + 1) * (LL + 1) + H) :=
    (pwCost_le_pointwiseTime (Cw := Cw) (le_trans hwC (Nat.mul_le_mul_right _ (le_max_left _ _)))).trans
      (hCp p ℓ M H (by omega) hp2 hℓp hM1)
  have hLLR : ((L : ℝ) + 1) * ((LL : ℝ) + 1) ≤ 2 * (ℓ * (d : ℝ) ^ P.lam') := by
    have a : (L : ℝ) + 1 ≤ 2 * ℓ := by exact_mod_cast hL1
    calc
      _ ≤ (2 * ℓ) * (d : ℝ) ^ P.lam' := mul_le_mul a hLLd (by positivity) (by positivity)
      _ = _ := by ring
  have hpwR : (pwCost p d ℓ K w H M (2 * 2 ^ ℓ * w * M) : ℝ) ≤
      Cp * (2 * transformCost P p d ℓ K ts + H) := by
    have := (Nat.cast_le (α := ℝ)).mpr hpw'
    push_cast at this
    have hTpL : (T : ℝ) * p * (L + 1) * (LL + 1) ≤ 2 * ((T : ℝ) * p * (ℓ * (d : ℝ) ^ P.lam')) := by
      have : (T : ℝ) * p * (((L : ℝ) + 1) * ((LL : ℝ) + 1)) ≤ (T : ℝ) * p * (2 * (ℓ * (d : ℝ) ^ P.lam')) :=
        mul_le_mul_of_nonneg_left hLLR (by positivity)
      linarith
    have hTpC : (T : ℝ) * p * (L + 1) * (LL + 1) ≤
        2 * transformCost P p d ℓ K ts := hTpL.trans (by linarith only [htc])
    exact this.trans (mul_le_mul_of_nonneg_left
      (add_le_add hTpC (le_refl (H : ℝ))) (Nat.cast_nonneg _))
  -- the header
  have hdlR : ((d * ℓ : ℕ) : ℝ) ≤ Cl * p := le_trans hdl (mul_le_mul_of_nonneg_right (le_max_left _ _) hp0.le)
  have hHn := length_header_le (p := p) (K := K) (w := w) hax
  have hH : (H : ℝ) ≤ CH * p := by
    have a := (Nat.cast_le (α := ℝ)).mpr hHn
    push_cast at a hdlR
    have hdd : (d : ℝ) ≤ d * ℓ := by
      have : (1 : ℝ) ≤ ℓ := by exact_mod_cast (by omega : 1 ≤ ℓ)
      nlinarith only [this, hd0]
    have hKp : (K : ℝ) ≤ p := by exact_mod_cast (by omega : K ≤ p)
    have hℓp' : (ℓ : ℝ) ≤ p := by exact_mod_cast hℓp.le
    have hwp : (w : ℝ) ≤ CwR * p := by
      have h : w ≤ Cw * p := le_trans hwC (Nat.mul_le_mul_right p (le_max_left P.Cw 2))
      calc (w : ℝ) ≤ ((Cw * p : ℕ) : ℝ) := by exact_mod_cast h
        _ = CwR * p := by push_cast; rfl
    simp only [CH]
    linarith only [a, hdd, hKp, hℓp', hwp, hdlR, hpR]
  -- the remainder
  have hrest := convExtra_le (p := p) (d := d) (ℓ := ℓ) (K := K) (w := w) (H := H) (M := M)
  have hkR : (k : ℝ) ≤ Cl * p := by
    have := (Nat.cast_le (α := ℝ)).mpr (log_prod_le hax)
    push_cast at this hdlR
    linarith [mul_comm (ℓ : ℝ) d]
  have hwp : (w : ℝ) ≤ CwR * p := by
    have h : w ≤ Cw * p := le_trans hwC (Nat.mul_le_mul_right p (le_max_left P.Cw 2))
    calc (w : ℝ) ≤ ((Cw * p : ℕ) : ℝ) := by exact_mod_cast h
      _ = CwR * p := by push_cast; rfl
  have hℓp' : (ℓ : ℝ) + 1 ≤ p := by exact_mod_cast hℓp
  have hrTR : ((2 ^ ℓ : ℕ) : ℝ) ≤ T := by exact_mod_cast hrT
  have hR : ((600 * H + 70 * (2 * 2 ^ ℓ * w * M) + 2 * 2 ^ ℓ * M * (4 * k + 60) + 8 * (2 ^ ℓ * (w + k) * M) +
      42 * (p * (2 * p + 10) + (ℓ + 1) * (ℓ + 1 + 2 ^ ℓ + 10) + w * (2 * w + 10)) +
      300 * (p + w + k + 2 ^ ℓ) + 10000 : ℕ) : ℝ) ≤ Rc * (T * p) := by
    push_cast
    have eT : ((2 : ℝ) ^ ℓ) * M = T := by simp [T]
    have e1 : (2 : ℝ) * 2 ^ ℓ * w * M = 2 * T * w := by rw [← eT]; ring
    have e2 : (2 : ℝ) * 2 ^ ℓ * M * (4 * k + 60) = 2 * T * (4 * k + 60) := by rw [← eT]; ring
    have e3 : (2 : ℝ) ^ ℓ * (w + k) * M = T * (w + k) := by rw [← eT]; ring
    rw [e1, e2, e3]
    exact rest_bound hpR hTR (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _) hwp hkR hℓp' hH
      (by exact_mod_cast hrT) (by positivity) hCw0 hCl0 hCH0
  have hall := (Nat.cast_le (α := ℝ)).mpr hrest
  have hsplit : (convExtra p d ℓ K w H M : ℝ) ≤ (pwCost p d ℓ K w H M (2 * 2 ^ ℓ * w * M) : ℝ) + Rc * (T * p) := by
    refine hall.trans ?_
    have := hR
    push_cast at this ⊢
    linarith
  have hCp0 : (0 : ℝ) ≤ Cp := Nat.cast_nonneg _
  have hHT : (H : ℝ) ≤ CH * (T * p) := by
    have : CH * (p : ℝ) ≤ CH * (T * p) := mul_le_mul_of_nonneg_left (by nlinarith only [hTR, hpR]) hCH0
    linarith
  calc (convExtra p d ℓ K w H M : ℝ)
      ≤ Cp * (2 * transformCost P p d ℓ K ts + H) + Rc * (T * p) := by linarith only [hsplit, hpwR]
    _ ≤ (2 * Cp + Cp * CH + Rc) * convolutionCost P p d ℓ K ts := by
        linarith only [mul_le_mul_of_nonneg_left hHT hCp0, mul_le_mul_of_nonneg_left htc_le hCp0,
          mul_le_mul_of_nonneg_left hTp hRc0, mul_le_mul_of_nonneg_left hTp (mul_nonneg hCp0 hCH0)]

/-! ### The convolution target -/

theorem transformCost_nonneg (P : TransformParams) (p d ℓ K : ℕ) (ts : List ℕ) :
    0 ≤ transformCost P p d ℓ K ts := by
  unfold transformCost
  have := Real.rpow_nonneg (Nat.cast_nonneg K) (P.τ - 1)
  have := Real.rpow_nonneg (Nat.cast_nonneg d) P.lam'
  positivity

/-- `prop:synthetic-convolution` from `lem:synthetic-transform-cost`: one fixed program
(forward transforms of both operands, pointwise products by Schönhage–Strassen, the opposite
transform, scaling by `M`) meets the convolution statement whenever fixed programs meet the
transform statement, for parameters with `0 < ε < 1`, `λ' > 0` and positive `a_d`, `a_r`, `b_d`. -/
theorem convolution_of_transform (P : TransformParams) (hε0 : 0 < P.ε) (hε1 : P.ε < 1)
    (hlam : 0 < P.lam') (had : 0 < P.ad) (har : 0 < P.ar) (hbd : 0 < P.bd)
    (hT : transformTarget P) : convolutionTarget P := by
  obtain ⟨p₁, L, t, q₁, q₂, a, Mf, Mo, C, ht, hmeet⟩ := hT
  obtain ⟨p₂, C2, hC2, hcost⟩ := convExtra_le_cost P hε0 hε1 hlam had har hbd
  refine ⟨max p₁ p₂, NB t, _, a, convProg Mf Mo ht, 3 * max C 0 + C2, by unfold NB; omega, ?_⟩
  intro p d ℓ K w ts hp hadm fs gs hfl hgl hfd hgd
  obtain ⟨hMF, hMO⟩ := hmeet p d ℓ K w ts (le_trans (le_max_left _ _) hp) hadm
  obtain ⟨hs, k, hl, hc, hk, hH⟩ := conv_instance Mf Mo ht P L C hadm hMF hMO fs gs hfl hgl hfd hgd
  refine ⟨hs, k, hl, hc, ?_, hH⟩
  have hx := hcost p d ℓ K w ts (le_trans (le_max_right _ _) hp) hadm
  have htc0 := transformCost_nonneg P p d ℓ K ts
  have hconv : convolutionCost P p d ℓ K ts = transformCost P p d ℓ K ts +
      ((2 ^ ℓ * ts.prod : ℕ) : ℝ) * p * (Nat.log 2 (2 ^ ℓ * p) + 1) := rfl
  have hextra : (0 : ℝ) ≤ ((2 ^ ℓ * ts.prod : ℕ) : ℝ) * p * (Nat.log 2 (2 ^ ℓ * p) + 1) := by positivity
  have htc : transformCost P p d ℓ K ts ≤ convolutionCost P p d ℓ K ts := by rw [hconv]; linarith
  have h3 : 3 * C * transformCost P p d ℓ K ts ≤ 3 * max C 0 * convolutionCost P p d ℓ K ts := by
    have a1 : C * transformCost P p d ℓ K ts ≤ max C 0 * transformCost P p d ℓ K ts :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) htc0
    have a2 : max C 0 * transformCost P p d ℓ K ts ≤ max C 0 * convolutionCost P p d ℓ K ts :=
      mul_le_mul_of_nonneg_left htc (le_max_right _ _)
    linarith
  calc (k : ℝ) ≤ 3 * C * transformCost P p d ℓ K ts +
        (convExtra p d ℓ K w (transformHeader p d (2 ^ ℓ) K w ts).length ts.prod : ℕ) := hk
    _ ≤ (3 * max C 0 + C2) * convolutionCost P p d ℓ K ts := by rw [add_mul]; linarith

end IntegerMultBounds.Schoenhage
