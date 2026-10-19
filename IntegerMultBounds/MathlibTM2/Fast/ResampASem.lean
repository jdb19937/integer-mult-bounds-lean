module

public import IntegerMultBounds.MathlibTM2.Fast.CMulStream
public import IntegerMultBounds.Resampling.WindowSum
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Bernstein

/-!
# The numerators of the numeric `Ã` on one line

A line of `s` grid values `u j = N_j / 2^q` (`N_j : GaussianInt`, scale `q`) is resampled to `t`
values by `resampANum s t m (termW p wf)` with integer weights `wf k j = WA k j / 2^p`. Every
retained term `termW p wf u k j = rhoC p (rhoC p (wf k j) u j)` is the grid value at scale `p`
of the truncated product `tdivN q (N_j · WA k j)` (`rsa_rhoC_term`), and the `1/2` of `Ã` moves
the sum to scale `p + 1`.

* `rsaCen s t k = ⌊s k / t⌋` is the window centre of output `k`. For `s < t` it advances by
  `0` or `1` per output, by the carry of `s k mod t + s` (`rsaCen_succ`).
* `rsaExt m N = N.drop (s - m) ++ N ++ N.take m` is the line cyclically extended by `m` records
  on both sides (`m ≤ s`); record `x` of it is `N_{(x - m) mod s}` (`rsaExt_getD`). The window of
  output `k` is the `2m + 1` records from `rsaCen s t k` on.
* `rsaPart q E c wt n = Σ_{i < n} tdivN q (E_{c+i} · wt i)`; `rsaOut q s t n E wt` lists the
  values `rsaPart q E (rsaCen s t k) (wt k) n`, `k < t`; `rsaTabL t n wt` is the table stream,
  rows `k < t`, terms `i < n`.
* `rsaWA s t m WA k i = ⟨WA k (rsaCen s t k - m + i), 0⟩`: the weights of the window of `k` in
  increasing order of `j ∈ truncWindow s t m k`.

**Main statement** (`rsa_resampANum`): for `m ≤ s ≤ t`, `k < t` and `u j = N_{j.val} / 2^q`,
`resampANum s t m (termW p (WA / 2^p)) u k` is `rsaPart q (rsaExt m N) (rsaCen s t k)
(rsaWA s t m WA k) (2 m + 1) / 2^(p+1)`; `rsaOut_resampANum` states it for entry `k` of the
line outputs `rsaOut q s t (2m + 1) (rsaExt m N) (rsaWA s t m WA)` computed by the line machine.
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2.Fast.ResampA

open IntegerMultBounds.NLogN IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.Resampling.WindowSum (termW rhoC_real sum_Icc_eq_range floor_centre)

/-! ### Window centres -/

/-- The window centre `⌊s k / t⌋` of output `k`. -/
def rsaCen (s t k : ℕ) : ℕ := s * k / t

lemma rsaCen_zero (s t : ℕ) : rsaCen s t 0 = 0 := by simp [rsaCen]

lemma rsaCen_lt {s t k : ℕ} (_hst : s ≤ t) (hk : k < t) (hs : 0 < s) : rsaCen s t k < s := by
  unfold rsaCen
  apply Nat.div_lt_of_lt_mul
  calc s * k < s * t := Nat.mul_lt_mul_of_pos_left hk hs
    _ = t * s := Nat.mul_comm _ _

lemma rsaCen_self {s t : ℕ} (ht : 0 < t) : rsaCen s t t = s := by
  unfold rsaCen; exact Nat.mul_div_cancel _ ht

/-- The centre advances by the carry of `s k mod t + s`. -/
lemma rsaCen_succ {s t : ℕ} (hst : s < t) (k : ℕ) :
    rsaCen s t (k + 1) = rsaCen s t k + if t ≤ s * k % t + s then 1 else 0 := by
  have ht : 0 < t := by omega
  unfold rsaCen
  have h1 : s * (k + 1) = t * (s * k / t) + (s * k % t + s) := by
    have := Nat.div_add_mod (s * k) t
    rw [Nat.mul_succ]; omega
  have hr := Nat.mod_lt (s * k) ht
  have h2 : (s * k % t + s) / t = if t ≤ s * k % t + s then 1 else 0 := by
    split_ifs with h
    · exact Nat.div_eq_of_lt_le (by omega) (by omega)
    · exact Nat.div_eq_of_lt (by omega)
  rw [h1, Nat.mul_add_div ht, h2]

lemma rsaCen_succ_mod {s t : ℕ} (k : ℕ) : s * (k + 1) % t = (s * k % t + s) % t := by
  rw [Nat.mul_succ, Nat.add_mod, Nat.add_mod (s * k % t) s t, Nat.mod_mod]

/-! ### Coefficient streams -/

lemma rsa_cstream_take {A w : ℕ} : ∀ (l : List GaussianInt) (k : ℕ),
    (cstream A w l).take (k * w) = cstream A w (l.take k)
  | [], k => by simp
  | x :: l, 0 => by simp
  | x :: l, k + 1 => by
      have hx : (csyms A w x).length = w := by simp [csyms]
      rw [cstream_cons, List.take_append, hx,
        List.take_of_length_le (by rw [hx]; nlinarith),
        show (k + 1) * w - w = k * w by rw [Nat.succ_mul]; omega, rsa_cstream_take l k,
        List.take_succ_cons, cstream_cons]

lemma rsa_cstream_drop {A w : ℕ} : ∀ (l : List GaussianInt) (k : ℕ),
    (cstream A w l).drop (k * w) = cstream A w (l.drop k)
  | [], k => by simp
  | x :: l, 0 => by simp
  | x :: l, k + 1 => by
      have hx : (csyms A w x).length = w := by simp [csyms]
      rw [cstream_cons, List.drop_append, hx,
        List.drop_eq_nil_of_le (by rw [hx]; nlinarith),
        show (k + 1) * w - w = k * w by rw [Nat.succ_mul]; omega, rsa_cstream_drop l k,
        List.drop_succ_cons, List.nil_append]

lemma rsa_cstream_reverse_take {A w : ℕ} (l : List GaussianInt) (k : ℕ) :
    ((cstream A w l).reverse.take (k * w)).reverse = cstream A w (l.drop (l.length - k)) := by
  rw [List.take_reverse, List.reverse_reverse, length_cstream,
    show l.length * w - k * w = (l.length - k) * w by rw [Nat.sub_mul], rsa_cstream_drop]

/-! ### Lists -/

lemma rsa_drop_getD {α : Type} (E : List α) (d : α) {k : ℕ} (hk : k < E.length) :
    E.drop k = E.getD k d :: E.drop (k + 1) := by
  rw [List.drop_eq_getElem_cons hk, List.getD_eq_getElem _ _ hk]

lemma rsa_take_drop_succ {α : Type} (E : List α) (d : α) {e i : ℕ} (h : e + i < E.length) :
    (E.drop e).take (i + 1) = (E.drop e).take i ++ [E.getD (e + i) d] := by
  rw [List.take_add_one, List.getElem?_drop, List.getElem?_eq_getElem h,
    List.getD_eq_getElem _ _ h]
  simp

lemma rsa_take_succ {α : Type} (E : List α) (d : α) {k : ℕ} (h : k < E.length) :
    E.take (k + 1) = E.take k ++ [E.getD k d] := by
  rw [List.take_add_one, List.getElem?_eq_getElem h, List.getD_eq_getElem _ _ h]
  simp

lemma rsa_csyms_zero (A w : ℕ) : csyms A w 0 = List.replicate (1 * w) (pairSym A false false) := by
  simp [csyms, red, coeffSyms, List.ofFn_const]

lemma rsa_getD_mem {α : Type} (E : List α) (d : α) {k : ℕ} (hk : k < E.length) :
    E.getD k d ∈ E := by
  rw [List.getD_eq_getElem _ _ hk]; exact List.getElem_mem hk

/-! ### The cyclic extension -/

/-- The line extended cyclically by `m` records on both sides. -/
def rsaExt (m : ℕ) (N : List GaussianInt) : List GaussianInt :=
  N.drop (N.length - m) ++ N ++ N.take m

lemma length_rsaExt {m : ℕ} {N : List GaussianInt} (hm : m ≤ N.length) :
    (rsaExt m N).length = N.length + 2 * m := by
  simp [rsaExt, hm]; omega

/-- Record `x` of the extension is `N_{(x - m) mod s}`. -/
lemma rsaExt_getD {m : ℕ} {N : List GaussianInt} (hm : m ≤ N.length) {x : ℕ}
    (hx : x < N.length + 2 * m) :
    (rsaExt m N).getD x 0 = N.getD (((x : ℤ) - m) % (N.length : ℤ)).toNat 0 := by
  have hs0 : 0 < N.length := by omega
  unfold rsaExt
  simp only [List.getD_eq_getElem?_getD]
  have hl1 : (N.drop (N.length - m)).length = m := by simp; omega
  have hl2 : (N.drop (N.length - m) ++ N).length = m + N.length := by simp; omega
  by_cases h1 : x < m
  · rw [List.append_assoc, List.getElem?_append_left (by rw [hl1]; omega), List.getElem?_drop]
    have e : (x : ℤ) - m = ((N.length - m + x : ℕ) : ℤ) + (N.length : ℤ) * (-1) := by
      push_cast; omega
    rw [e, Int.add_mul_emod_self_left, Int.emod_eq_of_lt (by omega) (by omega),
      Int.toNat_natCast]
  · by_cases h2 : x < m + N.length
    · rw [List.append_assoc, List.getElem?_append_right (by rw [hl1]; omega), hl1,
        List.getElem?_append_left (by omega)]
      have e : (x : ℤ) - m = ((x - m : ℕ) : ℤ) := by omega
      rw [e, Int.emod_eq_of_lt (by omega) (by omega), Int.toNat_natCast]
    · rw [List.getElem?_append_right (by rw [hl2]; omega), hl2, List.getElem?_take,
        ite_eq_left (by omega)]
      have e : (x : ℤ) - m = ((x - m - N.length : ℕ) : ℤ) + (N.length : ℤ) * 1 := by
        omega
      rw [e, Int.add_mul_emod_self_left, Int.emod_eq_of_lt (by omega) (by omega),
        Int.toNat_natCast]
      congr 2
      omega

/-! ### Line values -/

/-- The first `n` terms of a window at `c`: `Σ_{i < n} tdivN q (E_{c+i} · wt i)`. -/
def rsaPart (q : ℕ) (E : List GaussianInt) (c : ℕ) (wt : ℕ → GaussianInt) (n : ℕ) :
    GaussianInt :=
  ∑ i ∈ Finset.range n, tdivN q (E.getD (c + i) 0 * wt i)

lemma rsaPart_succ (q : ℕ) (E : List GaussianInt) (c : ℕ) (wt : ℕ → GaussianInt) (n : ℕ) :
    rsaPart q E c wt (n + 1) = rsaPart q E c wt n + tdivN q (E.getD (c + n) 0 * wt n) := by
  simp [rsaPart, Finset.sum_range_succ]

/-- The `t` outputs of a line: the window sums at the centres `rsaCen s t k`. -/
def rsaOut (q s t n : ℕ) (E : List GaussianInt) (wt : ℕ → ℕ → GaussianInt) : List GaussianInt :=
  (List.range t).map fun k => rsaPart q E (rsaCen s t k) (wt k) n

/-- The table stream: rows `k < t`, terms `i < n`. -/
def rsaTabL (t n : ℕ) (wt : ℕ → ℕ → GaussianInt) : List GaussianInt :=
  (List.range t).flatMap fun k => (List.range n).map (wt k)

lemma length_rsaTabL (t n : ℕ) (wt : ℕ → ℕ → GaussianInt) : (rsaTabL t n wt).length = t * n := by
  induction t with
  | zero => simp [rsaTabL]
  | succ t ih =>
      simp only [rsaTabL, List.range_succ, List.flatMap_append, List.length_append] at ih ⊢
      rw [ih]; simp [Nat.succ_mul]

lemma rsaTabL_getD (t n : ℕ) (wt : ℕ → ℕ → GaussianInt) {k i : ℕ} (hk : k < t) (hi : i < n) :
    (rsaTabL t n wt).getD (k * n + i) 0 = wt k i := by
  induction t with
  | zero => omega
  | succ t ih =>
      simp only [rsaTabL, List.range_succ, List.flatMap_append] at ih ⊢
      have hl : ((List.range t).flatMap fun k => (List.range n).map (wt k)).length = t * n :=
        length_rsaTabL t n wt
      by_cases hkt : k < t
      · rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by
          rw [hl]; nlinarith), ← List.getD_eq_getElem?_getD]
        exact ih hkt
      · have hk' : k = t := by omega
        subst hk'
        rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by rw [hl]; omega), hl]
        simp [hi]

lemma rsaPart_tab (q : ℕ) (E : List GaussianInt) (e t n : ℕ) (wt : ℕ → ℕ → GaussianInt) {k : ℕ}
    (hk : k < t) :
    rsaPart q E e (fun i => (rsaTabL t n wt).getD (k * n + i) 0) n = rsaPart q E e (wt k) n := by
  unfold rsaPart
  refine Finset.sum_congr rfl fun i hi => ?_
  dsimp only
  rw [rsaTabL_getD t n wt hk (Finset.mem_range.1 hi)]

lemma rsaOut_take_succ (q s t n : ℕ) (E : List GaussianInt) (wt : ℕ → ℕ → GaussianInt) {k : ℕ}
    (hk : k < t) :
    (rsaOut q s t n E wt).take (k + 1) =
      (rsaOut q s t n E wt).take k ++ [rsaPart q E (rsaCen s t k) (wt k) n] := by
  rw [rsa_take_succ _ 0 (by simp [rsaOut]; exact hk)]
  simp [rsaOut, List.getD_eq_getElem?_getD, hk]

/-! ### The weights of `Ã` -/

/-- The weight of term `i` of the window of output `k`: `WA k (⌊s k / t⌋ - m + i)`, real. -/
def rsaWA (s t m : ℕ) (WA : ZMod t → ℤ → ℤ) (k i : ℕ) : GaussianInt :=
  ⟨WA (k : ZMod t) ((rsaCen s t k : ℤ) - m + i), 0⟩

/-- The rounded product of a weight `a / 2^p` and a grid value `N / 2^q`. -/
lemma rsa_rhoC_term (p q : ℕ) (a : ℤ) (N : GaussianInt) :
    rhoC p ((((a : ℝ) / 2 ^ p : ℝ) : ℂ) * (GaussianInt.toComplex N / 2 ^ q)) =
      GaussianInt.toComplex (tdivN q (N * ⟨a, 0⟩)) / 2 ^ p := by
  have hp : (2 : ℝ) ^ p ≠ 0 := by positivity
  rw [two_pow_complex p, two_pow_complex q]
  apply Complex.ext
  · rw [rhoC_re, toComplex_div_re, tdivN_re, tdiv_rho0]
    congr 3
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, toComplex_div_re,
      toComplex_div_im, zero_mul, sub_zero, Zsqrtd.re_mul]
    push_cast
    field_simp
    ring
  · rw [rhoC_im, toComplex_div_im, tdivN_im, tdiv_rho0]
    congr 3
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, toComplex_div_re,
      toComplex_div_im, zero_mul, add_zero, Zsqrtd.im_mul]
    push_cast
    field_simp
    ring

/-- A weight on the grid is unchanged by rounding. -/
lemma rsa_rhoC_weight (p : ℕ) (a : ℤ) :
    rhoC p ((((a : ℝ) / 2 ^ p : ℝ) : ℂ)) = (((a : ℝ) / 2 ^ p : ℝ) : ℂ) := by
  rw [rhoC_real]
  have hp : (2 : ℝ) ^ p ≠ 0 := by positivity
  rw [mul_div_cancel₀ _ hp, rho0_intCast]

/-- **The numerators of `Ã` on one line.** For `m ≤ s ≤ t`, output `k < t` of
`resampANum s t m (termW p (WA / 2^p))` on the grid line `u j = N_{j.val} / 2^q` is the window
sum `rsaPart q (rsaExt m N) (rsaCen s t k) (rsaWA s t m WA k) (2 m + 1)` at scale `2^(p+1)`. -/
theorem rsa_resampANum {s t : ℕ} [NeZero s] [NeZero t] (p q m : ℕ) (WA : ZMod t → ℤ → ℤ)
    (N : List GaussianInt) (hN : N.length = s) (hst : s ≤ t) (hm : m ≤ s) (u : ZMod s → ℂ)
    (hu : ∀ j : ZMod s, u j = GaussianInt.toComplex (N.getD j.val 0) / 2 ^ q) {k : ℕ}
    (hk : k < t) :
    resampANum s t m (termW p fun k j => (WA k j : ℝ) / 2 ^ p) u (k : ZMod t) =
      GaussianInt.toComplex (rsaPart q (rsaExt m N) (rsaCen s t k) (rsaWA s t m WA k)
        (2 * m + 1)) / 2 ^ (p + 1) := by
  have hs0 : 0 < s := Nat.pos_of_ne_zero (NeZero.ne s)
  have hc : rsaCen s t k < s := rsaCen_lt hst hk hs0
  have hfl : ⌊resampCentre s t (k : ZMod t)⌋ = (rsaCen s t k : ℤ) := floor_centre hst k hk
  unfold resampANum truncWindow
  rw [hfl, show (rsaCen s t k : ℤ) + m = (rsaCen s t k : ℤ) - m + ((2 * m : ℕ) : ℤ) by
    push_cast; ring, sum_Icc_eq_range]
  unfold rsaPart
  rw [map_sum, Finset.sum_div, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  simp only [Finset.mem_range] at hi
  unfold termW
  rw [rsa_rhoC_weight]
  have hx : rsaCen s t k + i < N.length + 2 * m := by omega
  have hE := rsaExt_getD (m := m) (N := N) (by omega) hx
  have hidx : ((((rsaCen s t k : ℤ) - m + (i : ℤ) : ℤ) : ZMod s)).val =
      (((((rsaCen s t k + i : ℕ) : ℤ) - m) % (N.length : ℤ))).toNat := by
    have h' : ((((((rsaCen s t k : ℤ) - m + (i : ℤ) : ℤ) : ZMod s)).val : ℕ) : ℤ) =
        (((rsaCen s t k + i : ℕ) : ℤ) - m) % (N.length : ℤ) := by
      rw [ZMod.val_intCast, hN]; push_cast; ring_nf
    rw [← h', Int.toNat_natCast]
  rw [hu, hidx, ← hE, rsa_rhoC_term]
  unfold rsaWA
  rw [pow_succ]
  ring

lemma length_rsaOut (q s t n : ℕ) (E : List GaussianInt) (wt : ℕ → ℕ → GaussianInt) :
    (rsaOut q s t n E wt).length = t := by simp [rsaOut]

lemma rsaOut_getD (q s t n : ℕ) (E : List GaussianInt) (wt : ℕ → ℕ → GaussianInt) {k : ℕ}
    (hk : k < t) :
    (rsaOut q s t n E wt).getD k 0 = rsaPart q E (rsaCen s t k) (wt k) n := by
  simp [rsaOut, List.getD_eq_getElem?_getD, hk]

/-- **The line outputs are the numerators of `Ã`.** Output `k < t` of the line machine on the
grid line `u j = N_{j.val} / 2^q` with the weights `rsaWA s t m WA` is the numerator at scale
`2^(p+1)` of `resampANum s t m (termW p (WA / 2^p)) u k`. -/
theorem rsaOut_resampANum {s t : ℕ} [NeZero s] [NeZero t] (p q m : ℕ) (WA : ZMod t → ℤ → ℤ)
    (N : List GaussianInt) (hN : N.length = s) (hst : s ≤ t) (hm : m ≤ s) (u : ZMod s → ℂ)
    (hu : ∀ j : ZMod s, u j = GaussianInt.toComplex (N.getD j.val 0) / 2 ^ q) {k : ℕ}
    (hk : k < t) :
    resampANum s t m (termW p fun k j => (WA k j : ℝ) / 2 ^ p) u (k : ZMod t) =
      GaussianInt.toComplex ((rsaOut q s t (2 * m + 1) (rsaExt m N) (rsaWA s t m WA)).getD k 0) /
        2 ^ (p + 1) := by
  rw [rsaOut_getD _ _ _ _ _ _ hk, rsa_resampANum p q m WA N hN hst hm u hu hk]

end IntegerMultBounds.MathlibTM2.Fast.ResampA
