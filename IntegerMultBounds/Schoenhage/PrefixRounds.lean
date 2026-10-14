module

public import IntegerMultBounds.Schoenhage.DifOppositeRounds

/-! The arithmetic width of the rounds on prefix slots. Such a round applies
its butterflies one bit at a time without truncation, completes the monomial
exactly and rounds once (`roundArr p` of the exact round, as in
`compSchedule_close` and `compOppSchedule_close`, which round after every
slot round of either kind). Starting from a disk array on the `2^(-p)` grid,
after `s` butterflies every coefficient is a dyadic on the `2^(-(p+s))` grid
and still lies in the disk (`bflys_grid`, `bflys_width`), monomials keep the
grid and the disk (`twist_grid`, `untwist_grid`), so every numerator has
modulus at most `2^(p+s)` with `s ≤ D`: `p + D + O(1)` bits per component
suffice (`slotRound_width`, `oppSlotRound_width`). -/

@[expose] public section

namespace IntegerMultBounds.Schoenhage

open Spec.SignedRingProduct NLogN

/-! ### Dyadic grids -/

/-- `u` lies on the `2^(-m)` grid. -/
def OnGrid (m : ℕ) (u : ℂ) : Prop := ∃ a b : ℤ, u = ⟨(a : ℝ) / 2 ^ m, (b : ℝ) / 2 ^ m⟩

theorem onGrid_iff (m : ℕ) (u : ℂ) :
    OnGrid m u ↔ ∃ a b : ℤ, u.re = (a : ℝ) / 2 ^ m ∧ u.im = (b : ℝ) / 2 ^ m := by
  constructor
  · rintro ⟨a, b, rfl⟩; exact ⟨a, b, rfl, rfl⟩
  · rintro ⟨a, b, ha, hb⟩; exact ⟨a, b, Complex.ext ha hb⟩

theorem onGrid_half_add {m : ℕ} {u v : ℂ} (hu : OnGrid m u) (hv : OnGrid m v) :
    OnGrid (m + 1) ((1 / 2 : ℂ) • (u + v)) := by
  obtain ⟨a, b, rfl⟩ := hu
  obtain ⟨c, e, rfl⟩ := hv
  refine (onGrid_iff _ _).mpr ⟨a + c, b + e, ?_, ?_⟩ <;>
    simp [smul_eq_mul, Complex.mul_re, Complex.mul_im, pow_succ] <;> field_simp

theorem onGrid_half_sub {m : ℕ} {u v : ℂ} (hu : OnGrid m u) (hv : OnGrid m v) :
    OnGrid (m + 1) ((1 / 2 : ℂ) • (u - v)) := by
  obtain ⟨a, b, rfl⟩ := hu
  obtain ⟨c, e, rfl⟩ := hv
  refine (onGrid_iff _ _).mpr ⟨a - c, b - e, ?_, ?_⟩ <;>
    simp [smul_eq_mul, Complex.mul_re, Complex.mul_im, pow_succ] <;> field_simp

theorem onGrid_neg_one_pow_mul {m : ℕ} {u : ℂ} (hu : OnGrid m u) (e : ℕ) :
    OnGrid m ((-1 : ℂ) ^ e * u) := by
  obtain ⟨a, b, rfl⟩ := hu
  rcases neg_one_pow_eq_or ℂ e with h | h <;> rw [h]
  · rw [one_mul]; exact ⟨a, b, rfl⟩
  · refine (onGrid_iff _ _).mpr ⟨-a, -b, ?_, ?_⟩ <;> simp [neg_div]

theorem onGrid_rhoC (p : ℕ) (u : ℂ) : OnGrid p (rhoC p u) := ⟨_, _, rfl⟩

/-- Numerators of a disk point on the `2^(-m)` grid have modulus at most `2^m`. -/
theorem onGrid_numerators {m : ℕ} {u : ℂ} (hu : OnGrid m u) (hd : ‖u‖ ≤ 1) :
    ∃ a b : ℤ, u = ⟨(a : ℝ) / 2 ^ m, (b : ℝ) / 2 ^ m⟩ ∧ |a| ≤ 2 ^ m ∧ |b| ≤ 2 ^ m := by
  obtain ⟨a, b, rfl⟩ := hu
  refine ⟨a, b, rfl, ?_, ?_⟩
  · have h1 := Complex.abs_re_le_norm (⟨(a : ℝ) / 2 ^ m, (b : ℝ) / 2 ^ m⟩ : ℂ)
    have h2 : |(a : ℝ) / 2 ^ m| ≤ 1 := h1.trans hd
    rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ m), div_le_one (by positivity)] at h2
    exact_mod_cast h2
  · have h1 := Complex.abs_im_le_norm (⟨(a : ℝ) / 2 ^ m, (b : ℝ) / 2 ^ m⟩ : ℂ)
    have h2 : |(b : ℝ) / 2 ^ m| ≤ 1 := h1.trans hd
    rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ m), div_le_one (by positivity)] at h2
    exact_mod_cast h2

variable {r : ℕ}

/-- Every coefficient of the array lies on the `2^(-m)` grid. -/
def GridArr (m : ℕ) (w : ℕ → Fin r → ℂ) : Prop := ∀ y k, OnGrid m (w y k)

theorem gridArr_roundArr (p : ℕ) (w : ℕ → Fin r → ℂ) : GridArr p (roundArr p w) :=
  fun _ _ => onGrid_rhoC p _

/-! ### Butterflies and monomials on the grid -/

theorem bfly_grid {m : ℕ} (P : ℕ) {w : ℕ → Fin r → ℂ} (hw : GridArr m w) :
    GridArr (m + 1) (bfly P w) := by
  intro y k
  unfold bfly
  split_ifs
  · simpa [Pi.smul_apply, Pi.add_apply] using onGrid_half_add (hw y k) (hw (y + 2 ^ P) k)
  · simpa [Pi.smul_apply, Pi.sub_apply] using onGrid_half_sub (hw (y - 2 ^ P) k) (hw y k)

/-- `s` butterflies move an array from the `2^(-m)` grid to the `2^(-(m+s))` grid. -/
theorem bflys_grid : ∀ (Ps : List ℕ) {m : ℕ} {w : ℕ → Fin r → ℂ}, GridArr m w →
    GridArr (m + Ps.length) (bflys Ps w)
  | [], m, w, hw => by simpa [bflys, run] using hw
  | P :: Ps, m, w, hw => by
    have := bflys_grid Ps (bfly_grid P hw)
    simp only [List.length_cons]
    rw [show m + (Ps.length + 1) = m + 1 + Ps.length by ring]
    exact this

variable [NeZero r]

theorem twist_grid {m : ℕ} (f : ℕ → ℕ) {w : ℕ → Fin r → ℂ} (hw : GridArr m w) :
    GridArr m (twist f w) := by
  intro y k
  obtain ⟨e, j, h⟩ := shiftInv_apply (f y) (w y) k
  simp only [twist, h]
  exact onGrid_neg_one_pow_mul (hw y j) e

theorem untwist_grid {m : ℕ} (f : ℕ → ℕ) {w : ℕ → Fin r → ℂ} (hw : GridArr m w) :
    GridArr m (untwist f w) := by
  intro y k
  simp only [untwist, shiftNegZ_apply]
  exact onGrid_neg_one_pow_mul (hw y _) _

/-! ### Width of the prefix rounds -/

omit [NeZero r] in
/-- After the butterflies on bits below `n`, a disk array on the `2^(-m)` grid has its records below
`2^n` on the `2^(-(m+s))` grid with numerators of modulus at most `2^(m+s)`, `s` the number of
butterflies. -/
theorem bflys_width {n m : ℕ} (Ps : List ℕ) (hPs : ∀ P ∈ Ps, P < n) {w : ℕ → Fin r → ℂ}
    (hw : GridArr m w) (hd : ∀ y < 2 ^ n, ∀ k, ‖w y k‖ ≤ 1) :
    ∀ y < 2 ^ n, ∀ k, ∃ a b : ℤ, bflys Ps w y k = ⟨(a : ℝ) / 2 ^ (m + Ps.length), (b : ℝ) / 2 ^ (m + Ps.length)⟩ ∧
      |a| ≤ 2 ^ (m + Ps.length) ∧ |b| ≤ 2 ^ (m + Ps.length) := by
  intro y hy k
  have hdisk := run_contracts (Ps.map bfly) (fun G hG => by
    simp only [List.mem_map] at hG
    obtain ⟨P, hP, rfl⟩ := hG
    exact bfly_contracts (hPs P hP)) w 1 hd y hy k
  exact onGrid_numerators (bflys_grid Ps hw y k) hdisk

omit [NeZero r] in
theorem slotBits_lt {ts : List ℕ} (hts : PowAxes r ts) {n : ℕ} (hn : ts.prod = 2 ^ n)
    (π : BitPerm n) (h : ℕ) : ∀ P ∈ slotBits π ts (slotAxes ts h) h, P < n := by
  have hlog : Nat.log 2 ts.prod = n := by rw [hn, Nat.log_pow (by norm_num)]
  intro P hP
  simp only [slotBits, slotAxes, List.mem_map, List.mem_filter, List.mem_range, decide_eq_true_eq] at hP
  obtain ⟨i, ⟨hi, hih⟩, rfl⟩ := hP
  have := axOff_add_len_le hts hi
  exact π.σ_lt _ (by omega)

omit [NeZero r] in
theorem slotAxes_length_le (ts : List ℕ) (h : ℕ) : (slotAxes ts h).length ≤ ts.length := by
  unfold slotAxes
  exact (List.length_filter_le _ _).trans (by simp)

/-- `slotRound_width`: evaluated exactly, a forward slot round of a disk array on the `2^(-p)`
grid leaves every coefficient of its records below `2^n` on the `2^(-(p+s))` grid, `s ≤ D` its
number of axes, with numerators of modulus at most `2^(p+s)`; rounding it once is the computed
round. -/
theorem slotRound_width {ts : List ℕ} (hts : PowAxes r ts) {n : ℕ} (hn : ts.prod = 2 ^ n)
    (π : BitPerm n) (h p : ℕ) {w : ℕ → Fin r → ℂ} (hw : GridArr p w)
    (hd : ∀ y < 2 ^ n, ∀ k, ‖w y k‖ ≤ 1) :
    (slotAxes ts h).length ≤ ts.length ∧
    ∀ y < 2 ^ n, ∀ k, ∃ a b : ℤ,
      slotRound π ts h w y k =
        ⟨(a : ℝ) / 2 ^ (p + (slotAxes ts h).length), (b : ℝ) / 2 ^ (p + (slotAxes ts h).length)⟩ ∧
      |a| ≤ 2 ^ (p + (slotAxes ts h).length) ∧ |b| ≤ 2 ^ (p + (slotAxes ts h).length) := by
  refine ⟨slotAxes_length_le ts h, fun y hy k => ?_⟩
  have hlen : (slotBits π ts (slotAxes ts h) h).length = (slotAxes ts h).length := by simp [slotBits]
  have hgrid : GridArr (p + (slotAxes ts h).length) (slotRound π ts h w) := by
    unfold slotRound
    have := twist_grid (slotExp π r ts (slotAxes ts h) h) (bflys_grid (slotBits π ts (slotAxes ts h) h) hw)
    rwa [hlen] at this
  exact onGrid_numerators (hgrid y k) ((slotRound_contracts hts hn π h).1 w 1 hd y hy k)

/-- `oppSlotRound_width`: the same for an opposite slot round, whose inverse monomial comes first
and keeps the `2^(-p)` grid and the disk. -/
theorem oppSlotRound_width {ts : List ℕ} (hts : PowAxes r ts) {n : ℕ} (hn : ts.prod = 2 ^ n)
    (π : BitPerm n) (h p : ℕ) {w : ℕ → Fin r → ℂ} (hw : GridArr p w)
    (hd : ∀ y < 2 ^ n, ∀ k, ‖w y k‖ ≤ 1) :
    (slotAxes ts h).length ≤ ts.length ∧
    ∀ y < 2 ^ n, ∀ k, ∃ a b : ℤ,
      oppSlotRound π ts h w y k =
        ⟨(a : ℝ) / 2 ^ (p + (slotAxes ts h).length), (b : ℝ) / 2 ^ (p + (slotAxes ts h).length)⟩ ∧
      |a| ≤ 2 ^ (p + (slotAxes ts h).length) ∧ |b| ≤ 2 ^ (p + (slotAxes ts h).length) := by
  refine ⟨slotAxes_length_le ts h, fun y hy k => ?_⟩
  have hlen : (slotBits π ts (slotAxes ts h) h).length = (slotAxes ts h).length := by simp [slotBits]
  have := bflys_width (slotBits π ts (slotAxes ts h) h) (slotBits_lt hts hn π h)
    (untwist_grid (slotExp π r ts (slotAxes ts h) h) hw)
    (fun y hy k => untwist_contracts n _ w 1 hd y hy k) y hy k
  rw [hlen] at this
  exact this

end IntegerMultBounds.Schoenhage
