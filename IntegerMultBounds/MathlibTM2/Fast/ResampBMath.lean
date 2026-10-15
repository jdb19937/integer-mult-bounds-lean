module

public import IntegerMultBounds.MathlibTM2.Mult.FastB0
public import IntegerMultBounds.MathlibTM2.Fast.CMulArith
public import IntegerMultBounds.Resampling.RowSelect

/-!
# Integer numerators of the fast `B̃₀` on one line

`Mult.FastB0.resampB₀NumK p K m ef df` with integer tables `ef ℓ h = E ℓ h / 2^p`,
`df ℓ = D ℓ / 2^p`, applied to a grid array `w j = N j / 2^p`, is again a grid array. Its
numerators `rsbLineNum p K m E D N` are computed by exact Gaussian-integer operations:

* `rsbHalf N ℓ = tdivN 1 (N (rowIndex s t ℓ))`: row selection and the halving
  `rdV p ((1/2) • ·)`, truncating each part of the numerator toward zero;
* `rsbStep p m E H V ℓ = H ℓ - ∑_{h ∈ rsbHs m} tdivN p (V (ℓ + h) · E ℓ h)`: one rounded
  Horner step `v ↦ rdV p (v₀ - Ẽ v)`, the window `rsbHs m = [-m, …, -1, 1, …, m]` in increasing
  order, the index `ℓ + h` taken in `ZMod s`;
* `rsbIter p m E H k`: `k` steps from `H`;
* `rsbLineNum p K m E D N ℓ = tdivN p (rsbIter p m E (rsbHalf N) K ℓ · D ℓ)`: the diagonal.

`rsb_resampB₀NumK`: `resampB₀NumK p K m (E/2^p) (D/2^p) (N/2^p) = rsbLineNum … / 2^p`, exactly;
`rsbLineNum_eq_numer`: `rsbLineNum` is the numerator `numer p` of `resampB₀NumK`.

`rsb_iter_ball`: every Horner iterate on an input of norm at most one has norm at most one.

`rsbMask s t`: bit `j < t` says whether `j = rowIndexNat s t ℓ` for some `ℓ < s`;
`rsb_filter_mask`: the selected entries of a line of length `t`, in increasing order, are the
entries at `rowIndex s t ℓ`, `ℓ = 0, …, s - 1`.
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2.Fast

open IntegerMultBounds IntegerMultBounds.NLogN
open IntegerMultBounds.Resampling.OffDiagSum (offTermW)
open IntegerMultBounds.Resampling.TabledMaps (diagW)

noncomputable section

/-- The grid value `N / 2^p`. -/
def rsbGrid (p : ℕ) (N : GaussianInt) : ℂ := GaussianInt.toComplex N / 2 ^ p

/-- The real Gaussian integer `x + 0 i`. -/
def rsbReal (x : ℤ) : GaussianInt := ⟨x, 0⟩

/-- The off-diagonal window offsets `-m, …, -1, 1, …, m`, in increasing order. -/
def rsbHs (m : ℕ) : List ℤ :=
  (List.range m).map (fun i : ℕ => (i : ℤ) - m) ++ (List.range m).map (fun i : ℕ => (i : ℤ) + 1)

lemma length_rsbHs (m : ℕ) : (rsbHs m).length = 2 * m := by
  simp [rsbHs]; ring

lemma mem_rsbHs {m : ℕ} {h : ℤ} : h ∈ rsbHs m ↔ h ≠ 0 ∧ h.natAbs ≤ m := by
  simp only [rsbHs, List.mem_append, List.mem_map, List.mem_range]
  constructor
  · rintro (⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩) <;> omega
  · rintro ⟨h0, hm⟩
    rcases lt_or_gt_of_ne h0 with hneg | hpos
    · left; exact ⟨(h + m).toNat, by omega, by omega⟩
    · right; exact ⟨(h - 1).toNat, by omega, by omega⟩

lemma rsbHs_nodup (m : ℕ) : (rsbHs m).Nodup := by
  unfold rsbHs
  rw [List.nodup_append]
  refine ⟨(List.nodup_range).map (fun a b h => by simpa using h),
    (List.nodup_range).map (fun a b h => by simpa using h), ?_⟩
  intro x hx y hy
  simp only [List.mem_map, List.mem_range] at hx hy
  obtain ⟨i, hi, rfl⟩ := hx
  obtain ⟨j, hj, rfl⟩ := hy
  omega

lemma rsbHs_toFinset (m : ℕ) : (rsbHs m).toFinset = offDiagWindow m := by
  ext h
  rw [List.mem_toFinset, mem_rsbHs, mem_offDiagWindow]

lemma sum_offDiagWindow_rsbHs {M : Type*} [AddCommMonoid M] (m : ℕ) (f : ℤ → M) :
    ∑ h ∈ offDiagWindow m, f h = ((rsbHs m).map f).sum := by
  rw [← rsbHs_toFinset, List.sum_toFinset _ (rsbHs_nodup m)]

/-! ### Grid values -/

lemma rsbGrid_add (p : ℕ) (a b : GaussianInt) : rsbGrid p (a + b) = rsbGrid p a + rsbGrid p b := by
  simp [rsbGrid, add_div]

lemma rsbGrid_sub (p : ℕ) (a b : GaussianInt) : rsbGrid p (a - b) = rsbGrid p a - rsbGrid p b := by
  simp [rsbGrid, sub_div]

lemma rsbGrid_zero (p : ℕ) : rsbGrid p 0 = 0 := by simp [rsbGrid]

lemma rsbGrid_list_sum (p : ℕ) (l : List GaussianInt) :
    rsbGrid p l.sum = (l.map (rsbGrid p)).sum := by
  induction l with
  | nil => simp [rsbGrid_zero]
  | cons a l ih => simp [rsbGrid_add, ih]

/-- `rhoC p` fixes grid values. -/
lemma rhoC_rsbGrid (p : ℕ) (N : GaussianInt) : rhoC p (rsbGrid p N) = rsbGrid p N := by
  rw [rhoC_eq_numer, rsbGrid, numer_grid]

lemma rsbGrid_real (p : ℕ) (x : ℤ) : (((x : ℝ) / 2 ^ p : ℝ) : ℂ) = rsbGrid p (rsbReal x) := by
  apply Complex.ext
  · rw [Complex.ofReal_re, rsbGrid, two_pow_complex, toComplex_div_re]
    simp [rsbReal]
  · rw [Complex.ofReal_im, rsbGrid, two_pow_complex, toComplex_div_im]
    simp [rsbReal]

/-- The rounded product of two grid values. -/
lemma rhoC_mul_rsbGrid (p : ℕ) (a b : GaussianInt) :
    rhoC p (rsbGrid p a * rsbGrid p b) = rsbGrid p (tdivN p (a * b)) :=
  rhoC_mul_grid p a b

/-- The rounded half of a grid value. -/
lemma rhoC_half_rsbGrid (p : ℕ) (N : GaussianInt) :
    rhoC p ((1 / 2 : ℂ) * rsbGrid p N) = rsbGrid p (tdivN 1 N) := by
  have hpos : (2 : ℝ) ^ p ≠ 0 := by positivity
  apply Complex.ext
  · rw [rhoC_re, rsbGrid, rsbGrid, two_pow_complex, toComplex_div_re, tdivN_re, tdiv_rho0]
    simp only [Complex.mul_re, Complex.div_ofReal_re, Complex.div_ofReal_im, one_div,
      Complex.inv_re, Complex.inv_im, Complex.normSq_ofNat]
    rw [← GaussianInt.intCast_re, ← GaussianInt.intCast_im]
    congr 2
    norm_num
    field_simp
  · rw [rhoC_im, rsbGrid, rsbGrid, two_pow_complex, toComplex_div_im, tdivN_im, tdiv_rho0]
    simp only [Complex.mul_im, Complex.div_ofReal_re, Complex.div_ofReal_im, one_div,
      Complex.inv_re, Complex.inv_im, Complex.normSq_ofNat]
    rw [← GaussianInt.intCast_re, ← GaussianInt.intCast_im]
    congr 2
    norm_num
    field_simp

/-! ### The integer line map -/

variable {s t : ℕ} [NeZero s] [NeZero t]

/-- Row selection and halving: `tdivN 1 (N (rowIndex s t ℓ))`. -/
def rsbHalf (N : ZMod t → GaussianInt) : ZMod s → GaussianInt :=
  fun ℓ => tdivN 1 (N (rowIndex s t ℓ))

/-- One integer Horner step `V ↦ H - Ẽ V`. -/
def rsbStep (p m : ℕ) (E : ZMod s → ℤ → ℤ) (H V : ZMod s → GaussianInt) : ZMod s → GaussianInt :=
  fun ℓ => H ℓ - ((rsbHs m).map fun h : ℤ => tdivN p (V (ℓ + (h : ZMod s)) * rsbReal (E ℓ h))).sum

/-- `k` integer Horner steps from `H`. -/
def rsbIter (p m : ℕ) (E : ZMod s → ℤ → ℤ) (H : ZMod s → GaussianInt) :
    ℕ → ZMod s → GaussianInt
  | 0 => H
  | k + 1 => rsbStep p m E H (rsbIter p m E H k)

/-- The numerators of `B̃₀` on one line. -/
def rsbLineNum (p K m : ℕ) (E : ZMod s → ℤ → ℤ) (D : ZMod s → ℤ) (N : ZMod t → GaussianInt) :
    ZMod s → GaussianInt :=
  fun ℓ => tdivN p (rsbIter p m E (rsbHalf N) K ℓ * rsbReal (D ℓ))

omit [NeZero s] in
/-- The off-diagonal map with integer weights on a grid array. -/
lemma offDiagNum_rsbGrid (p m : ℕ) (E : ZMod s → ℤ → ℤ) (V : ZMod s → GaussianInt) :
    offDiagNum m (offTermW p fun ℓ h => (E ℓ h : ℝ) / 2 ^ p) (fun j => rsbGrid p (V j)) =
      fun ℓ => rsbGrid p (((rsbHs m).map fun h : ℤ =>
        tdivN p (V (ℓ + (h : ZMod s)) * rsbReal (E ℓ h))).sum) := by
  funext ℓ
  unfold offDiagNum
  rw [sum_offDiagWindow_rsbHs, rsbGrid_list_sum, List.map_map]
  congr 1
  apply List.map_congr_left
  intro h _
  simp only [Function.comp_apply, offTermW]
  rw [rsbGrid_real, rhoC_rsbGrid, rhoC_mul_rsbGrid, mul_comm (rsbReal _)]

/-- The rounded Horner iteration on grid arrays. -/
lemma hornerNeumannR_rsbGrid (p m : ℕ) (E : ZMod s → ℤ → ℤ) (H : ZMod s → GaussianInt) :
    ∀ k, hornerNeumannR (rdV p) (offDiagNum m (offTermW p fun ℓ h => (E ℓ h : ℝ) / 2 ^ p))
        (fun j => rsbGrid p (H j)) k = fun ℓ => rsbGrid p (rsbIter p m E H k ℓ)
  | 0 => rfl
  | k + 1 => by
      rw [hornerNeumannR, hornerNeumannR_rsbGrid p m E H k, offDiagNum_rsbGrid]
      funext ℓ
      simp only [rdV, Pi.sub_apply]
      rw [← rsbGrid_sub, rhoC_rsbGrid]
      rfl

omit [NeZero t] in
/-- **The fast `B̃₀` on integer data.** With integer tables `E`, `D` at scale `2^p` and a grid
input `N / 2^p`, the output of `resampB₀NumK` is the grid array of `rsbLineNum`. -/
theorem rsb_resampB₀NumK (p K m : ℕ) (E : ZMod s → ℤ → ℤ) (D : ZMod s → ℤ)
    (N : ZMod t → GaussianInt) :
    Mult.FastB0.resampB₀NumK p K m (fun ℓ h => (E ℓ h : ℝ) / 2 ^ p) (fun ℓ => (D ℓ : ℝ) / 2 ^ p)
        (fun j => rsbGrid p (N j)) = fun ℓ => rsbGrid p (rsbLineNum p K m E D N ℓ) := by
  have hv : rdV p ((1 / 2 : ℂ) • rowSelect s t (fun j => rsbGrid p (N j))) =
      fun ℓ => rsbGrid p (rsbHalf N ℓ) := by
    funext ℓ
    simp only [rdV, Pi.smul_apply, smul_eq_mul, rowSelect]
    rw [rhoC_half_rsbGrid]
    rfl
  unfold Mult.FastB0.resampB₀NumK Mult.FastB0.resampJNumK
  rw [hv, hornerNeumannR_rsbGrid]
  funext ℓ
  simp only [diagW]
  rw [rsbGrid_real, rhoC_rsbGrid, rhoC_mul_rsbGrid, mul_comm (rsbReal _)]
  rfl

omit [NeZero t] in
/-- The numerators of `B̃₀` on one line are the `rsbLineNum`. -/
theorem rsbLineNum_eq_numer (p K m : ℕ) (E : ZMod s → ℤ → ℤ) (D : ZMod s → ℤ)
    (N : ZMod t → GaussianInt) (ℓ : ZMod s) :
    rsbLineNum p K m E D N ℓ = numer p (Mult.FastB0.resampB₀NumK p K m
      (fun ℓ h => (E ℓ h : ℝ) / 2 ^ p) (fun ℓ => (D ℓ : ℝ) / 2 ^ p)
      (fun j => rsbGrid p (N j)) ℓ) := by
  rw [rsb_resampB₀NumK]
  exact (numer_grid p _).symm

/-! ### The selection mask -/

/-- Bit `j < t`: `j` is the row index of some `ℓ < s`. -/
def rsbMask (s t : ℕ) : List Bool :=
  (List.range t).map fun j : ℕ => decide (∃ ℓ < s, Resampling.RowSelect.q s t ℓ = j)

omit [NeZero s] [NeZero t] in
lemma length_rsbMask (s t : ℕ) : (rsbMask s t).length = t := by simp [rsbMask]

omit [NeZero t] in
/-- `rowIndex` as a natural number. -/
lemma rowIndex_val_q (hst : s < t) (ℓ : ℕ) (hℓ : ℓ < s) :
    (rowIndex s t (ℓ : ZMod s)).val = Resampling.RowSelect.q s t ℓ := by
  rw [rowIndex_val s t hst, Resampling.RowSelect.rowIndexNat_eq s t ℓ
    (Nat.pos_of_ne_zero (NeZero.ne s)) hℓ]

/-- The array `V` as the list of its entries `0, …, n - 1`. -/
def rsbArr {n : ℕ} {α : Type*} (V : ZMod n → α) : List α :=
  (List.range n).map fun i : ℕ => V (i : ZMod n)

omit [NeZero s] [NeZero t] in
lemma length_rsbArr {n : ℕ} {α : Type*} (V : ZMod n → α) : (rsbArr V).length = n := by
  simp [rsbArr]

omit [NeZero t] in
/-- The selected entries of a line are the row-selected ones. -/
theorem rsb_filter_mask (hst : s < t) {α : Type*} (N : ZMod t → α) :
    (((rsbArr N).zip (rsbMask s t)).filter (·.2)).map (·.1) =
      rsbArr fun ℓ : ZMod s => N (rowIndex s t ℓ) := by
  have hs : 0 < s := Nat.pos_of_ne_zero (NeZero.ne s)
  have hz : (rsbArr N).zip (rsbMask s t) =
      (List.range t).map fun j : ℕ =>
        (N (j : ZMod t), decide (∃ ℓ < s, Resampling.RowSelect.q s t ℓ = j)) := by
    apply List.ext_getElem (by simp [rsbArr, rsbMask])
    intro i h1 h2
    simp [rsbArr, rsbMask]
  rw [hz, List.filter_map, List.map_map]
  have hf := Resampling.RowSelect.filter_range_eq_map (Resampling.RowSelect.q s t) s t
    (fun j k hjk _ => Resampling.RowSelect.q_strictMono s t j k hs hst hjk)
    (fun j hj => Resampling.RowSelect.q_lt s t j hs hst hj)
  have e : ((fun x : α × Bool => x.2) ∘ fun j : ℕ =>
      (N (j : ZMod t), decide (∃ ℓ < s, Resampling.RowSelect.q s t ℓ = j))) =
      fun j : ℕ => decide (∃ ℓ < s, Resampling.RowSelect.q s t ℓ = j) := rfl
  rw [e, hf, List.map_map, rsbArr]
  apply List.map_congr_left
  intro ℓ hℓ
  rw [List.mem_range] at hℓ
  simp only [Function.comp_apply, rowIndex]
  rw [Resampling.RowSelect.rowIndexNat_eq s t ℓ hs hℓ]

/-! ### The Horner iterates stay in the unit disk -/

section Ball

variable {s t : ℕ} [NeZero s] [NeZero t] {α : ℝ}

/-- Every rounded Horner iterate of `B̃₀` on an input of norm at most one has norm at most one,
under the window and room conditions of `FastB0.resampB₀NumK_spec` (no condition on the number
of steps). -/
theorem rsb_iter_ball (hst : s < t) (hα : 0 < α) (hθ : 1 ≤ α ^ 2 * ((t : ℝ) / s - 1)) {p m : ℕ}
    (hm : (p : ℝ) ≤ 4 * α ^ 2 * (m : ℝ) ^ 2) (hp : 13 ≤ p) (hmp : 3 * m ≤ p)
    (ef : ZMod s → ℤ → ℝ)
    (hef : ∀ ℓ h, 2 ^ p * ‖rhoC p (ef ℓ h : ℂ) - (Real.exp (normExp s t α ℓ.val h) : ℂ)‖ ≤ 2)
    (w : ZMod t → ℂ) (hw : ‖w‖ ≤ 1) (k : ℕ) :
    ‖hornerNeumannR (rdV p) (offDiagNum m (offTermW p ef))
      (rdV p ((1 / 2 : ℂ) • rowSelect s t w)) k‖ ≤ 1 := by
  obtain ⟨hroom, -⟩ := Mult.FastB0.room_and_budget hp hmp
  have hE := opNorm_offDiagCLM_le_unit hst hα hθ
  have hv1 : ‖rowSelect s t w‖ ≤ 1 := (norm_rowSelect_le _).trans hw
  have hhalf : ‖(1 / 2 : ℂ) • rowSelect s t w‖ ≤ 1 / 2 := by
    rw [norm_smul, norm_div, norm_one, RCLike.norm_two]; linarith
  have hv0b : ‖rdV p ((1 / 2 : ℂ) • rowSelect s t w)‖ ≤ 1 / 2 := (norm_rdV_le p _).trans hhalf
  exact (hornerNeumannR_err_unit hE (Mult.FastB0.offDiagW_err_alpha hst hα hθ hm ef hef) hroom
    (norm_rdV_sub_le p) (norm_rdV_le p) hv0b k).1

omit [NeZero s] [NeZero t] in
/-- The row selection and halving of a grid line is the grid line of `rsbHalf`. -/
lemma rsb_half_grid (p : ℕ) (N : ZMod t → GaussianInt) :
    rdV p ((1 / 2 : ℂ) • rowSelect s t (fun j => rsbGrid p (N j))) =
      fun ℓ => rsbGrid p (rsbHalf N ℓ) := by
  funext ℓ
  simp only [rdV, Pi.smul_apply, smul_eq_mul, rowSelect]
  rw [rhoC_half_rsbGrid]
  rfl

end Ball

end

end IntegerMultBounds.MathlibTM2.Fast
