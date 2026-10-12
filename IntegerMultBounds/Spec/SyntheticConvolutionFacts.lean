module

public import IntegerMultBounds.Spec.SyntheticConvolution
public import IntegerMultBounds.Spec.SyntheticTransformFacts

/-! The convolution theorem behind `prop:synthetic-convolution`: the opposite
transform of the pointwise product of two forward transforms is `M⁻²` times the
cyclic convolution over the record addresses (`oppT_mul_fwdT`), in every
stored layout (`oppExact_pointwise`). With forward and opposite transforms
within `√2 ℓ 2^(-p)` and the rounded products `Q_p(fg/r)` between them, `M`
times the result is within `√2 M (3ℓ + 1) 2^(-p)` of `ℳ_r(f, g)`
(`conv_error`). -/

@[expose] public section

namespace IntegerMultBounds.Spec.SignedRingProduct

open NLogN

variable {r : ℕ} [NeZero r]

/-! ### The convolution theorem -/

theorem negacyclicMul_shift_shift (a b : ℕ) (u v : Fin r → ℂ) :
    negacyclicMul (shiftNegZ a u) (shiftNegZ b v) = shiftNegZ (a + b) (negacyclicMul u v) := by
  calc negacyclicMul (shiftNegZ a u) (shiftNegZ b v)
      = shiftNegZ a (negacyclicMul u (shiftNegZ b v)) := (shiftNegZ_negacyclicMul a u _).symm
    _ = shiftNegZ a (negacyclicMul (shiftNegZ b v) u) := by rw [negacyclicMul_comm u]
    _ = shiftNegZ a (shiftNegZ b (negacyclicMul v u)) := by rw [shiftNegZ_negacyclicMul b v u]
    _ = shiftNegZ (a + b) (negacyclicMul u v) := by rw [shiftNegZ_add, negacyclicMul_comm v]

/-- Adding the inverse exponent of an axis address subtracts its digits. -/
theorem exp_step {ts : List ℕ} (h : PowAxes r ts) (D : ℕ → ℕ) (j m : ℕ) :
    axisExp r ts D j + (2 * r - synthExpL r ts j m % (2 * r)) % (2 * r) ≡
      axisExp r ts (fun i => D i + (ts.getD i 1 - digit ts i m)) j [MOD 2 * r] := by
  rw [← ZMod.natCast_eq_natCast_iff]
  have hle : synthExpL r ts j m % (2 * r) ≤ 2 * r := (Nat.mod_lt _ (by have := NeZero.pos r; omega)).le
  push_cast [ZMod.natCast_mod, Nat.cast_sub hle, ZMod.natCast_self]
  simp only [synthExpL, axisExp, Nat.cast_list_sum, List.map_map]
  have h2r : (2 : ZMod (2 * r)) * (r : ZMod (2 * r)) = 0 := by exact_mod_cast ZMod.natCast_self (2 * r)
  rw [h2r, zero_sub, ← sub_eq_add_neg, list_sum_map_sub]
  congr 1
  apply List.map_congr_left
  intro i hi
  have hi' := List.mem_range.mp hi
  obtain ⟨a, ha, hdvd⟩ := h.getD hi'
  have hm := digit_lt h.pos i m
  have hc : (2 * r / ts.getD i 1 * ts.getD i 1 : ℕ) = 2 * r := by rw [ha]; exact Nat.div_mul_cancel hdvd
  have hc' : ((2 * r / ts.getD i 1 : ℕ) : ZMod (2 * r)) * (ts.getD i 1 : ℕ) = 0 := by
    rw [← Nat.cast_mul, hc, ZMod.natCast_self]
  simp only [Function.comp_apply]
  push_cast [Nat.cast_sub hm.le]
  linear_combination -(digit ts i j : ZMod (2 * r)) * hc'

theorem subAddr_lt {ts : List ℕ} (hpos : ∀ t ∈ ts, 0 < t) (x y : ℕ) : subAddr ts x y < ts.prod :=
  undigits_lt ts _ fun i _ => Nat.mod_lt _ (getD_pos hpos i)

theorem digit_subAddr {ts : List ℕ} (hpos : ∀ t ∈ ts, 0 < t) (x y : ℕ) {i : ℕ} (hi : i < ts.length) :
    digit ts i (subAddr ts x y) = (digit ts i x + (ts.getD i 1 - digit ts i y)) % ts.getD i 1 :=
  digit_undigits ts _ (fun i _ => Nat.mod_lt _ (getD_pos hpos i)) i hi

/-- Orthogonality for products: the characters of `x`, `-k` and `-l` cancel exactly when `l = x - k`. -/
theorem sum_conv_char {ts : List ℕ} (h : PowAxes r ts) {x k l : ℕ} (hl : l < ts.prod)
    (v : Fin r → ℂ) :
    ∑ j ∈ Finset.range ts.prod, shiftNegZ (synthExpL r ts x j +
        ((2 * r - synthExpL r ts j k % (2 * r)) % (2 * r) +
          (2 * r - synthExpL r ts j l % (2 * r)) % (2 * r))) v =
      if l = subAddr ts x k then (ts.prod : ℂ) • v else 0 := by
  have hmod : ∀ j, synthExpL r ts x j + ((2 * r - synthExpL r ts j k % (2 * r)) % (2 * r) +
      (2 * r - synthExpL r ts j l % (2 * r)) % (2 * r)) ≡
      axisExp r ts (fun i => digit ts i x + (ts.getD i 1 - digit ts i k) +
        (ts.getD i 1 - digit ts i l)) j [MOD 2 * r] := fun j => by
    rw [← Nat.add_assoc]
    exact ((exp_step h (fun i => digit ts i x) j k).add_right _).trans (exp_step h _ j l)
  rw [Finset.sum_congr rfl (fun j _ => shiftNegZ_congr_mod (hmod j) v), sum_axisExp ts h _ v]
  congr 1
  apply propext
  have hpos := h.pos
  constructor
  · intro hc
    refine digits_eq hpos hl (subAddr_lt hpos x k) fun i hi => ?_
    have hci := hc i hi
    rw [← Nat.mod_add_mod] at hci
    rw [digit_subAddr hpos x k hi]
    exact ((diff_mod_eq_zero (Nat.mod_lt _ (getD_pos hpos i)) (digit_lt hpos i l)).mp hci).symm
  · rintro rfl i hi
    rw [← Nat.mod_add_mod, digit_subAddr hpos x k hi]
    exact (diff_mod_eq_zero (Nat.mod_lt _ (getD_pos hpos i)) (Nat.mod_lt _ (getD_pos hpos i))).mpr rfl

/-- The convolution theorem: `F⁺ (F⁻f · F⁻g) = M⁻² (f ⋆ g)`. -/
theorem oppT_mul_fwdT {ts : List ℕ} (h : PowAxes r ts) (f g : ℕ → Fin r → ℂ) {x : ℕ} :
    oppT ts (fun j => negacyclicMul (fwdT ts f j) (fwdT ts g j)) x =
      (1 / (ts.prod : ℂ)) ^ 2 • ∑ y ∈ Finset.range ts.prod, negacyclicMul (f y) (g (subAddr ts x y)) := by
  have hM : (ts.prod : ℂ) ≠ 0 := by
    rw [Nat.cast_ne_zero]; exact (prod_pos h.pos).ne'
  simp only [oppT, fwdT, shiftInv, negacyclicMul_smul_left, negacyclicMul_smul_right,
    negacyclicMul_sum_left, negacyclicMul_sum_right, negacyclicMul_shift_shift, shiftNegZ_smul,
    shiftNegZ_sum, shiftNegZ_add, ← Finset.smul_sum, smul_smul]
  rw [Finset.sum_congr rfl (fun j _ => Finset.sum_comm), Finset.sum_comm]
  have hinner : ∀ k ∈ Finset.range ts.prod, ∑ j ∈ Finset.range ts.prod, ∑ l ∈ Finset.range ts.prod,
      shiftNegZ (synthExpL r ts x j + ((2 * r - synthExpL r ts j k % (2 * r)) % (2 * r) +
        (2 * r - synthExpL r ts j l % (2 * r)) % (2 * r))) (negacyclicMul (f k) (g l)) =
      (ts.prod : ℂ) • negacyclicMul (f k) (g (subAddr ts x k)) := by
    intro k _
    rw [Finset.sum_comm, Finset.sum_congr rfl (fun l hl => sum_conv_char h (Finset.mem_range.mp hl) _),
      Finset.sum_ite_eq']
    simp [subAddr_lt h.pos x k]
  rw [Finset.sum_congr rfl hinner, ← Finset.smul_sum, smul_smul]
  congr 1
  field_simp

/-- In any stored layout the opposite counterpart of a recordwise function of two forward
counterparts is `F⁺` of that function of the two transforms. -/
theorem oppExact_pointwise {ts : List ℕ} (h : PowAxes r ts) (Lp : Equiv.Perm (Fin ts.prod))
    (Φ : (Fin r → ℂ) → (Fin r → ℂ) → (Fin r → ℂ)) (f g : ℕ → Fin r → ℂ) (n : ℕ) :
    oppExact ts Lp (fun y => Φ (fwdExact ts Lp f y) (fwdExact ts Lp g y)) n =
      oppT ts (fun j => Φ (fwdT ts f j) (fwdT ts g j)) n := by
  unfold oppExact oppT
  dsimp only
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  have hj' := Finset.mem_range.mp hj
  have hb := bitrevAddr_lt h j
  rw [dite_eq_left (by rw [Nat.mod_eq_of_lt hb]; exact hb)]
  congr 1
  unfold fwdExact
  simp only [Fin.is_lt, ↓reduceDIte, Fin.eta, Equiv.symm_apply_apply, Nat.mod_eq_of_lt hb,
    bitrevAddr_bitrevAddr h hj']

/-! ### Error of forward, pointwise and opposite -/

/-- The exact recordwise product `fg / r`. -/
noncomputable def prodExact (a b : Fin r → ℂ) : Fin r → ℂ := fun j => negacyclicMul a b j / (r : ℂ)

omit [NeZero r] in
theorem prodExact_eq (a b : Fin r → ℂ) : prodExact a b = (1 / (r : ℂ)) • negacyclicMul a b := by
  funext j; simp [prodExact, div_eq_inv_mul]

theorem oppT_smul {ts : List ℕ} (c : ℂ) (z : ℕ → Fin r → ℂ) (n : ℕ) :
    oppT ts (fun j => c • z j) n = c • oppT ts z n := by
  simp only [oppT, shiftNegZ_smul, ← Finset.smul_sum, smul_comm c]

/-- An average of `M` shifted records of norm at most `δ` has norm at most `δ`. -/
theorem norm_avg_shift_le {M : ℕ} (hM : 0 < M) (e : ℕ → ℕ) (a : ℕ → Fin r → ℂ) {δ : ℝ}
    (ha : ∀ k < M, ‖a k‖ ≤ δ) :
    ‖(1 / (M : ℂ)) • ∑ k ∈ Finset.range M, shiftNegZ (e k) (a k)‖ ≤ δ := by
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  rw [norm_smul, norm_div, norm_one, Complex.norm_natCast]
  have hsum : ‖∑ k ∈ Finset.range M, shiftNegZ (e k) (a k)‖ ≤ M * δ := by
    calc ‖∑ k ∈ Finset.range M, shiftNegZ (e k) (a k)‖
        ≤ ∑ k ∈ Finset.range M, ‖shiftNegZ (e k) (a k)‖ := norm_sum_le _ _
      _ ≤ ∑ _k ∈ Finset.range M, δ := Finset.sum_le_sum fun k hk =>
          (norm_shiftNegZ_le _ _).trans (ha k (Finset.mem_range.mp hk))
      _ = M * δ := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  calc 1 / (M : ℝ) * ‖∑ k ∈ Finset.range M, shiftNegZ (e k) (a k)‖ ≤ 1 / M * (M * δ) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = δ := by field_simp

theorem shiftNegZ_sub (e : ℕ) (a b : Fin r → ℂ) :
    shiftNegZ e (a - b) = shiftNegZ e a - shiftNegZ e b := by
  rw [sub_eq_add_neg, shiftNegZ_add_vec, shiftNegZ_neg, ← sub_eq_add_neg]

/-- The opposite counterpart does not enlarge recordwise differences. -/
theorem norm_oppExact_sub_le {ts : List ℕ} (h : PowAxes r ts) (Lp : Equiv.Perm (Fin ts.prod))
    (a b : ℕ → Fin r → ℂ) {δ : ℝ} (hab : ∀ n < ts.prod, ‖a n - b n‖ ≤ δ) (x : ℕ) :
    ‖oppExact ts Lp a x - oppExact ts Lp b x‖ ≤ δ := by
  unfold oppExact oppT
  rw [← smul_sub, ← Finset.sum_sub_distrib]
  simp only [← shiftNegZ_sub]
  refine norm_avg_shift_le (prod_pos h.pos) _ _ fun k _ => ?_
  have hb := bitrevAddr_lt h k
  rw [dite_eq_left (by rw [Nat.mod_eq_of_lt hb]; exact hb), dite_eq_left (by rw [Nat.mod_eq_of_lt hb]; exact hb)]
  exact hab _ (Fin.is_lt _)

/-- The exact forward counterpart of a disk array lies in the disk. -/
theorem norm_fwdExact_le {ts : List ℕ} (h : PowAxes r ts) (Lp : Equiv.Perm (Fin ts.prod))
    (z : ℕ → Fin r → ℂ) (hz : ∀ n < ts.prod, ‖z n‖ ≤ 1) (y : ℕ) : ‖fwdExact ts Lp z y‖ ≤ 1 := by
  unfold fwdExact
  split_ifs
  · exact norm_avg_shift_le (prod_pos h.pos) _ _ hz
  · simp

omit [NeZero r] in
theorem norm_arrayVec_le {p : ℕ} {fs : List (Rec r)} (hfs : ∀ f ∈ fs, DiskGrid p f.1 f.2) (n : ℕ) :
    ‖arrayVec p fs n‖ ≤ 1 := by
  unfold arrayVec
  split
  · rename_i f hf
    exact (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun j =>
      DiskGrid.norm_le (hfs f (List.mem_of_getElem? hf)) j
  · simp

omit [NeZero r] in
theorem arrayVec_prodRec {p : ℕ} {Fs Gs : List (Rec r)} {n : ℕ} (hF : n < Fs.length) (hG : n < Gs.length) :
    arrayVec p (List.zipWith (prodRec p) Fs Gs) n =
      fun j => rhoC p (prodExact (arrayVec p Fs n) (arrayVec p Gs n) j) := by
  have hz : n < (List.zipWith (prodRec p) Fs Gs).length := by simp; omega
  simp only [arrayVec, List.getElem?_eq_getElem hz, List.getElem?_eq_getElem hF,
    List.getElem?_eq_getElem hG, List.getElem_zipWith]
  rfl

omit [NeZero r] in
theorem norm_sub_lt_of_close {M : ℕ} {u v : ℕ → Fin r → ℂ} {ε : ℝ} (hε : 0 < ε) (h : Close M u v ε)
    {n : ℕ} (hn : n < M) : ‖u n - v n‖ < ε :=
  (pi_norm_lt_iff hε).mpr fun k => h n hn k

/-- The rounded product of two computed transforms is within `(2ℓ + 1) √2 2^(-p)` of the exact product. -/
theorem norm_prod_err {p : ℕ} {a a' b b' : Fin r → ℂ} {η : ℝ} (ha : ‖a' - a‖ < η) (hb : ‖b' - b‖ < η)
    (ha1 : ‖a‖ ≤ 1) (hb1 : ‖b'‖ ≤ 1) :
    ‖(fun j => rhoC p (prodExact a' b' j)) - prodExact a b‖ < 2 * η + Real.sqrt 2 / 2 ^ p := by
  have hr : (0 : ℝ) < r := by exact_mod_cast NeZero.pos r
  have hη : 0 < η := lt_of_le_of_lt (norm_nonneg _) ha
  have hdiff : prodExact a' b' - prodExact a b =
      (1 / (r : ℂ)) • (negacyclicMul (a' - a) b' + negacyclicMul a (b' - b)) := by
    rw [prodExact_eq, prodExact_eq, ← smul_sub]
    congr 1
    have e1 : negacyclicMul (-a) b' = -negacyclicMul a b' := by
      rw [← neg_one_smul ℂ a, negacyclicMul_smul_left, neg_one_smul]
    have e2 : negacyclicMul a (-b) = -negacyclicMul a b := by
      rw [← neg_one_smul ℂ b, negacyclicMul_smul_right, neg_one_smul]
    rw [sub_eq_add_neg a', negacyclicMul_add_left, sub_eq_add_neg b', negacyclicMul_add_right, e1, e2]
    abel
  have hprod : ‖prodExact a' b' - prodExact a b‖ < 2 * η := by
    rw [hdiff, norm_smul, norm_div, norm_one, Complex.norm_natCast]
    have h1 := norm_negacyclicMul_le (a' - a) b'
    have h2 := norm_negacyclicMul_le a (b' - b)
    have hsum := norm_add_le (negacyclicMul (a' - a) b') (negacyclicMul a (b' - b))
    have hn1 : ‖a' - a‖ * ‖b'‖ ≤ ‖a' - a‖ := by
      have := norm_nonneg (a' - a); nlinarith [norm_nonneg b']
    have hn2 : ‖a‖ * ‖b' - b‖ ≤ ‖b' - b‖ := by
      have := norm_nonneg (b' - b); nlinarith [norm_nonneg a]
    have hlt : ‖negacyclicMul (a' - a) b' + negacyclicMul a (b' - b)‖ < r * (2 * η) := by
      nlinarith
    calc 1 / (r : ℝ) * ‖negacyclicMul (a' - a) b' + negacyclicMul a (b' - b)‖
        < 1 / r * (r * (2 * η)) := mul_lt_mul_of_pos_left hlt (by positivity)
      _ = 2 * η := by field_simp
  have hround : ‖(fun j => rhoC p (prodExact a' b' j)) - prodExact a' b'‖ < Real.sqrt 2 / 2 ^ p :=
    (pi_norm_lt_iff (by positivity)).mpr fun j => norm_rhoC_sub_lt p _
  calc ‖(fun j => rhoC p (prodExact a' b' j)) - prodExact a b‖
      ≤ ‖(fun j => rhoC p (prodExact a' b' j)) - prodExact a' b'‖ + ‖prodExact a' b' - prodExact a b‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ < Real.sqrt 2 / 2 ^ p + 2 * η := add_lt_add hround hprod
    _ = 2 * η + Real.sqrt 2 / 2 ^ p := add_comm _ _

/-- The error of the convolution: forward transforms within `√2 ℓ 2^(-p)`, rounded pointwise
products and an opposite transform within `√2 ℓ 2^(-p)`, scaled by `M`, are within
`√2 M (3ℓ + 1) 2^(-p)` of the normalized convolution. -/
theorem conv_error {ts : List ℕ} (h : PowAxes r ts) (Lp : Equiv.Perm (Fin ts.prod)) {p ℓ : ℕ}
    (fs gs Fs Gs Vs : List (Rec r)) (hfs : ∀ f ∈ fs, DiskGrid p f.1 f.2)
    (hFlen : Fs.length = ts.prod) (hGlen : Gs.length = ts.prod)
    (hGs : ∀ g ∈ Gs, DiskGrid p g.1 g.2)
    (hF : Close ts.prod (arrayVec p Fs) (fwdExact ts Lp (arrayVec p fs)) (Real.sqrt 2 * ℓ / 2 ^ p))
    (hG : Close ts.prod (arrayVec p Gs) (fwdExact ts Lp (arrayVec p gs)) (Real.sqrt 2 * ℓ / 2 ^ p))
    (hV : Close ts.prod (arrayVec p Vs) (oppExact ts Lp (arrayVec p (List.zipWith (prodRec p) Fs Gs)))
      (Real.sqrt 2 * ℓ / 2 ^ p)) :
    Close ts.prod (fun n => (ts.prod : ℂ) • arrayVec p Vs n) (convM ts (arrayVec p fs) (arrayVec p gs))
      (Real.sqrt 2 * ts.prod * (3 * ℓ + 1) / 2 ^ p) := by
  have hMpos := prod_pos h.pos
  have hM : (0 : ℝ) < ts.prod := by exact_mod_cast hMpos
  have hMc : (ts.prod : ℂ) ≠ 0 := by exact_mod_cast hMpos.ne'
  have hε : (0 : ℝ) < Real.sqrt 2 / 2 ^ p := by positivity
  set ε := Real.sqrt 2 / 2 ^ p with hεdef
  have hℓε : Real.sqrt 2 * ℓ / 2 ^ p = ℓ * ε := by rw [hεdef]; ring
  -- the exact recordwise products and the computed ones
  set P : ℕ → Fin r → ℂ := fun y => prodExact (fwdExact ts Lp (arrayVec p fs) y) (fwdExact ts Lp (arrayVec p gs) y)
  set U := arrayVec p (List.zipWith (prodRec p) Fs Gs)
  have hpoint : ∀ n < ts.prod, ‖U n - P n‖ < 2 * (ℓ * ε) + ε := by
    intro n hn
    rw [show U n = _ from arrayVec_prodRec (hFlen ▸ hn) (hGlen ▸ hn)]
    rcases Nat.eq_zero_or_pos ℓ with hℓ | hℓ
    · -- with `ℓ = 0` the forward closeness is vacuous only if the bound is positive; it is not
      have := hF n hn ⟨0, NeZero.pos r⟩
      rw [hℓε, hℓ] at this; simp at this; exact absurd this (not_lt.mpr (norm_nonneg _))
    have hℓreal : (0 : ℝ) < ℓ := by exact_mod_cast hℓ
    have hℓpos : 0 < (ℓ : ℝ) * ε := mul_pos hℓreal hε
    exact norm_prod_err (by rw [← hℓε]; exact norm_sub_lt_of_close (by rw [hℓε]; exact hℓpos) hF hn)
      (by rw [← hℓε]; exact norm_sub_lt_of_close (by rw [hℓε]; exact hℓpos) hG hn)
      (norm_fwdExact_le h Lp _ (fun k _ => norm_arrayVec_le hfs k) n) (norm_arrayVec_le hGs n)
  -- the largest pointwise error
  obtain ⟨δ, hδ, hδlt⟩ : ∃ δ, (∀ n < ts.prod, ‖U n - P n‖ ≤ δ) ∧ δ < 2 * (ℓ * ε) + ε := by
    refine ⟨(Finset.range ts.prod).sup' (Finset.nonempty_range_iff.mpr hMpos.ne') fun n => ‖U n - P n‖,
      fun n hn => Finset.le_sup' (fun n => ‖U n - P n‖) (Finset.mem_range.mpr hn), ?_⟩
    rw [Finset.sup'_lt_iff]
    exact fun n hn => hpoint n (Finset.mem_range.mp hn)
  have hexact : ∀ x < ts.prod, (ts.prod : ℂ) • oppExact ts Lp P x = convM ts (arrayVec p fs) (arrayVec p gs) x := by
    intro x _
    simp only [P]
    rw [oppExact_pointwise h Lp prodExact]
    simp only [prodExact_eq]
    rw [oppT_smul, oppT_mul_fwdT h, convM, smul_smul, smul_smul]
    congr 1
    push_cast
    field_simp
  intro x hx k
  have hopp := norm_oppExact_sub_le h Lp U P hδ x
  have hVx := hV x hx k
  rw [hℓε] at hVx
  rw [← hexact x hx]
  simp only [Pi.smul_apply]
  rw [← smul_sub, norm_smul, Complex.norm_natCast]
  have hk : ‖arrayVec p Vs x k - oppExact ts Lp P x k‖ < ℓ * ε + (2 * (ℓ * ε) + ε) := by
    calc ‖arrayVec p Vs x k - oppExact ts Lp P x k‖
        ≤ ‖arrayVec p Vs x k - oppExact ts Lp U x k‖ + ‖oppExact ts Lp U x k - oppExact ts Lp P x k‖ :=
          norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ < ℓ * ε + (2 * (ℓ * ε) + ε) := by
          apply add_lt_add_of_lt_of_le hVx
          exact (norm_le_pi_norm (oppExact ts Lp U x - oppExact ts Lp P x) k).trans (hopp.trans hδlt.le)
  calc (ts.prod : ℝ) * ‖arrayVec p Vs x k - oppExact ts Lp P x k‖
      < ts.prod * (ℓ * ε + (2 * (ℓ * ε) + ε)) := mul_lt_mul_of_pos_left hk hM
    _ = Real.sqrt 2 * ts.prod * (3 * ℓ + 1) / 2 ^ p := by rw [hεdef]; ring

end IntegerMultBounds.Spec.SignedRingProduct
