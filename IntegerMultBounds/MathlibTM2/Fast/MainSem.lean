module

public import IntegerMultBounds.MathlibTM2.Fast.MainProg

/-!
# Formats and values between the stages of the fast multiplier

The stage machines of `Fast/MainProg` meet at stream formats that agree up to the identities
proved here, and the values they carry satisfy the bounds the next stage needs.

**Formats.**
* `mn_digitStream_eq`: the digit records of `Fast/Input` are the coefficient stream
  `srcCoef p S u` of the quarter-scaled digits `u = scaledDigits S b (digitsOf b xs)` read by the
  source transform.
* `mn_srcPad_eq`: the padded source box `srcPad q s t f` is the numerator box of the zero
  extension `mnPad s t f` on the box `∏ ZMod (t i)` read by the pointwise product; `mn_rdV_pad`:
  the truncated pointwise product commutes with the zero extension.
* `mn_coef_stream`: a coefficient stream is the stream of residues read by the rounding stage.
* `mn_pipelineCoeffs_eq`: the coefficients of `Pipeline.pipelineCoeffs` are the rounded
  numerators `rndCoeff b S p N_i.re` the rounding stage writes, for `N_i` the numerators of the
  computed opposite transform.

**Values.**
* `mn_srcMap_fixed`, `mn_oppMap_fixed`: the computed transforms take values on the grid
  `2^{-p} ℤ[i]` (`B̃₀` ends with a truncation `Q_p` on every line, `× 2^γ` and conjugation keep
  the grid).
* `mn_srcMap_norm`, `mn_oppMap_norm`: on inputs of norm at most `1/2` both have norm at most
  `0.51` (`SourceErr.sourceApprox_norm_le`).
* `mn_fits`, `mn_rndCoeff_lt`: numerators of values of norm at most `0.51` fit `w ≥ q + 1` bits,
  and their rounded coefficients are below `2^{2b + 2 size S + 6}`.
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2.Fast.Main

open IntegerMultBounds IntegerMultBounds.NLogN IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Layer
open IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Src IntegerMultBounds.MathlibTM2.Fast.ResampA IntegerMultBounds.MathlibTM2.Fast.ChirpSt IntegerMultBounds.MathlibTM2.Fast.ConvSt
open IntegerMultBounds.MathlibTM2.Mult IntegerMultBounds.MathlibTM2.Mult.Sizes IntegerMultBounds.MathlibTM2.Mult.Pipeline

set_option linter.unusedSimpArgs false

noncomputable section

/-! ### Grid values -/

lemma mn_numer_zero (q : ℕ) : numer q 0 = 0 := by
  simp [numer, rho0]
  rfl

lemma mn_rhoC_zero (q : ℕ) : rhoC q 0 = 0 := by
  apply Complex.ext <;> simp [rhoC, rho0]

lemma mn_isFixed_zero (q : ℕ) : IsFixed q 0 := ⟨0, 0, by apply Complex.ext <;> simp⟩

/-- A value of norm at most `0.51` has a numerator fitting `w ≥ q + 1` bits. -/
theorem mn_fits {q w : ℕ} {z : ℂ} (hz : ‖z‖ ≤ 51 / 100) (hw : q + 1 ≤ w) : Fits w (numer q z) :=
  cst_fits_numer (k := 0) (by rw [pow_zero]; linarith) (by omega)

/-! ### The zero extension of a source box -/

section Pad

variable {d : ℕ}

/-- The zero extension of a function on the source box `∏ ZMod (s i)` to the box
`∏ ZMod (t i)`. -/
def mnPad (s t : Fin d → ℕ) (f : ((i : Fin d) → ZMod (s i)) → ℂ) :
    ((i : Fin d) → ZMod (t i)) → ℂ :=
  fun y => if ∀ i, (y i).val < s i then f (fun i => ((y i).val : ZMod (s i))) else 0

/-- The padded stream of `f` is the numerator box of its zero extension. -/
theorem mn_srcPad_eq (q : ℕ) (s t : Fin d → ℕ) [∀ i, NeZero (t i)]
    (f : ((i : Fin d) → ZMod (s i)) → ℂ) : srcPad q s t f = cstNumBox q t (mnPad s t f) := by
  rw [srcPad, cstNumBox_eq]
  congr 1
  funext x
  have hv : ∀ i, (cstCast t x i).val = (x i : ℕ) := fun i =>
    ZMod.val_natCast_of_lt (x i).isLt
  simp only [mnPad, hv]
  split_ifs
  · rfl
  · exact (mn_numer_zero q).symm

/-- The truncated pointwise product commutes with the zero extension. -/
theorem mn_rdV_pad (q : ℕ) (s t : Fin d → ℕ) (f h : ((i : Fin d) → ZMod (s i)) → ℂ) :
    rdV q (mnPad s t f * mnPad s t h) = mnPad s t (rdV q (f * h)) := by
  funext y
  simp only [rdV, Pi.mul_apply, mnPad]
  split_ifs
  · rfl
  · rw [mul_zero, mn_rhoC_zero]

theorem mn_pad_fixed {q : ℕ} {s t : Fin d → ℕ} {f : ((i : Fin d) → ZMod (s i)) → ℂ}
    (hf : ∀ x, IsFixed q (f x)) (y : (i : Fin d) → ZMod (t i)) : IsFixed q (mnPad s t f y) := by
  unfold mnPad
  split_ifs
  · exact hf _
  · exact mn_isFixed_zero q

theorem mn_pad_fits {q w : ℕ} {s t : Fin d → ℕ} {f : ((i : Fin d) → ZMod (s i)) → ℂ}
    (hf : ∀ x, Fits w (numer q (f x))) (y : (i : Fin d) → ZMod (t i)) :
    Fits w (numer q (mnPad s t f y)) := by
  unfold mnPad
  split_ifs
  · exact hf _
  · rw [mn_numer_zero]; exact rsa_fits_zero w

end Pad

/-! ### The computed transforms on the grid -/

section Fixed

/-- A tensor of line maps with grid values takes grid values (`d ≥ 1`). -/
theorem mn_tensorZR_fixed {q : ℕ} : ∀ (d : ℕ) (M N : Fin d → ℕ)
    (B : (i : Fin d) → (ZMod (M i) → ℂ) → (ZMod (N i) → ℂ)),
    (∀ i f j, IsFixed q (B i f j)) → 0 < d →
    ∀ (u : ((i : Fin d) → ZMod (M i)) → ℂ) (x : (i : Fin d) → ZMod (N i)),
      IsFixed q (tensorZR d M N B u x)
  | 0, _, _, _, _, h, _, _ => absurd h (lt_irrefl 0)
  | d + 1, M, N, B, hB, _, u, x => by
      simp only [tensorZR, Function.comp_apply, alongHeadZR]
      exact hB 0 _ _

/-- `B̃₀` on one line ends with the truncation `Q_p`. -/
theorem mn_lineB_fixed (n : ℕ) (i : Fin (d n)) (f : ZMod (t n i) → ℂ) (j : ZMod (s n i)) :
    IsFixed (p n) (lineB n i f j) := by
  simp only [lineB, FastB0.resampB₀NumK, Resampling.TabledMaps.diagW]
  exact isFixed_rhoC _ _

theorem mn_sourceApprox_fixed {n : ℕ} (hd : 0 < d n) (v : ((i : Fin (d n)) → ZMod (s n i)) → ℂ)
    (k : (i : Fin (d n)) → ZMod (s n i)) :
    IsFixed (p n) (SourceErr.sourceApprox (s n) (t n) (p n) (gamma n) (lineA n) (lineB n)
      (chirpKernel n) (convBox n) v k) := by
  simp only [SourceErr.sourceApprox, Pi.smul_apply, smul_eq_mul]
  have h := (mn_tensorZR_fixed (d n) (t n) (s n) (lineB n) (mn_lineB_fixed n) hd
    (bluesteinApproxD (p n) (chirpKernel n) (convBox n)
      (tensorZR (d n) (s n) (t n) (lineA n) v)) k).natMul (2 ^ gamma n)
  push_cast at h
  exact h

/-- The computed source transform takes values on the grid. -/
theorem mn_srcMap_fixed {n : ℕ} (hd : 0 < d n) (u : ZMod (∏ i, s n i) → ℂ)
    (k : (i : Fin (d n)) → ZMod (s n i)) : IsFixed (p n) (srcMap n u k) := by
  rw [src_srcMap_eq]
  exact mn_sourceApprox_fixed hd _ k

/-- The computed opposite transform takes values on the grid. -/
theorem mn_oppMap_fixed {n : ℕ} (hd : 0 < d n) (y : ((i : Fin (d n)) → ZMod (s n i)) → ℂ)
    (k : ZMod (∏ i, s n i)) : IsFixed (p n) (oppMap n y k) := by
  rw [src_oppMap_eq]
  exact cst_isFixed_conj (mn_sourceApprox_fixed hd _ _)

end Fixed

/-! ### Norms -/

section Norms

variable {n : ℕ}

/-- On inputs of norm at most `1/2` the computed source transform has norm at most `0.51`. -/
theorem mn_srcMap_norm (hbig : Big n) (hsmall : 2 * d n * p n ^ 2 ≤ Sizes.T n * logT n)
    (hEs : 9 * (2 : ℝ) ^ gamma n * Sizes.T n * logT n ≤ 2 ^ p n / 100)
    {u : ZMod (∏ i, s n i) → ℂ} (hu : ‖u‖ ≤ 1 / 2) : ‖srcMap n u‖ ≤ 51 / 100 := by
  obtain ⟨hF, hG⟩ := source_approx hbig hsmall hEs
  rw [src_srcMap_eq]
  exact (SourceErr.sourceApprox_norm_le hF hG (by linarith)
    ((norm_comp_le_pi_norm _ u).trans hu)).1

/-- On inputs of norm at most `1/2` the computed opposite transform has norm at most `0.51`. -/
theorem mn_oppMap_norm (hbig : Big n) (hsmall : 2 * d n * p n ^ 2 ≤ Sizes.T n * logT n)
    (hEs : 9 * (2 : ℝ) ^ gamma n * Sizes.T n * logT n ≤ 2 ^ p n / 100)
    {y : ((i : Fin (d n)) → ZMod (s n i)) → ℂ} (hy : ‖y‖ ≤ 1 / 2) : ‖oppMap n y‖ ≤ 51 / 100 := by
  obtain ⟨hF, hG⟩ := source_approx hbig hsmall hEs
  have h := (SourceErr.sourceApprox_norm_le hF hG (by linarith) hy).2
  have e : oppMap n y = SourceErr.oppApprox (s n) (t n) (p n) (gamma n) (lineA n) (lineB n)
      (chirpKernel n) (convBox n) y ∘ crtPhi (s n) (s_pairwise n) := rfl
  rw [e]
  exact (norm_comp_le_pi_norm _ _).trans h

/-- The truncated pointwise product of two values of norm at most `0.51` has norm at most
`1/2`. -/
theorem mn_rdV_norm {ι : Type} [Fintype ι] (q : ℕ) {f h : ι → ℂ} (hf : ‖f‖ ≤ 51 / 100)
    (hh : ‖h‖ ≤ 51 / 100) : ‖rdV q (f * h)‖ ≤ 1 / 2 := by
  rw [pi_norm_le_iff_of_nonneg (by norm_num)]
  intro k
  refine (norm_rhoC_le q _).trans ?_
  rw [Pi.mul_apply, norm_mul]
  have h1 := (norm_le_pi_norm f k).trans hf
  have h2 := (norm_le_pi_norm h k).trans hh
  have := mul_le_mul h1 h2 (norm_nonneg _) (by norm_num)
  linarith

end Norms

/-! ### Digits -/

section Digits

open IntegerMultBounds.ExactRecovery (scaledDigits norm_scaledDigits_le)

/-- The numerator of a quarter-scaled digit. -/
theorem mn_numer_scaledDigits {b p S : ℕ} [NeZero S] (hbp : b + 2 ≤ p) (ds : List ℕ)
    (k : ZMod S) :
    numer p (scaledDigits S b ds k) = ⟨(ds.getD k.val 0 : ℤ) * 2 ^ (p - b - 2), 0⟩ := by
  rw [← numerator_div_eq_scaledDigits hbp ds k, numer_grid]

/-- **The digit records are the coefficient stream of the quarter-scaled digits.** -/
theorem mn_digitStream_eq {A b p w S : ℕ} [NeZero S] (hbp : b + 2 ≤ p) (xs : List Bool) :
    digitStream A b p w S xs =
      cstream A w (srcCoef p S (scaledDigits S b (digitsOf b xs))) := by
  rw [digitStream, cst_cstream_eq_red, srcCoef, List.map_map]
  congr 1
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp only [List.getElem_map, List.getElem_ofFn, List.getElem_range, Function.comp_apply]
  rw [mn_numer_scaledDigits hbp]
  have hi : i < S := by simpa using h1
  rw [ZMod.val_natCast_of_lt hi]

theorem mn_scaledDigits_norm {b S : ℕ} [NeZero S] (hb : 0 < b) (xs : List Bool) :
    ‖scaledDigits S b (digitsOf b xs)‖ ≤ 1 / 2 :=
  (norm_scaledDigits_le (digitsOf_lt hb xs)).trans (by norm_num)

theorem mn_scaledDigits_fixed {b p S : ℕ} [NeZero S] (hbp : b + 2 ≤ p) (xs : List Bool)
    (k : ZMod S) : IsFixed p (scaledDigits S b (digitsOf b xs) k) := by
  rw [← numerator_div_eq_scaledDigits hbp]
  exact cst_isFixed_grid p _

/-- Every operand of at most `n` bits has at most `S` digits. -/
theorem mn_digits_len {n : ℕ} (h : Big n) (x : ℕ) : (digitsOf (b n) (bitsMSB n x)).length ≤ S n := by
  have hb := one_le_b h.1
  have h1 := digitsOf_length_le_div hb (bitsMSB n x)
  rw [length_bitsMSB] at h1
  have h2 := h.two_q_le
  have h3 : 0 < S n := by have := h.T_lt_two_S; have := h.S_lt_T; omega
  unfold q at h2
  omega

end Digits

/-! ### Rounding -/

section Round

/-- A coefficient stream is the stream of the residues of its numerators. -/
theorem mn_coef_stream (A w q S : ℕ) (g : ZMod S → ℂ) :
    cstream A w (srcCoef q S g) =
      (List.ofFn fun i : Fin S => red w (numer q (g ((i : ℕ) : ZMod S)))).flatMap
        (coeffSyms A w) := by
  rw [cst_cstream_eq_red, srcCoef, List.map_map]
  congr 1
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp

/-- The rounded coefficient of a value of norm at most `0.51` is below `2^{2b + 2 size S + 6}`. -/
theorem mn_rndCoeff_lt {b S p : ℕ} {z : ℂ} (hz : ‖z‖ ≤ 51 / 100) :
    rndCoeff b S p (numer p z).re < 2 ^ (2 * b + 2 * Nat.size S + 6) := by
  have hp : (0 : ℝ) < 2 ^ p := by positivity
  have hre : |((numer p z).re : ℝ)| ≤ 2 ^ p * (51 / 100) := by
    simp only [numer]
    refine (abs_rho0_le _).trans ?_
    rw [abs_mul, abs_of_pos hp]
    exact mul_le_mul_of_nonneg_left ((Complex.abs_re_le_norm z).trans hz) hp.le
  have hS : (S : ℝ) < 2 ^ Nat.size S := by exact_mod_cast Nat.lt_size_self S
  have hS0 : (0 : ℝ) ≤ S := Nat.cast_nonneg _
  have hX0 : (0 : ℝ) ≤ 2 ^ (2 * b) * S * 16 * S := by positivity
  have hy : (2 ^ (2 * b) * S * 16 * S : ℝ) * (((numer p z).re : ℝ) / 2 ^ p) ≤
      (2 ^ (2 * b) * S * 16 * S : ℝ) * (51 / 100) := by
    refine mul_le_mul_of_nonneg_left ?_ hX0
    rw [div_le_iff₀ hp]
    have := le_abs_self ((numer p z).re : ℝ)
    linarith
  have hXlt : (2 ^ (2 * b) * S * 16 * S : ℝ) ≤ 2 ^ (2 * b + 2 * Nat.size S + 4) := by
    have hSS : (S : ℝ) * S ≤ 2 ^ Nat.size S * 2 ^ Nat.size S :=
      mul_le_mul hS.le hS.le hS0 (by positivity)
    calc (2 ^ (2 * b) * S * 16 * S : ℝ) = 2 ^ (2 * b) * 16 * (S * S) := by ring
      _ ≤ 2 ^ (2 * b) * 16 * (2 ^ Nat.size S * 2 ^ Nat.size S) := by gcongr
      _ = 2 ^ (2 * b + 2 * Nat.size S + 4) := by
        rw [show 2 * b + 2 * Nat.size S + 4 = 2 * b + Nat.size S + Nat.size S + 4 by ring,
          pow_add, pow_add, pow_add]
        norm_num
        ring
  have hE1 : (1 : ℝ) ≤ 2 ^ (2 * b + 2 * Nat.size S + 4) := one_le_pow₀ (by norm_num)
  set Y : ℝ := (2 ^ (2 * b) * S * 16 * S : ℝ) * (((numer p z).re : ℝ) / 2 ^ p) with hY
  have h1 := round_le_add_half Y
  have h2 : ((round Y : ℤ) : ℝ) < ((2 ^ (2 * b + 2 * Nat.size S + 6) : ℕ) : ℝ) := by
    push_cast
    rw [show 2 * b + 2 * Nat.size S + 6 = (2 * b + 2 * Nat.size S + 4) + 2 by ring, pow_add]
    nlinarith
  have h3 : round Y < ((2 ^ (2 * b + 2 * Nat.size S + 6) : ℕ) : ℤ) := by exact_mod_cast h2
  unfold rndCoeff
  rw [← hY]
  rcases le_or_gt (round Y) 0 with h0 | h0
  · rw [Int.toNat_eq_zero.2 h0]; positivity
  · have h4 : ((round Y).toNat : ℤ) < ((2 ^ (2 * b + 2 * Nat.size S + 6) : ℕ) : ℤ) := by
      rw [Int.toNat_of_nonneg h0.le]; exact h3
    exact_mod_cast h4

end Round

/-! ### The coefficients of the pipeline -/

section Pipeline

open IntegerMultBounds.ExactRecovery (scaledDigits computedConv computed)

/-- The operand vector of `x`: the quarter-scaled digits of its low `n` bits. -/
abbrev mnU (n x : ℕ) : ZMod (∏ i, s n i) → ℂ :=
  scaledDigits (∏ i, s n i) (b n) (digitsOf (b n) (bitsMSB n x))

/-- The argument of the opposite transform: the truncated pointwise product of the two computed
source transforms. -/
abbrev mnY (n x y : ℕ) : ((i : Fin (d n)) → ZMod (s n i)) → ℂ :=
  rdV (p n) (srcMap n (mnU n x) * srcMap n (mnU n y))

/-- **The coefficients of the pipeline** are the rounded numerators of the computed opposite
transform. -/
theorem mn_pipelineCoeffs_eq {n : ℕ} (hd : 0 < d n) (x y : ℕ) :
    pipelineCoeffs n x y = List.ofFn fun i : Fin (∏ i, s n i) =>
      rndCoeff (b n) (∏ i, s n i) (p n)
        (numer (p n) (oppMap n (mnY n x y) ((i : ℕ) : ZMod (∏ i, s n i)))).re := by
  unfold pipelineCoeffs
  congr 1
  funext i
  rw [← rndCoeff_complex (b n) (∏ i, s n i) (p n) _ _
    (cst_grid_numer (mn_oppMap_fixed hd (mnY n x y) ((i : ℕ) : ZMod (∏ i, s n i)))).symm]
  rfl

end Pipeline

end

end IntegerMultBounds.MathlibTM2.Fast.Main
