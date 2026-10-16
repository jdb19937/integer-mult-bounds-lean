module

public import IntegerMultBounds.MathlibTM2.Fast.SrcRegs

/-!
# Semantics of the source transform on streams

Pure facts behind the composite machines of `Fast/SrcStage`.

**Formats.** `srcPad q s t f`: a function `f` on the source box `∏ ZMod (s i)` as the padded box
stream on `∏ [0, t i)` (`rsaBox` order, axis `0` most significant): the numerator at scale `2^q`
of `f` at every address below `s`, zero elsewhere. `srcCoef q S u`: the coefficient stream of
`u : ZMod S → ℂ`, the numerators at scale `2^q` of `u 0, …, u (S - 1)`.

**CRT conversions.** `src_crt_fwd`: the box written by `crtForward` from the records of
`srcCoef q (∏ s) u` and the zero record is the stream of `srcPad q s t (u ∘ Φ⁻¹)`
(`Φ = crtPhi s hcop`), when `t j = 2^{a j}`. `src_crt_inv_box`, `src_crt_inv`: the stream of
`srcPad q s t g` is the CRT box of `srcRec q s g`, and the records `crtInverse` reads off it
at the addresses `Φ k` are those of `srcCoef q (∏ s) (g ∘ Φ)`.

**Products.** `src_numer_rhoC_mul_succ`: a product of grid values at scales `2^q` and
`2^{q+1}` truncated at scale `2^q` has numerator `tdivN (q + 1) (N₁ N₂)`; `src_zip_chirp1` is
its box form, the first chirp product `Q_p(ā' · Ã u)` on the output of `Ã` (scale `2^{p+1}`).
`src_boxConv_isFixed`: the computed convolution `Pipeline.boxConv` takes grid values.

**Margins** (`src_margins`). For `‖v‖ ≤ 1/2` and the pipeline's ingredients (`lineA`,
`chirpKernel`, `convBox`): `‖Ã v‖ ≤ .6`, `‖Q_p(ā' · Ã v)‖ ≤ .6`, `‖M'(a', ·)‖ ≤ .701`,
`‖C̃ (Ã v)‖ ≤ .701` (`SourceErr.sourceApprox_margins` with `Pipeline.convBox_spec`). These keep
every stage inside the disk its theorem asks for.
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2.Fast.Src

open IntegerMultBounds IntegerMultBounds.NLogN IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.ResampA IntegerMultBounds.MathlibTM2.Fast.ChirpSt IntegerMultBounds.MathlibTM2.Fast.ConvSt
open IntegerMultBounds.MathlibTM2.Mult
open scoped Function

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

noncomputable section

/-! ### Formats -/

section Formats

variable {d : ℕ}

/-- The padded box stream of a function on the source box: the numerators at scale `2^q` at
the addresses of `∏ [0, t i)` below `s`, zero elsewhere. -/
def srcPad (q : ℕ) (s t : Fin d → ℕ) (f : ((i : Fin d) → ZMod (s i)) → ℂ) : List GaussianInt :=
  rsaBox d t fun x => if ∀ i, (x i : ℕ) < s i then numer q (f fun i => ((x i : ℕ) : ZMod (s i)))
    else 0

/-- The coefficient stream of `u : ZMod S → ℂ`: numerators at scale `2^q`, index increasing. -/
def srcCoef (q S : ℕ) (u : ZMod S → ℂ) : List GaussianInt :=
  (List.range S).map fun k : ℕ => numer q (u (k : ZMod S))

/-- The CRT content of a padded box: the coefficient at a valid address, zero elsewhere. -/
def srcRec (q : ℕ) (s : Fin d → ℕ) (g : ((i : Fin d) → ZMod (s i)) → ℂ) (y : Fin d → ℕ) :
    GaussianInt :=
  if ∀ i, y i < s i then numer q (g fun i => ((y i : ℕ) : ZMod (s i))) else 0

lemma src_length_coef (q S : ℕ) (u : ZMod S → ℂ) : (srcCoef q S u).length = S := by
  simp [srcCoef]

lemma src_length_pad (q : ℕ) (s t : Fin d → ℕ) (f : ((i : Fin d) → ZMod (s i)) → ℂ) :
    (srcPad q s t f).length = ∏ i, t i := length_rsaBox d t _

lemma src_cstream_rsaBox {A w : ℕ} (t : Fin d → ℕ) (G : ((i : Fin d) → Fin (t i)) → GaussianInt) :
    cstream A w (rsaBox d t G) = (rsaBox d t fun x => csyms A w (G x)).flatten := by
  rw [rsaBox_map (csyms A w) d t G, cstream, List.flatMap_def]

/-- The symbols of a coefficient stream are pair symbols, below `8`. -/
lemma src_csyms_lt {A w : ℕ} (hA : 4 ≤ A) (N : GaussianInt) : ∀ c ∈ csyms A w N, c.val < 8 := by
  intro c hc
  simp only [csyms, coeffSyms, List.mem_ofFn] at hc
  obtain ⟨j, rfl⟩ := hc
  rw [pairSym_val hA]
  cases (red w N).1.val.testBit j <;> cases (red w N).2.val.testBit j <;> simp

variable (s : Fin d → ℕ) [∀ i, NeZero (s i)] (hcop : Pairwise (Nat.Coprime on s))

/-- **The forward CRT layout on coefficient streams.** -/
theorem src_crt_fwd {A w q : ℕ} (a t : Fin d → ℕ) (ht : ∀ j, t j = 2 ^ a j)
    (u : ZMod (∏ i, s i) → ℂ) :
    (crtBox a (List.finRange d)
        (crtSpecC s hcop ((srcCoef q (∏ i, s i) u).map (csyms A w)) (csyms A w 0)) 0).flatten =
      cstream A w (srcPad q s t fun x => u ((crtPhi s hcop).symm x)) := by
  rw [src_crtBox_rsaBox d a t ht, srcPad, src_cstream_rsaBox]
  congr 2
  funext x
  simp only [crtSpecC]
  split_ifs with h
  · rw [List.getD_eq_getElem?_getD, List.getElem?_map, srcCoef, List.getElem?_map,
      List.getElem?_range (ZMod.val_lt _)]
    simp only [Option.map_some, Option.getD_some, ZMod.natCast_zmod_val]
  · rfl

/-- The padded box of `g` is the CRT box of its content. -/
theorem src_crt_inv_box {A w q : ℕ} (a t : Fin d → ℕ) (ht : ∀ j, t j = 2 ^ a j)
    (g : ((i : Fin d) → ZMod (s i)) → ℂ) :
    cstream A w (srcPad q s t g) =
      (crtBox a (List.finRange d) (fun y => csyms A w (srcRec q s g y)) 0).flatten := by
  rw [src_crtBox_rsaBox d a t ht, srcPad, src_cstream_rsaBox]
  rfl

/-- **The inverse CRT layout on coefficient streams.** The records at the addresses `Φ k` are
the coefficient stream of `g ∘ Φ`. -/
theorem src_crt_inv {A w q : ℕ} (g : ((i : Fin d) → ZMod (s i)) → ℂ) :
    ((List.range (∏ j, s j)).map fun k =>
        csyms A w (srcRec q s g fun j =>
          (crtPhi s hcop ((k : ℕ) : ZMod (∏ i, s i)) j).val)).flatten =
      cstream A w (srcCoef q (∏ i, s i) fun k => g (crtPhi s hcop k)) := by
  rw [cstream, srcCoef, List.flatMap_def, List.map_map]
  congr 1
  refine List.map_congr_left fun k _ => ?_
  simp only [Function.comp_apply, srcRec]
  rw [ite_eq_left (fun i => ZMod.val_lt _)]
  simp only [ZMod.natCast_zmod_val]

end Formats

/-! ### Grid products -/

section Products

theorem src_grid_mul_succ (q : ℕ) (N₁ N₂ : GaussianInt) :
    cstGrid q N₁ * cstGrid (q + 1) N₂ = cstGrid (q + (q + 1)) (N₁ * N₂) := by
  unfold cstGrid
  rw [map_mul]
  have h1 : (2 : ℂ) ^ q ≠ 0 := pow_ne_zero _ two_ne_zero
  have h2 : (2 : ℂ) ^ (q + 1) ≠ 0 := pow_ne_zero _ two_ne_zero
  field_simp
  ring

/-- **A product of grid values at scales `2^q` and `2^{q+1}`,** truncated at scale `2^q`. -/
theorem src_numer_rhoC_mul_succ {q : ℕ} {u v : ℂ} (hu : IsFixed q u) (hv : IsFixed (q + 1) v) :
    numer q (rhoC q (u * v)) = tdivN (q + 1) (numer q u * numer (q + 1) v) := by
  conv_lhs => rw [← cst_grid_numer hu, ← cst_grid_numer hv]
  rw [src_grid_mul_succ, cst_rhoC_grid_shift, cst_numer_grid]

variable {d : ℕ} (t : Fin d → ℕ)

/-- The first chirp product on numerator boxes: the kernel at scale `2^q`, the operand at scale
`2^{q+1}`, the products truncated with the shift `q + 1`. -/
theorem src_zip_chirp1 {q : ℕ} (a' x : ((i : Fin d) → ZMod (t i)) → ℂ)
    (ha : ∀ k, IsFixed q (a' (cstCast t k))) (hx : ∀ k, IsFixed (q + 1) (x (cstCast t k))) :
    List.zipWith (fun y z => tdivN (q + 1) (y * z))
        (cstNumBox q t fun k => starRingEnd ℂ (a' k)) (cstNumBox (q + 1) t x) =
      cstNumBox q t (cstChirpProd t q a' x) := by
  rw [cstNumBox_eq, cstNumBox_eq, cstNumBox_eq, cst_zipWith_rsaBox]
  congr 1
  funext k
  simp only [cstChirpProd]
  rw [src_numer_rhoC_mul_succ (cst_isFixed_conj (ha k)) (hx k)]

end Products

/-- The computed convolution of `Mult/Pipeline` takes grid values. -/
theorem src_boxConv_isFixed (p : ℕ) :
    ∀ (D : ℕ) (t : Fin D → ℕ) (inst : ∀ i, NeZero (t i))
      (f g : ((i : Fin D) → ZMod (t i)) → ℂ) (x : (i : Fin D) → ZMod (t i)),
      IsFixed p (Pipeline.boxConv p D t inst f g x)
  | 0, _, _, _, _, _ => ⟨0, 0, by apply Complex.ext <;> simp [Pipeline.boxConv]⟩
  | _ + 1, _, _, _, _, _ => isFixed_rhoC _ _

/-! ### Margins -/

section Margins

open IntegerMultBounds.MathlibTM2.Mult.Pipeline IntegerMultBounds.MathlibTM2.Mult.Sizes
open IntegerMultBounds.Resampling.WeightTable (tableA tables_ok)

variable {n : ℕ}

/-- `Ã` on one axis approximates `resampA` within `p²`. -/
theorem src_lineA_approx (h : Big n) (i : Fin (d n)) :
    ApproxMap (p n) (lineA n i) (resampA (s n i) (t n i) (alpha n : ℝ)) ((p n : ℝ) ^ 2) := by
  have hα2 := two_le_alpha h.1
  have hαR : (2 : ℝ) ≤ alpha n := by exact_mod_cast hα2
  have hp := h.thirteen_le_p
  have hαp : alpha n ^ 2 ≤ p n := h.alpha_sq_le_p
  obtain ⟨hm, hm1, hmp⟩ := windowA_spec (alpha_sq_lt_p h)
  have htab := (tables_ok (s n i) (t n i) (alpha n) (p n) (h.good.lt i) hp hα2 hαp).1
  have hAx := IntegerMultBounds.Resampling.TabledMaps.approxMap_resampANumW (s := s n i)
    (t := t n i) (α := (alpha n : ℝ)) (by linarith) (by exact_mod_cast hαp) hm hm1 _
    (fun k j => IntegerMultBounds.Resampling.TabledMaps.tol_of_int (p n) _ _ (htab k j))
  have hε : errA (windowA (p n) (alpha n)) < (p n : ℝ) ^ 2 := errA_lt_sq' hmp (by omega)
  unfold errA at hε
  exact fun v hv => (hAx v hv).trans hε.le

/-- **The disk margins of the pipeline's source transform** on inputs of norm at most `1/2`. -/
theorem src_margins (h : Big n) (hsmall : 2 * d n * p n ^ 2 ≤ T n * logT n)
    (hEs : 9 * (2 : ℝ) ^ gamma n * T n * logT n ≤ 2 ^ p n / 100)
    {v : ((i : Fin (d n)) → ZMod (s n i)) → ℂ} (hv : ‖v‖ ≤ 1 / 2) :
    ‖tensorZR (d n) (s n) (t n) (lineA n) v‖ ≤ 6 / 10 ∧
      ‖fun j => rhoC (p n) (starRingEnd ℂ (chirpKernel n j) *
        tensorZR (d n) (s n) (t n) (lineA n) v j)‖ ≤ 6 / 10 ∧
      ‖convBox n (chirpKernel n) (fun j => rhoC (p n) (starRingEnd ℂ (chirpKernel n j) *
        tensorZR (d n) (s n) (t n) (lineA n) v j))‖ ≤ 701 / 1000 ∧
      ‖bluesteinApproxD (p n) (chirpKernel n) (convBox n)
        (tensorZR (d n) (s n) (t n) (lineA n) v)‖ ≤ 701 / 1000 := by
  have hd1 := h.one_le_d
  have hpT : ∏ i, t n i = T n := prod_t hd1
  have hα1 : (1 : ℝ) ≤ alpha n := by
    have := two_le_alpha h.1; exact_mod_cast (show 1 ≤ alpha n by omega)
  have hsm : 2 * d n * p n ^ 2 ≤ (∏ i, t n i) * logT n := by rw [hpT]; exact hsmall
  have hEs' : 9 * (2 : ℝ) ^ (d n * (2 * ⌈(alpha n : ℝ) ^ 2⌉₊ + 2)) *
      ((∏ i, t n i : ℕ) : ℝ) * logT n ≤ 2 ^ p n / 100 := by
    rw [hpT]
    refine le_trans ?_ hEs
    have hle : d n * (2 * ⌈(alpha n : ℝ) ^ 2⌉₊ + 2) ≤ gamma n := by
      rw [gamma_eq_ceil]; exact Nat.mul_le_mul_left _ (by omega)
    have : (2 : ℝ) ^ (d n * (2 * ⌈(alpha n : ℝ) ^ 2⌉₊ + 2)) ≤ 2 ^ gamma n :=
      pow_le_pow_right₀ (by norm_num) hle
    have h0 : (0 : ℝ) ≤ T n * logT n := by positivity
    nlinarith
  exact SourceErr.sourceApprox_margins (fun i => opNorm_resampA_le hα1) (src_lineA_approx h)
    (fun i u hu => pre_lineA_ball h i u hu)
    (fun j => (Chirp.chirpProd_ha'_explicit (t n) (s n) (p n) j).2)
    (fun f g hf hg => (convBox_spec h hsmall hEs f g hf hg).2) hsm hEs' hv

end Margins

end

end IntegerMultBounds.MathlibTM2.Fast.Src
