module

public import IntegerMultBounds.MathlibTM2.Fast.SrcPhase

/-!
# The source transform `F'` and its opposite as machines

Two fixed programs over the machine constants `M : SrcMach t₀ T Q` (`Fast/SrcPhase`) and the
transform programs `fwdP`, `oppP` of `Fast/ConvSpec`:

* `srcP M fwdP oppP` computes `Pipeline.srcMap n = F̃ ∘ Φ`: from the coefficient stream of `u`
  on `c .str` it pushes the padded stream of `srcMap n u` on the source box onto `x .sb`.
* `oppP' M fwdP oppP` computes `Pipeline.oppMap n = Φ⁻¹ ∘ F̃⁺`: from the padded stream of `y` on
  `x .sb` it leaves the coefficient stream of `oppMap n y` on `c .str`.

Both run `srcCore = srcPA; srcPK; srcPC1; srcPV; srcPC2; srcPB; srcPG`, the source transform
`F̃ = 2^γ · B̃₀ ∘ C̃ ∘ Ã` on padded boxes (`srcCore_runs`). `srcP` puts the CRT layout
`crtForward` (`Fast/CRTMachine.crtForward_runs`) and a transfer in front; `oppP'` conjugates
before and after (`conj ∘ F̃ ∘ conj`, the conjugation automaton of `PointStage.cst_conj_runs`
and a reversal) and ends with `crtInverse` (`crtInverse_runs`).

## Formats

* Coefficient stream (`srcCoef p S u`, `S = ∏ s_i`): the numerators at scale `2^p` of
  `u 0, …, u (S - 1)`, each `w` pair symbols (`cstream`).
* Padded box (`srcPad p s t f`): the numerators of `f` at the addresses of `∏ [0, t_i)` below
  `s`, zero elsewhere, axis `0` most significant. The CRT box with widths `a j = log₂ t_j` is
  this stream (`src_crt_fwd`, `src_crt_inv_box`); the resampling, chirp and convolution stages
  read it without data movement.

## Hypotheses

The results keep as hypotheses only:
* the transform contracts `SynFwdSpec`/`SynOppSpec` of `fwdP`, `oppP` on `v .io` with the record
  order `π` (`hπ`) and bounds `cF`, `cO`, their precondition `Pre` framed by the layout
  (`SrcFramed`), `Pre → PreF`, `Pre → PreO`;
* the parameter registers (`SrcBase`, `SrcCrtBase`): the `Ã` records `preRecsA` on `a (.c .out)`
  and the `B̃₀` records `preRecsB` on `b (.inl .prm)` over base files `V₀`, `σ₀` (`PreBaseA`,
  `BandBase`), the axis counters (`d - 1` symbols), the chirp loader's unary parameters and idle
  table registers (`SrcKerBase`), the stored axis descriptions `ldcBlocks t`, `ldcBlocks s` on
  `x .tSp`, `x .sSp`, the twist tables `tblTwistStream` and the shift counters of the
  convolution (`SrcConvBase`), the product registers ready for `w` and `p + 1` (`SrcMulBase`),
  the unary `γ`, `w - γ`, `ℓ` (`SrcXBase`), and the CRT axis lists, packed bounds, masks and zero
  record (`SrcCrtBase`); the work registers these structures name are empty;
* one width `w`: `p + chirpGuard d + 3 ≤ w < W`, and the word-size conditions of the table
  machines (`hWA`, `hWB`, `hWs`, `hWk`); `Σ aᵢ ≤ w` and `γ ≤ w` follow (`src_sum_cvAx_le`,
  `src_gamma_le`);
* `Big n`, `2 d p² ≤ T log₂ T` (`hsmall`) and `9 · 2^γ T log₂ T ≤ 2^p / 100` (`hEs`), the size
  conditions of `Pipeline.source_approx`;
* the input disk bound `‖u‖ ≤ 1/2` (resp. `‖y‖ ≤ 1/2`), grid values at scale `2^p`.

## Results

* `srcCore_runs`: `x .sb` gains `srcPad p s t (sourceApprox s t p γ (lineA n) (lineB n)
  (chirpKernel n) (convBox n) v)`; the resampling families end configured for axis `0`
  (`preCfgA`, `bandCfgB`), every other register as it began.
* `srcP_runs`, `srcOpp_runs`: the two transforms, with the costs `srcPCost`, `oppPCost`.
* `SrcBase.next`: with the records of several runs stacked on the parameter registers, the file
  after a run is again a file between runs (`src_preBaseA_load`, `BandBase.load`), so
  `srcP`, `srcP`, `oppP'` run in sequence on one register file.

## Costs and `Cost/Total.totBound`

`srcCoreCost` is the sum of the phase costs: `srcCostA` and `srcCostB` (`Ã`, `B̃₀` with their
loaders and table machines: `d` axis passes of `O(T p^{1/2} α)` products, the term `totResamp`);
`srcCostK` (the kernel: `d` table products over the box, `O(d T M(p))`, inside `totResamp`);
`srcCostV` (the convolution: the transforms `2 cF + cO` and the ring products, the term
`totConv`; its three twists `O(T M(p))`); the two chirp products `srcCostC` and the scale,
`O(T M(p))`, the term `T · M(p)` of the transform (`totBound` has `3 (totResamp + totConv +
T M(p))` for the three transforms `F'`, `F'`, `G'`); transfers and clears `O(T w)`. `crtCost`
(forward or inverse layout) is the term `totCRT`; the pipeline runs three layouts (two forward,
one inverse) against `2 totCRT` in `totBound`, a factor `3/2` inside the constant `C`. The
conjugations of `oppP'` are `O(T w)`.
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2.Fast.Src

open IntegerMultBounds IntegerMultBounds.NLogN IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.ResampA IntegerMultBounds.MathlibTM2.Fast.ChirpSt IntegerMultBounds.MathlibTM2.Fast.ConvSt
open IntegerMultBounds.MathlibTM2.Mult IntegerMultBounds.MathlibTM2.Mult.Sizes IntegerMultBounds.MathlibTM2.Mult.Pipeline
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
open scoped Function

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

noncomputable section

variable {t₀ T Q : ℕ}

/-! ### Size facts -/

section Sizes

variable {n : ℕ}

lemma srcHd0 (h : Big n) : 0 < d n := h.one_le_d

/-- `Σ aᵢ ≤ p` for the convolution's record axes `aᵢ = log₂ t_i`, `i < d - 1`. -/
lemma src_sum_cvAx_le (h : Big n) : (List.ofFn (cvAx (t n))).sum ≤ p n := by
  have hM := cv_M_mul_r h
  have hr : 1 ≤ r n := Nat.one_le_two_pow
  have h1 : 2 ^ (List.ofFn (cvAx (t n))).sum ≤ 2 ^ logT n := by
    have : cvM (cvAx (t n)) ≤ cvM (cvAx (t n)) * r n := Nat.le_mul_of_pos_right _ hr
    rw [hM] at this
    exact this
  have h2 := (Nat.pow_le_pow_iff_right (by norm_num)).1 h1
  have h3 := h.logT_bounds.2
  unfold p
  omega

/-- `γ ≤ p`. -/
lemma src_gamma_le (h : Big n) : gamma n ≤ p n := by
  have := h.four_gamma_le_b
  unfold p
  omega

/-- The widths of the CRT box: `t j = 2^{a j}`. -/
def srcAx (n : ℕ) : Fin (d n) → ℕ := fun j => Nat.log 2 (t n j)

lemma src_t_eq (n : ℕ) (j : Fin (d n)) : t n j = 2 ^ srcAx n j := t_pow_log n j

lemma src_ax_bounds (j : Fin (d n)) : ℓ n - 1 ≤ srcAx n j ∧ srcAx n j ≤ ℓ n := by
  unfold srcAx
  rcases pre_log_t (n := n) j with e | e <;> rw [e] <;> omega

lemma src_kernel_ok (n : ℕ) (j : (i : Fin (d n)) → ZMod (t n i)) :
    IsFixed (p n) (chirpKernel n j) ∧ ‖chirpKernel n j‖ ≤ 1 :=
  ⟨(Chirp.chirpProd_spec (t n) (s n) (Chirp.sixteen_mul_le_chirpGuard (d n)) j).1,
    (Chirp.chirpProd_spec (t n) (s n) (Chirp.sixteen_mul_le_chirpGuard (d n)) j).2.1⟩

end Sizes

/-! ### The register files between runs -/

section Bases

variable {K : ℕ}

/-- The chirp kernel family between runs: the chirp stage's registers at rest for `w` and
`q = p + g` (`CstBase`, `g = chirpGuard d`), `d - 1` symbols on the axis counter, the unary `p`,
`g`, `w` on `pU`, `gU`, `wU`, the table machine idle with `W` symbols on `wr` and `w` on `wn`,
the kernel register and the description registers empty. -/
structure SrcKerBase {A : ℕ} (ρ : CsR ldcX → List (Fin (A + 4))) (n w W : ℕ) : Prop where
  base : CstBase ρ w (p n) (Chirp.chirpGuard (d n))
  ax : (ρ .ax).length + 1 = d n
  kr : ρ .kr = []
  tS : ρ (.x .tS) = []
  sS : ρ (.x .sS) = []
  tU : ρ (.x .tU) = []
  sU : ρ (.x .sU) = []
  pU : (ρ (.x .pU)).length = p n
  gU : (ρ (.x .gU)).length = Chirp.chirpGuard (d n)
  wU : (ρ (.x .wU)).length = w
  wr : (ρ (.x (.tbl .wr))).length = W
  wn : (ρ (.x (.tbl .wn))).length = w
  tbl : ∀ r, r ≠ .wr → r ≠ .wn → ρ (.x (.tbl r)) = []

/-- The registers of the first chirp product: ready for `w` and the shift `p + 1`, operands and
result empty. -/
structure SrcMulBase {A : ℕ} (ρ : CR → List (Fin (A + 4))) (n w : ℕ) : Prop where
  ready : Ready ρ w (p n + 1)
  xs : ρ .xs = []
  ys : ρ .ys = []
  xsv : ρ .xsv = []
  ysv : ρ .ysv = []
  acc : ρ .acc = []
  out : ρ .out = []

/-- The transfer registers: spares empty, `γ`, `w - γ`, `ℓ` symbols on `gS`, `gR`, `lU`, the
axis descriptions `ldcBlocks t`, `ldcBlocks s` on `tSp`, `sSp`. -/
structure SrcXBase {A : ℕ} (ρ : SrcX → List (Fin (A + 4))) (n w : ℕ) : Prop where
  tr : ρ .tr = []
  cA : ρ .cA = []
  cB : ρ .cB = []
  c1 : ρ .c1 = []
  c2 : ρ .c2 = []
  gT : ρ .gT = []
  gU : ρ .gU = []
  gD : ρ .gD = []
  gS : (ρ .gS).length = gamma n
  gR : (ρ .gR).length = w - gamma n
  lU : (ρ .lU).length = ℓ n
  tSp : ρ .tSp = ldcBlocks (List.ofFn (t n))
  sSp : ρ .sSp = ldcBlocks (List.ofFn (s n))

/-- **The register file between runs.** The `Ã` family is `rsaWith V₀ _ axsA []` (any box
stream) over a base file `V₀` with the records of the pipeline followed by `restA` on `c .out`;
the `B̃₀` family is `rsbWith σ₀ [] axsB []` with the records followed by `restB` on `prm`; the
kernel, convolution, product and transfer families as in `SrcKerBase`, `SrcConvBase`,
`SrcMulBase`, `SrcXBase`. -/
structure SrcBase (M : SrcMach t₀ T Q) (E : SrcF t₀ (prime + K)) (n w W : ℕ) (hd0 : 0 < d n)
    (V₀ : RsaV (RsaX t₀) (prime + K)) (σ₀ : RsbR ⊕ RsbX t₀ → List (Fin (prime + K + 4)))
    (restA restB axsA axsB : List (Fin (prime + K + 4))) : Prop where
  a : ∀ r, r ≠ .ln → E.a r = (rsaWith V₀ [] axsA []).get r
  aBase : PreBaseA V₀ w M.hd
  aOut : V₀.cr .out = preRecsA n W hd0 0 ++ restA
  aAx : axsA.length = d n - 1
  b : E.b = rsbWith σ₀ [] axsB []
  bBase : BandBase σ₀ w M.hd
  bOut : σ₀ (.inl .prm) = preRecsB n W hd0 0 ++ restB
  bAx : axsB.length = d n - 1
  k : SrcKerBase E.k n w W
  v : SrcConvBase E.v n w
  m : SrcMulBase E.m n w
  x : SrcXBase E.x n w

/-- The CRT family: the axis lists of widths `a = srcAx n`, lengths `s` and offsets `μ` in the
forward format, the packed bounds and masks, the zero record `csyms w 0`, every other CRT
register and the interchange bank empty. -/
structure SrcCrtBase {A : ℕ} (ρ : CrtReg → List (Fin (A + 4)))
    (ρb : Fin (swapT 6) → List (Fin (A + 4))) (n w : ℕ) : Prop where
  wT : ρ .wT = crtEnts ((crtRevAx (d n)).map (srcAx n))
  sT : ρ .sT = crtEnts ((crtRevAx (d n)).map (s n))
  mT : ρ .mT = crtEnts ((crtRevAx (d n)).map fun j => (crtMu (s n) (s_pairwise n) j :
    ZMod (s n j)).val)
  sig : ρ .sig = binSyms (crtPre (srcAx n) (d n)) (crtSig (srcAx n) (s n) (d n))
  msk : ρ .msk = binSyms (crtPre (srcAx n) (d n)) (crtMask (srcAx n) (d n))
  zr : ρ .zr = csyms A w 0
  rest : ∀ x ∈ crtRestEmpty, ρ x = []
  bank : ∀ j, ρb j = []

lemma SrcCrtBase.upd_str {A : ℕ} {ρ : CrtReg → List (Fin (A + 4))}
    {ρb : Fin (swapT 6) → List (Fin (A + 4))} {n w : ℕ} (h : SrcCrtBase ρ ρb n w)
    (l : List (Fin (A + 4))) : SrcCrtBase (Function.update ρ .str l) ρb n w :=
  ⟨by rw [Function.update_of_ne (by decide)]; exact h.wT,
    by rw [Function.update_of_ne (by decide)]; exact h.sT,
    by rw [Function.update_of_ne (by decide)]; exact h.mT,
    by rw [Function.update_of_ne (by decide)]; exact h.sig,
    by rw [Function.update_of_ne (by decide)]; exact h.msk,
    by rw [Function.update_of_ne (by decide)]; exact h.zr,
    fun x hx => by
      rw [Function.update_of_ne (by rintro rfl; revert hx; decide)]
      exact h.rest x hx,
    h.bank⟩

lemma src_rsaWith_get_ne {A : ℕ} (V : RsaV (RsaX t₀) A) (l l' a a' : List (Fin (A + 4)))
    {r : RsaR (RsaX t₀)} (hr : r ≠ .ln) : (rsaWith V l a a').get r = (rsaWith V l' a a').get r := by
  cases r <;> first | rfl | exact absurd rfl hr

lemma src_rsaWith_ln {A : ℕ} (V : RsaV (RsaX t₀) A) (l l' a a' : List (Fin (A + 4))) :
    { rsaWith V l a a' with ln := l' } = rsaWith V l' a a' := rfl

lemma src_rsbWith_get_src {A : ℕ} (σ : RsbR ⊕ RsbX t₀ → List (Fin (A + 4)))
    (l a a' : List (Fin (A + 4))) : rsbWith σ l a a' (.inl .src) = l := by
  simp only [rsbWith, Sum.elim_inl, Function.update_self]

lemma SrcBase.a_eq {M : SrcMach t₀ T Q} {E : SrcF t₀ (prime + K)} {n w W : ℕ} {hd0 : 0 < d n}
    {V₀ : RsaV (RsaX t₀) (prime + K)} {σ₀ : RsbR ⊕ RsbX t₀ → List (Fin (prime + K + 4))}
    {restA restB axsA axsB : List (Fin (prime + K + 4))}
    (h : SrcBase M E n w W hd0 V₀ σ₀ restA restB axsA axsB) :
    E.a = (rsaWith V₀ (E.a .ln) axsA []).get := by
  funext r
  by_cases hr : r = .ln
  · subst hr; rfl
  · rw [h.a r hr]; exact src_rsaWith_get_ne V₀ _ _ _ _ hr

end Bases

/-! ### The source transform on padded boxes -/

section Core

variable {K : ℕ} {U P : Type} {body : P → Pr P T Q (prime + K) U}

/-- **The source transform on padded boxes**: `Ã`, the kernel, the first chirp product, the
convolution, the second chirp product, `B̃₀`, the scale by `2^γ`. -/
def srcCore (M : SrcMach t₀ T Q) (fwdP oppP : Pr P T Q (prime + K) U) :
    Pr P T Q (prime + K) U :=
  .seq (srcPA M) <| .seq (srcPK M) <| .seq (srcPC1 M) <| .seq (srcPV M fwdP oppP) <|
  .seq (srcPC2 M) <| .seq (srcPB M) (srcPG M)

/-- The cost of `srcCore`, phase by phase. -/
def srcCoreCost (M : SrcMach t₀ T Q) (n w W cF cO : ℕ) (hd0 : 0 < d n)
    (V₀ : RsaV (RsaX t₀) (prime + K)) (σ₀ : RsbR ⊕ RsbX t₀ → List (Fin (prime + K + 4)))
    (restA restB : List (Fin (prime + K + 4))) : ℕ :=
  srcCostA M n w W hd0 V₀ restA + srcCostK (K := K) (T := T) n w W +
    srcCostC T w (∏ i, t n i) + srcCostV T n w cF cO +
    (srcCostC T w (∏ i, t n i) + (2 * ((∏ i, t n i) * w) + 2)) +
    (4 * ((∏ i, t n i) * w) + 4 + srcCostB M n w W hd0 σ₀ restB) +
    ((∏ i, t n i) * (6 * w + 4 * gamma n + 14) + 4)

/-- **The source transform `F̃` on padded boxes.** From the register file between runs with the
padded stream of `v` (grid values at scale `2^p`, `‖v‖ ≤ 1/2`) on `a .ln`, `srcCore` pushes the
padded stream of `sourceApprox s t p γ (lineA n) (lineB n) (chirpKernel n) (convBox n) v` onto
`x .sb`; the resampling families end configured for axis `0` with the box registers empty,
every other register as it began. -/
theorem srcCore_runs (M : SrcMach t₀ T Q) (hA : 96 ≤ prime + K) {n : ℕ} (hbig : Big n)
    (hsmall : 2 * d n * p n ^ 2 ≤ Sizes.T n * logT n)
    (hEs : 9 * (2 : ℝ) ^ gamma n * Sizes.T n * logT n ≤ 2 ^ p n / 100)
    {fwdP oppP : Pr P T Q (prime + K) U} {Pre PreF PreO : Stacks T (prime + K) → Prop}
    {w W cF cO : ℕ} {π : ℕ → ℕ}
    (hF : SynFwdSpec body fwdP (M.rg (.v .io)) PreF w (p n) (ℓ n) (cvAx (t n)) π cF)
    (hO : SynOppSpec body oppP (M.rg (.v .io)) PreO w (p n) (ℓ n) (cvAx (t n)) π cO)
    (hPF : ∀ S, Pre S → PreF S) (hPO : ∀ S, Pre S → PreO S)
    (hπ : ∀ m < cvM (cvAx (t n)), π m < cvM (cvAx (t n))) (hP : SrcFramed M.rg Pre)
    (hw : p n + Chirp.chirpGuard (d n) + 3 ≤ w) (hwW : w < W)
    (hWA : ∀ i : Fin (d n), alpha n ^ 2 * ((s n i + t n i) * (windowA (p n) (alpha n) + 1)) ^ 2 *
      2 ^ (13 * p n + 8) < 2 ^ W)
(hWB : 9 * p n + 2 ≤ w ∧ ∀ i : Fin (d n), alpha n ^ 2 * ((s n i + t n i) *
      (8 * FastB0.fastWindow (p n) (alpha n) + 1)) ^ 2 * 2 ^ (65 * p n + 8) < 2 ^ W)
    (hWs : ∀ k, s n k * t n k * t n k < 2 ^ W)
    (hWk : ∀ k, 8 * (p n + Chirp.chirpGuard (d n)) + Nat.size (t n k) + 80 ≤ W)
    {V₀ : RsaV (RsaX t₀) (prime + K)} {σ₀ : RsbR ⊕ RsbX t₀ → List (Fin (prime + K + 4))}
    {restA restB axsA axsB : List (Fin (prime + K + 4))} (E : SrcF t₀ (prime + K))
    (hE : SrcBase M E n w W (srcHd0 hbig) V₀ σ₀ restA restB axsA axsB)
    (v : ((i : Fin (d n)) → ZMod (s n i)) → ℂ) (hv : ‖v‖ ≤ 1 / 2)
    (hvf : ∀ x, IsFixed (p n) (v x))
    (hln : E.a .ln = cstream (prime + K) w (srcPad (p n) (s n) (t n) v)) :
    SrcRuns body M.rg M.ι Pre (srcCore M fwdP oppP) E.get
      { E with a := (rsaWith (preCfgA V₀ M.hd n w W (srcHd0 hbig) restA (d n - 1)) [] axsA []).get,
               b := rsbWith (bandCfgB σ₀ M.hd n w W (srcHd0 hbig) restB (d n - 1)) [] axsB [],
               x := (Function.update E.x .sb (cstream (prime + K) w (srcPad (p n) (s n) (t n)
                 (SourceErr.sourceApprox (s n) (t n) (p n) (gamma n) (lineA n) (lineB n)
                   (chirpKernel n) (convBox n) v)) ++ E.x .sb)) }.get
      (srcCoreCost M n w W cF cO (srcHd0 hbig) V₀ σ₀ restA restB) := by
  have hdisj := M.hdisj
  have hd0 := srcHd0 hbig
  have hp13 := hbig.thirteen_le_p
  obtain ⟨m1, m2, m3, m4⟩ := src_margins hbig hsmall hEs hv
  set a' := chirpKernel n with ha'
  set x₁ := tensorZR (d n) (s n) (t n) (lineA n) v with hx₁
  set x₀ := cstChirpProd (t n) (p n) a' x₁ with hx₀
  set y₀ := convBox n a' x₀ with hy₀
  set c₁ := cstChirpProd (t n) (p n) a' y₀ with hc₁
  have hc₁' : c₁ = bluesteinApproxD (p n) a' (convBox n) x₁ := rfl
  have ha1 : ‖a'‖ ≤ 1 := (pi_norm_le_iff_of_nonneg zero_le_one).2 fun j => (src_kernel_ok n j).2
  have hfit_a : ∀ k, Fits w (numer (p n) (a' (cstCast (t n) k))) := fun k =>
    cst_fits_numer (k := 1) (by
      have := (src_kernel_ok n (cstCast (t n) k)).2; rw [pow_one]; linarith) (by omega)
  have hb := hE.k
  have hvv := hE.v
  have hm := hE.m
  have hx := hE.x
  -- phase `Ã`
  obtain ⟨hfix₁, sA⟩ := srcA_runs (body := body) M hA hbig hd0 (by omega) hwW.le hWA V₀ hE.aBase
    restA hE.aOut axsA hE.aAx v (fun x => (norm_le_pi_norm v x).trans (by linarith)) hvf E
    (by rw [hE.a_eq, hln])
  set X₁ := cstream (prime + K) w (cstNumBox (p n + 1) (t n) x₁) with hX₁
  set E₁ : SrcF t₀ (prime + K) :=
    { E with a := (rsaWith (preCfgA V₀ M.hd n w W hd0 restA (d n - 1)) X₁ axsA []).get } with hE₁
  -- the kernel
  have sK := srcK_runs (body := body) M hA n hbig.one_le_d (by omega) hwW hWs hWk E₁ hb.base hb.ax
    hb.tS hb.sS hb.tU hb.sU hb.pU hb.gU hb.wU hb.wr hb.wn hb.tbl hx.tSp hx.sSp hx.c1 hx.c2
  set KER := cstream (prime + K) w (cstNumBox (p n) (t n) a') with hKER
  rw [show E₁.k .kr = [] from hb.kr, List.append_nil] at sK
  set E₂ : SrcF t₀ (prime + K) := { E₁ with k := Function.update E₁.k .kr KER } with hE₂
  -- the first chirp product
  have sC1 := srcC1_runs (body := body) M hA (by omega) (by omega) (t n) a' x₁
    (fun k => (src_kernel_ok n _).1) hfix₁ hfit_a
    (fun k => cst_fits_numer (k := 0) (by
      have := (norm_le_pi_norm x₁ (cstCast (t n) k)).trans m1; rw [pow_zero]; linarith)
      (by omega))
    E₂ rfl (by simp [hE₂, hKER]) hm.ready hm.xs hm.ys hm.xsv hm.ysv hm.acc hm.out hx.tr hx.cA hx.cB
    hx.c1 hx.c2
  set X₀ := cstream (prime + K) w (cstNumBox (p n) (t n) x₀) with hX₀
  set E₃ : SrcF t₀ (prime + K) :=
    { E₂ with a := Function.update E₂.a .ln [], m := Function.update E₂.m .out X₀ } with hE₃
  -- the convolution
  have sV := srcV_runs (body := body) M hA hbig hEs hF hO hPF hPO hπ hP (by omega)
    ((src_sum_cvAx_le hbig).trans (by omega)) a' x₀ (fun y => (src_kernel_ok n y).1)
    (fun y => isFixed_rhoC _ _) ha1 (m2.trans (by norm_num)) E₃ hvv (by simp [hE₃, hE₂, hKER])
    (by simp [hE₃, hX₀]) hb.pU hx.lU hb.wU hx.tr hx.c1 hx.c2
  set Y₀ := cstream (prime + K) w (cstNumBox (p n) (t n) y₀) with hY₀
  set E₄ : SrcF t₀ (prime + K) :=
    { E₃ with m := Function.update E₃.m .out [], v := Function.update E₃.v .fo Y₀ } with hE₄
  -- the second chirp product
  have sC2 := srcC2_runs (body := body) M hA (by omega) (by omega) (t n) a' y₀
    (fun k => (src_kernel_ok n _).1) (fun k => src_boxConv_isFixed _ _ _ _ _ _ _) hfit_a
    (fun k => cst_fits_numer (k := 0) (by
      have := (norm_le_pi_norm y₀ (cstCast (t n) k)).trans m3; rw [pow_zero]; linarith)
      (by omega))
    E₄ (by simp [hE₄, hY₀]) (by simp [hE₄, hE₃, hE₂, hKER]) (cst_ready_of_eq hvv.ready fun y h1 h2 h3 h4 h5 h6 =>
      by simp [hE₄, hE₃, hE₂, hE₁])
    (by simp [hE₄, hE₃, hE₂, hE₁, hvv.cmxs]) (by simp [hE₄, hE₃, hE₂, hE₁, hvv.cmys])
    (by simp [hE₄, hE₃, hE₂, hE₁, hvv.cmxsv]) (by simp [hE₄, hE₃, hE₂, hE₁, hvv.cmysv])
    (by simp [hE₄, hE₃, hE₂, hE₁, hvv.cmacc]) (by simp [hE₄, hE₃, hE₂, hE₁, hvv.cmout])
    hx.tr hx.cA hx.cB hx.c1 hx.c2
  set C₁ := cstream (prime + K) w (cstNumBox (p n) (t n) c₁) with hC₁
  set E₅ : SrcF t₀ (prime + K) :=
    { E₄ with k := Function.update E₄.k .kr [],
              v := (Function.update (Function.update E₄.v .fo []) (.cm .out) C₁) } with hE₅
  -- `B̃₀`
  obtain ⟨hfixz, sB⟩ := srcB_runs (body := body) M hA hbig hd0 hWB.1 hwW.le hWB.2 σ₀ hE.bBase
    restB hE.bOut axsB hE.bAx c₁ (fun y => isFixed_rhoC _ _)
    (fun y => (norm_le_pi_norm c₁ y).trans (m4.trans (by norm_num))) E₅ (by simp [hE₅, hE₄,
      hE₃, hE₂, hE₁, hE.b]) (by simp [hE₅, hC₁]) hx.tr
  set z := tensorZR (d n) (t n) (s n) (lineB n) c₁ with hz
  set Z := cstream (prime + K) w (srcPad (p n) (s n) (t n) z) with hZ
  set E₆ : SrcF t₀ (prime + K) :=
    { E₅ with v := Function.update E₅.v (.cm .out) [],
              b := rsbWith (bandCfgB σ₀ M.hd n w W hd0 restB (d n - 1)) Z axsB [] } with hE₆
  -- the scale
  have sG := srcG_runs (body := body) M (q := p n) (γ := gamma n) (w := w) (s n) (t n)
    (by omega) ((src_gamma_le hbig).trans (by omega)) z hfixz E₆
    (by simp only [hE₆, src_rsbWith_get_src, hZ])
    (by simp [hE₆, hE₅, hE₄, hE₃, hE₂, hE₁, hx.gS]) (by simp [hE₆, hE₅, hE₄, hE₃, hE₂, hE₁, hx.gR])
    (by simp [hE₆, hE₅, hE₄, hE₃, hE₂, hE₁, hx.gT]) (by simp [hE₆, hE₅, hE₄, hE₃, hE₂, hE₁, hx.gU])
    (by simp [hE₆, hE₅, hE₄, hE₃, hE₂, hE₁, hx.gD])
  refine ((SrcRuns.of_rsa sA).seq hdisj hP ((SrcRuns.of_rsa sK).seq hdisj hP
    ((SrcRuns.of_rsa sC1).seq hdisj hP (sV.seq hdisj hP ((SrcRuns.of_rsa sC2).seq hdisj hP
    ((SrcRuns.of_rsa sB).seq hdisj hP (SrcRuns.of_rsa sG))))))).congr ?_ |>.mono (le_of_eq ?_)
  swap
  · simp only [srcCoreCost]
    ring
  congr 1
  refine SrcF.ext ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · simp only [hE₆, hE₅, hE₄, hE₃, hE₂, hE₁, RsaV.upd_ln, src_rsaWith_ln]
  · simp only [hE₆, hZ, src_rsbWith_src]
  · simp only [hE₆, hE₅, hE₄, hE₃, hE₂, hE₁, Function.update_idem]
    exact Function.update_eq_self_iff.2 hb.kr.symm
  · simp only [hE₆, hE₅, hE₄, hE₃, hE₂, hE₁, Function.update_idem]
    have e1 : Function.update E.v .fo [] = E.v := Function.update_eq_self_iff.2 hvv.fo.symm
    rw [e1]
    exact Function.update_eq_self_iff.2 hvv.cmout.symm
  · rfl
  · rfl
  · simp only [hE₆, hE₅, hE₄, hE₃, hE₂, hE₁, Function.update_idem]
    exact Function.update_eq_self_iff.2 hm.out.symm
  · rfl

end Core

/-! ### Register files along a run -/

section Mono

variable {K : ℕ}

lemma SrcXBase.of_eq {A : ℕ} {ρ ρ' : SrcX → List (Fin (A + 4))} {n w : ℕ} (h : SrcXBase ρ n w)
    (he : ∀ j, j ≠ .sb → ρ' j = ρ j) : SrcXBase ρ' n w := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rwa [he _ (by decide)]

/-- `SrcBase` reads neither the box register `a .ln`, the result register `x .sb` nor the CRT
family. -/
lemma SrcBase.of_eq {M : SrcMach t₀ T Q} {E E' : SrcF t₀ (prime + K)} {n w W : ℕ}
    {hd0 : 0 < d n} {V₀ : RsaV (RsaX t₀) (prime + K)}
    {σ₀ : RsbR ⊕ RsbX t₀ → List (Fin (prime + K + 4))}
    {restA restB axsA axsB : List (Fin (prime + K + 4))}
    (h : SrcBase M E n w W hd0 V₀ σ₀ restA restB axsA axsB)
    (ha : ∀ r, r ≠ .ln → E'.a r = E.a r) (hb : E'.b = E.b) (hk : E'.k = E.k) (hv : E'.v = E.v)
    (hm : E'.m = E.m) (hx : ∀ j, j ≠ .sb → E'.x j = E.x j) :
    SrcBase M E' n w W hd0 V₀ σ₀ restA restB axsA axsB :=
  ⟨fun r hr => (ha r hr).trans (h.a r hr), h.aBase, h.aOut, h.aAx, hb.trans h.b, h.bBase,
    h.bOut, h.bAx, hk ▸ h.k, hv ▸ h.v, hm ▸ h.m, h.x.of_eq hx⟩

end Mono

/-! ### Conjugation and the CRT layouts -/

section Edges

variable {K : ℕ} {U P : Type} {body : P → Pr P T Q (prime + K) U}

/-- Conjugate the stream on `src` onto `dst` in forward order: the conjugation automaton onto
`x .cB` (reversed; counter `m .wn`, state slot and spare `m .tmp`), then a reversal onto
`dst`. -/
def srcConj (M : SrcMach t₀ T Q) (src dst : SrcR t₀) : Pr P T Q (prime + K) U :=
  .seq (autoWords ![M.rg src] ![M.rg (.x .cB)] (M.rg (.m .tmp)) (M.rg (.m .wn)) (M.rg (.m .tmp))
    (gaussAuto (prime + K) ![![(0, -1)]] 1 true))
  (moveR (M.rg (.x .cB)) (M.rg dst) id)

/-- **Conjugation of a stream, forward order.** -/
theorem src_conj_runs (M : SrcMach t₀ T Q) (hA : 96 ≤ prime + K) {w : ℕ} (hw : 1 ≤ w)
    {src dst : SrcR t₀} (hd : [src, .x .cB, .m .wn, .m .tmp].Nodup) (hsd : src ≠ dst)
    (hdB : dst ≠ .x .cB) (ρ : SrcR t₀ → List (Fin (prime + K + 4))) (l : List GaussianInt)
    (hsrc : ρ src = cstream (prime + K) w l) (hcB : ρ (.x .cB) = [])
    (hctr : (ρ (.m .wn)).length = w) (htmp : ρ (.m .tmp) = []) :
    RsaRuns body M.rg M.ι (srcConj M src dst) ρ
      (Function.update (Function.update ρ src []) dst
        (cstream (prime + K) w (l.map star) ++ ρ dst))
      (l.length * (5 * w + 6) + 2 + (2 * (l.length * w) + 2)) := by
  have hd' := hd
  regs_ne hd'
  have h1 := cst_conj_runs (body := body) (ι := M.ι) M.hrg M.hdisj (src := src) (out := .x .cB)
    (st := .m .tmp) (ctr := .m .wn) (tmp := .m .tmp) hd ‹src ≠ .m .tmp› (by omega) hw ρ l hsrc
    hctr htmp
  have h2 := rsa_moveR (body := body) (ι := M.ι) M.hrg (a := .x .cB) (b := dst) (Ne.symm hdB)
    (Function.update (Function.update ρ src []) (.x .cB)
      ((cstream (prime + K) w (l.map star)).reverse ++ ρ (.x .cB)))
  refine ((RsaRuns.seq M.hdisj h1 h2).congr ?_).mono (le_of_eq ?_)
  · funext r
    simp only [Function.update_apply, hcB, List.append_nil, List.reverse_reverse]
    split_ifs <;> subst_vars <;> simp_all
  · simp only [Function.update_self, hcB, List.append_nil, List.length_reverse, length_cstream,
      List.length_map]

/-- The conjugate of a padded box. -/
theorem src_pad_conj {d q : ℕ} (s t : Fin d → ℕ) (y : ((i : Fin d) → ZMod (s i)) → ℂ) :
    (srcPad q s t y).map star = srcPad q s t fun k => starRingEnd ℂ (y k) := by
  rw [srcPad, srcPad, ← rsaBox_map]
  congr 1
  funext x
  split_ifs
  · rw [cst_numer_conj]
  · simp

variable {n : ℕ}

lemma src_crt_hs (h : Big n) (j : Fin (d n)) : 0 < s n j ∧ s n j < 2 ^ srcAx n j :=
  ⟨Nat.pos_of_ne_zero (NeZero.ne _), by rw [← src_t_eq]; exact h.good.lt j⟩

lemma src_crt_rι (M : SrcMach t₀ T Q) (x : CrtReg) (j : Fin (swapT 6)) : M.rc x ≠ M.rcb j :=
  fun h => by have := M.hrg h; simp at this

/-- **The forward CRT layout** on the composite: the coefficient stream of `u` on `c .str`
becomes the padded stream of `u ∘ Φ⁻¹`. -/
theorem srcCrtF_runs (M : SrcMach t₀ T Q) (hA : 96 ≤ prime + K) (hbig : Big n) {w : ℕ}
    (hw : 1 ≤ w) (E : SrcF t₀ (prime + K)) (hC : SrcCrtBase E.c E.cb n w)
    (u : ZMod (∏ i, s n i) → ℂ)
    (hstr : E.c .str = cstream (prime + K) w (srcCoef (p n) (∏ i, s n i) u)) :
    RsaRuns body M.rg M.ι (crtForward M.hQc M.rcb M.hrcb M.hTc M.rc) E.get
      { E with c := (Function.update E.c .str (cstream (prime + K) w
          (srcPad (p n) (s n) (t n) fun x => u ((crtPhi (s n) (s_pairwise n)).symm x)))) }.get
      (crtCost T (crtPre (srcAx n) (d n)) w (d n) (ℓ n) (ℓ n - 1)) := by
  have h := src_of_crt (body := body) (ι := M.ι) M.hrg (ρ := E.get) (x := .c .str)
    (l := cstream (prime + K) w
      (srcPad (p n) (s n) (t n) fun x => u ((crtPhi (s n) (s_pairwise n)).symm x)))
    (b := crtCost T (crtPre (srcAx n) (d n)) w (d n) (ℓ n) (ℓ n - 1)) fun S _ hS => by
      have hb := fun j => src_ax_bounds (n := n) j
      have H := crtForward_runs (body := body) (srcAx n) (s n) (src_crt_hs hbig) (s_pairwise n)
        (fun j j' => by have := hb j; have := hb j'; omega) (ℓ n) (ℓ n - 1)
        (fun j => (hb j).2) (fun j => (hb j).1) M.hQc M.rcb M.hrcb M.hTc (r := M.rc) M.hrc
        (src_crt_rι M) ((srcCoef (p n) (∏ i, s n i) u).map (csyms (prime + K) w))
        (csyms (prime + K) w 0) w hw (by simp [src_length_coef])
        (fun x hx => by
          obtain ⟨N, -, rfl⟩ := List.mem_map.1 hx
          simp [csyms])
        (by simp [csyms])
        (fun x hx => by
          obtain ⟨N, -, rfl⟩ := List.mem_map.1 hx
          exact src_csyms_lt (by omega) N)
        (src_csyms_lt (by omega) 0) S.R
        (by rw [show S.R (M.rc .str) = E.c .str from hS (.c .str), hstr, cstream,
          List.flatMap_def])
        (by rw [show S.R (M.rc .wT) = E.c .wT from hS (.c .wT), hC.wT])
        (by rw [show S.R (M.rc .sT) = E.c .sT from hS (.c .sT), hC.sT])
        (by rw [show S.R (M.rc .mT) = E.c .mT from hS (.c .mT), hC.mT])
        (by rw [show S.R (M.rc .sig) = E.c .sig from hS (.c .sig), hC.sig])
        (by rw [show S.R (M.rc .msk) = E.c .msk from hS (.c .msk), hC.msk])
        (by rw [show S.R (M.rc .zr) = E.c .zr from hS (.c .zr), hC.zr])
        (fun x hx => by rw [show S.R (M.rc x) = E.c x from hS (.c x)]; exact hC.rest x hx)
        (fun i => by rw [show S.R (M.rcb i) = E.cb i from hS (.cb i)]; exact hC.bank i)
      rw [src_crt_fwd (s n) (s_pairwise n) (srcAx n) (t n) (src_t_eq n)] at H
      exact H
  rwa [SrcF.upd_c] at h

/-- **The inverse CRT layout** on the composite: the padded stream of `g` on `c .str` becomes
the coefficient stream of `g ∘ Φ`. -/
theorem srcCrtI_runs (M : SrcMach t₀ T Q) (hA : 96 ≤ prime + K) (hbig : Big n) {w : ℕ}
    (hw : 1 ≤ w) (E : SrcF t₀ (prime + K)) (hC : SrcCrtBase E.c E.cb n w)
    (g : ((i : Fin (d n)) → ZMod (s n i)) → ℂ)
    (hstr : E.c .str = cstream (prime + K) w (srcPad (p n) (s n) (t n) g)) :
    RsaRuns body M.rg M.ι (crtInverse M.hQc M.rcb M.hrcb M.hTc M.rc) E.get
      { E with c := (Function.update E.c .str (cstream (prime + K) w
          (srcCoef (p n) (∏ i, s n i) fun k => g (crtPhi (s n) (s_pairwise n) k)))) }.get
      (crtCost T (crtPre (srcAx n) (d n)) w (d n) (ℓ n) (ℓ n - 1)) := by
  have h := src_of_crt (body := body) (ι := M.ι) M.hrg (ρ := E.get) (x := .c .str)
    (l := cstream (prime + K) w
      (srcCoef (p n) (∏ i, s n i) fun k => g (crtPhi (s n) (s_pairwise n) k)))
    (b := crtCost T (crtPre (srcAx n) (d n)) w (d n) (ℓ n) (ℓ n - 1)) fun S _ hS => by
      have hb := fun j => src_ax_bounds (n := n) j
      have H := crtInverse_runs (body := body) (srcAx n) (s n) (src_crt_hs hbig) (s_pairwise n)
        (fun j j' => by have := hb j; have := hb j'; omega) (ℓ n) (ℓ n - 1)
        (fun j => (hb j).2) (fun j => (hb j).1) M.hQc M.rcb M.hrcb M.hTc (r := M.rc) M.hrc
        (src_crt_rι M) (fun y => csyms (prime + K) w (srcRec (p n) (s n) g y)) w hw
        (fun y => by simp [csyms]) (fun y => src_csyms_lt (by omega) _) S.R
        (by rw [show S.R (M.rc .str) = E.c .str from hS (.c .str), hstr,
          src_crt_inv_box (s n) (srcAx n) (t n) (src_t_eq n)])
        (by rw [show S.R (M.rc .wT) = E.c .wT from hS (.c .wT), hC.wT])
        (by rw [show S.R (M.rc .sT) = E.c .sT from hS (.c .sT), hC.sT])
        (by rw [show S.R (M.rc .mT) = E.c .mT from hS (.c .mT), hC.mT])
        (by rw [show S.R (M.rc .sig) = E.c .sig from hS (.c .sig), hC.sig])
        (by rw [show S.R (M.rc .msk) = E.c .msk from hS (.c .msk), hC.msk])
        (by rw [show S.R (M.rc .zr) = E.c .zr from hS (.c .zr), hC.zr]; simp [csyms])
        (fun x hx => by rw [show S.R (M.rc x) = E.c x from hS (.c x)]; exact hC.rest x hx)
        (fun i => by rw [show S.R (M.rcb i) = E.cb i from hS (.cb i)]; exact hC.bank i)
      rw [src_crt_inv (s n) (s_pairwise n)] at H
      exact H
  rwa [SrcF.upd_c] at h

end Edges

/-! ### The transforms -/

section Transforms

variable {K : ℕ} {U P : Type} {body : P → Pr P T Q (prime + K) U}

/-- **The computed source transform `F' = F̃ ∘ Φ`** (`Pipeline.srcMap`): the CRT layout of the
coefficient stream on `c .str`, the box moved onto `a .ln`, the source transform. -/
def srcP (M : SrcMach t₀ T Q) (fwdP oppP : Pr P T Q (prime + K) U) : Pr P T Q (prime + K) U :=
  .seq (crtForward M.hQc M.rcb M.hrcb M.hTc M.rc) <|
  .seq (srcMv M.rg (.c .str) (.a .ln) (.x .tr)) (srcCore M fwdP oppP)

/-- **The computed opposite transform `G' = Φ⁻¹ ∘ conj ∘ F̃ ∘ conj`** (`Pipeline.oppMap`): the
padded box on `x .sb` conjugated onto `a .ln`, the source transform, its result conjugated onto
`c .str`, the inverse CRT layout. -/
def oppP' (M : SrcMach t₀ T Q) (fwdP oppP : Pr P T Q (prime + K) U) : Pr P T Q (prime + K) U :=
  .seq (srcConj M (.x .sb) (.a .ln)) <| .seq (srcCore M fwdP oppP) <|
  .seq (srcConj M (.x .sb) (.c .str)) (crtInverse M.hQc M.rcb M.hrcb M.hTc M.rc)

/-- The cost of `srcP`: the CRT layout (`totCRT`), the transfer, the source transform. -/
def srcPCost (M : SrcMach t₀ T Q) (n w W cF cO : ℕ) (hd0 : 0 < d n)
    (V₀ : RsaV (RsaX t₀) (prime + K)) (σ₀ : RsbR ⊕ RsbX t₀ → List (Fin (prime + K + 4)))
    (restA restB : List (Fin (prime + K + 4))) : ℕ :=
  crtCost T (crtPre (srcAx n) (d n)) w (d n) (ℓ n) (ℓ n - 1) + (4 * ((∏ i, t n i) * w) + 4) +
    srcCoreCost M n w W cF cO hd0 V₀ σ₀ restA restB

/-- The cost of one conjugation of a box of `T` entries. -/
def srcConjCost (V w : ℕ) : ℕ := V * (5 * w + 6) + 2 + (2 * (V * w) + 2)

/-- The cost of `oppP'`: two conjugations, the source transform, the inverse CRT layout
(`totCRT`). -/
def oppPCost (M : SrcMach t₀ T Q) (n w W cF cO : ℕ) (hd0 : 0 < d n)
    (V₀ : RsaV (RsaX t₀) (prime + K)) (σ₀ : RsbR ⊕ RsbX t₀ → List (Fin (prime + K + 4)))
    (restA restB : List (Fin (prime + K + 4))) : ℕ :=
  srcConjCost (∏ i, t n i) w + srcCoreCost M n w W cF cO hd0 V₀ σ₀ restA restB +
    srcConjCost (∏ i, t n i) w + crtCost T (crtPre (srcAx n) (d n)) w (d n) (ℓ n) (ℓ n - 1)

lemma src_srcMap_eq (n : ℕ) (u : ZMod (∏ i, s n i) → ℂ) :
    srcMap n u = SourceErr.sourceApprox (s n) (t n) (p n) (gamma n) (lineA n) (lineB n)
      (chirpKernel n) (convBox n) fun x => u ((crtPhi (s n) (s_pairwise n)).symm x) := rfl

lemma src_oppMap_eq (n : ℕ) (y : ((i : Fin (d n)) → ZMod (s n i)) → ℂ) :
    oppMap n y = fun k => SourceErr.oppApprox (s n) (t n) (p n) (gamma n) (lineA n) (lineB n)
      (chirpKernel n) (convBox n) y (crtPhi (s n) (s_pairwise n) k) := rfl

/-- **The computed source transform `F'` as a machine.** From the register file between runs
(`SrcBase`, `SrcCrtBase`) with the coefficient stream of `u` (grid values at scale `2^p`,
`‖u‖ ≤ 1/2`) on `c .str` and the box register `a .ln` empty, `srcP` pushes the padded stream of
`Pipeline.srcMap n u` on the source box onto `x .sb`, empties `c .str`, configures the resampling
families for axis `0` (consuming one set of records), and leaves every other register as it
began, within `srcPCost` steps. -/
theorem srcP_runs (M : SrcMach t₀ T Q) (hA : 96 ≤ prime + K) {n : ℕ} (hbig : Big n)
    (hsmall : 2 * d n * p n ^ 2 ≤ Sizes.T n * logT n)
    (hEs : 9 * (2 : ℝ) ^ gamma n * Sizes.T n * logT n ≤ 2 ^ p n / 100)
    {fwdP oppP : Pr P T Q (prime + K) U} {Pre PreF PreO : Stacks T (prime + K) → Prop}
    {w W cF cO : ℕ} {π : ℕ → ℕ}
    (hF : SynFwdSpec body fwdP (M.rg (.v .io)) PreF w (p n) (ℓ n) (cvAx (t n)) π cF)
    (hO : SynOppSpec body oppP (M.rg (.v .io)) PreO w (p n) (ℓ n) (cvAx (t n)) π cO)
    (hPF : ∀ S, Pre S → PreF S) (hPO : ∀ S, Pre S → PreO S)
    (hπ : ∀ m < cvM (cvAx (t n)), π m < cvM (cvAx (t n))) (hP : SrcFramed M.rg Pre)
    (hw : p n + Chirp.chirpGuard (d n) + 3 ≤ w) (hwW : w < W)
    (hWA : ∀ i : Fin (d n), alpha n ^ 2 * ((s n i + t n i) * (windowA (p n) (alpha n) + 1)) ^ 2 *
      2 ^ (13 * p n + 8) < 2 ^ W)
(hWB : 9 * p n + 2 ≤ w ∧ ∀ i : Fin (d n), alpha n ^ 2 * ((s n i + t n i) *
      (8 * FastB0.fastWindow (p n) (alpha n) + 1)) ^ 2 * 2 ^ (65 * p n + 8) < 2 ^ W)
    (hWs : ∀ k, s n k * t n k * t n k < 2 ^ W)
    (hWk : ∀ k, 8 * (p n + Chirp.chirpGuard (d n)) + Nat.size (t n k) + 80 ≤ W)
    {V₀ : RsaV (RsaX t₀) (prime + K)} {σ₀ : RsbR ⊕ RsbX t₀ → List (Fin (prime + K + 4))}
    {restA restB axsA axsB : List (Fin (prime + K + 4))} (E : SrcF t₀ (prime + K))
    (hE : SrcBase M E n w W (srcHd0 hbig) V₀ σ₀ restA restB axsA axsB)
    (hC : SrcCrtBase E.c E.cb n w) (hln : E.a .ln = [])
    (u : ZMod (∏ i, s n i) → ℂ) (hu : ‖u‖ ≤ 1 / 2) (huf : ∀ k, IsFixed (p n) (u k))
    (hstr : E.c .str = cstream (prime + K) w (srcCoef (p n) (∏ i, s n i) u)) :
    SrcRuns body M.rg M.ι Pre (srcP M fwdP oppP) E.get
      { E with a := (rsaWith (preCfgA V₀ M.hd n w W (srcHd0 hbig) restA (d n - 1)) [] axsA []).get,
               b := rsbWith (bandCfgB σ₀ M.hd n w W (srcHd0 hbig) restB (d n - 1)) [] axsB [],
               c := Function.update E.c .str [],
               x := (Function.update E.x .sb
                 (cstream (prime + K) w (srcPad (p n) (s n) (t n) (srcMap n u)) ++ E.x .sb)) }.get
      (srcPCost M n w W cF cO (srcHd0 hbig) V₀ σ₀ restA restB) := by
  have hdisj := M.hdisj
  set v : ((i : Fin (d n)) → ZMod (s n i)) → ℂ :=
    fun x => u ((crtPhi (s n) (s_pairwise n)).symm x) with hvdef
  have s1 := srcCrtF_runs (body := body) M hA hbig (by omega) E hC u hstr
  set BOX := cstream (prime + K) w (srcPad (p n) (s n) (t n) v) with hBOX
  set E₁ : SrcF t₀ (prime + K) := { E with c := Function.update E.c .str BOX } with hE₁
  have s2 := src_mv_runs (body := body) M.hrg hdisj (a := .c .str) (b := .a .ln) (sp := .x .tr)
    (by simp) (by simp) (by simp) E₁.get (by simp [hE₁, hE.x.tr])
  rw [SrcF.get_c, SrcF.get_a, SrcF.upd_c, SrcF.upd_a] at s2
  set E₂ : SrcF t₀ (prime + K) :=
    { E with c := Function.update E.c .str [], a := Function.update E.a .ln BOX } with hE₂
  have e₂ : ({ { E₁ with c := Function.update E₁.c .str [] } with
      a := Function.update { E₁ with c := Function.update E₁.c .str [] }.a .ln
        (E₁.c .str ++ { E₁ with c := Function.update E₁.c .str [] }.a .ln) } :
      SrcF t₀ _) = E₂ := by
    simp only [hE₁, hE₂, Function.update_idem, Function.update_self, hln, List.append_nil]
  rw [e₂] at s2
  have hE₂b : SrcBase M E₂ n w W (srcHd0 hbig) V₀ σ₀ restA restB axsA axsB :=
    hE.of_eq (fun r hr => by simp [hE₂, Function.update_of_ne hr]) rfl rfl rfl rfl
      (fun _ _ => rfl)
  have s3 := srcCore_runs (body := body) M hA hbig hsmall hEs hF hO hPF hPO hπ hP hw hwW hWA hWB
    hWs hWk E₂ hE₂b v
    ((pi_norm_le_iff_of_nonneg (by norm_num)).2 fun x => (norm_le_pi_norm u _).trans hu)
    (fun x => huf _) (by simp [hE₂, hBOX])
  refine ((SrcRuns.of_rsa s1).seq hdisj hP ((SrcRuns.of_rsa s2).seq hdisj hP s3)).congr ?_
    |>.mono (le_of_eq ?_)
  · congr 1
  · simp only [srcPCost, hE₁, Function.update_self, hBOX, length_cstream, src_length_pad]
    ring

/-- **The computed opposite transform `G'` as a machine.** From the register file between runs
(`SrcBase`, `SrcCrtBase`) with the padded stream of `y` (grid values at scale `2^p`,
`‖y‖ ≤ 1/2`) on `x .sb`, the box register `a .ln` and `c .str` empty, `oppP'` leaves the
coefficient stream of `Pipeline.oppMap n y` on `c .str`, empties `x .sb`, configures the
resampling families for axis `0`, and leaves every other register as it began, within
`oppPCost` steps. -/
theorem srcOpp_runs (M : SrcMach t₀ T Q) (hA : 96 ≤ prime + K) {n : ℕ} (hbig : Big n)
    (hsmall : 2 * d n * p n ^ 2 ≤ Sizes.T n * logT n)
    (hEs : 9 * (2 : ℝ) ^ gamma n * Sizes.T n * logT n ≤ 2 ^ p n / 100)
    {fwdP oppP : Pr P T Q (prime + K) U} {Pre PreF PreO : Stacks T (prime + K) → Prop}
    {w W cF cO : ℕ} {π : ℕ → ℕ}
    (hF : SynFwdSpec body fwdP (M.rg (.v .io)) PreF w (p n) (ℓ n) (cvAx (t n)) π cF)
    (hO : SynOppSpec body oppP (M.rg (.v .io)) PreO w (p n) (ℓ n) (cvAx (t n)) π cO)
    (hPF : ∀ S, Pre S → PreF S) (hPO : ∀ S, Pre S → PreO S)
    (hπ : ∀ m < cvM (cvAx (t n)), π m < cvM (cvAx (t n))) (hP : SrcFramed M.rg Pre)
    (hw : p n + Chirp.chirpGuard (d n) + 3 ≤ w) (hwW : w < W)
    (hWA : ∀ i : Fin (d n), alpha n ^ 2 * ((s n i + t n i) * (windowA (p n) (alpha n) + 1)) ^ 2 *
      2 ^ (13 * p n + 8) < 2 ^ W)
(hWB : 9 * p n + 2 ≤ w ∧ ∀ i : Fin (d n), alpha n ^ 2 * ((s n i + t n i) *
      (8 * FastB0.fastWindow (p n) (alpha n) + 1)) ^ 2 * 2 ^ (65 * p n + 8) < 2 ^ W)
    (hWs : ∀ k, s n k * t n k * t n k < 2 ^ W)
    (hWk : ∀ k, 8 * (p n + Chirp.chirpGuard (d n)) + Nat.size (t n k) + 80 ≤ W)
    {V₀ : RsaV (RsaX t₀) (prime + K)} {σ₀ : RsbR ⊕ RsbX t₀ → List (Fin (prime + K + 4))}
    {restA restB axsA axsB : List (Fin (prime + K + 4))} (E : SrcF t₀ (prime + K))
    (hE : SrcBase M E n w W (srcHd0 hbig) V₀ σ₀ restA restB axsA axsB)
    (hC : SrcCrtBase E.c E.cb n w) (hln : E.a .ln = []) (hstr : E.c .str = [])
    (y : ((i : Fin (d n)) → ZMod (s n i)) → ℂ) (hy : ‖y‖ ≤ 1 / 2)
    (hyf : ∀ k, IsFixed (p n) (y k))
    (hsb : E.x .sb = cstream (prime + K) w (srcPad (p n) (s n) (t n) y)) :
    SrcRuns body M.rg M.ι Pre (oppP' M fwdP oppP) E.get
      { E with a := (rsaWith (preCfgA V₀ M.hd n w W (srcHd0 hbig) restA (d n - 1)) [] axsA []).get,
               b := rsbWith (bandCfgB σ₀ M.hd n w W (srcHd0 hbig) restB (d n - 1)) [] axsB [],
               c := (Function.update E.c .str
                 (cstream (prime + K) w (srcCoef (p n) (∏ i, s n i) (oppMap n y)))),
               x := Function.update E.x .sb [] }.get
      (oppPCost M n w W cF cO (srcHd0 hbig) V₀ σ₀ restA restB) := by
  have hdisj := M.hdisj
  set yc : ((i : Fin (d n)) → ZMod (s n i)) → ℂ := fun k => starRingEnd ℂ (y k) with hyc
  set SA := SourceErr.sourceApprox (s n) (t n) (p n) (gamma n) (lineA n) (lineB n)
    (chirpKernel n) (convBox n) yc with hSA
  -- the first conjugation
  have s1 := src_conj_runs (body := body) M hA (w := w) (by omega) (src := .x .sb)
    (dst := .a .ln) (by simp) (by simp) (by simp) E.get _ hsb (by simp [hE.x.cB]) hE.m.ready.wn hE.m.ready.tmp
  rw [src_pad_conj, SrcF.get_a, hln, List.append_nil, SrcF.upd_x, SrcF.upd_a, src_length_pad]
    at s1
  set E₁ : SrcF t₀ (prime + K) :=
    { E with x := Function.update E.x .sb [],
             a := Function.update E.a .ln (cstream (prime + K) w (srcPad (p n) (s n) (t n) yc)) }
    with hE₁
  have hE₁b : SrcBase M E₁ n w W (srcHd0 hbig) V₀ σ₀ restA restB axsA axsB :=
    hE.of_eq (fun r hr => by simp [hE₁, Function.update_of_ne hr]) rfl rfl rfl rfl
      (fun j hj => by simp [hE₁, Function.update_of_ne hj])
  -- the source transform
  have s2 := srcCore_runs (body := body) M hA hbig hsmall hEs hF hO hPF hPO hπ hP hw hwW hWA hWB
    hWs hWk E₁ hE₁b yc (by rw [hyc, SourceErr.norm_conj_fun]; exact hy)
    (fun x => cst_isFixed_conj (hyf x)) (by simp [hE₁])
  set E₂ : SrcF t₀ (prime + K) :=
    { E₁ with a := (rsaWith (preCfgA V₀ M.hd n w W (srcHd0 hbig) restA (d n - 1)) [] axsA []).get,
              b := rsbWith (bandCfgB σ₀ M.hd n w W (srcHd0 hbig) restB (d n - 1)) [] axsB [],
              x := (Function.update E₁.x .sb (cstream (prime + K) w
                (srcPad (p n) (s n) (t n) SA) ++ E₁.x .sb)) } with hE₂
  -- the second conjugation
  have s3 := src_conj_runs (body := body) M hA (w := w) (by omega) (src := .x .sb)
    (dst := .c .str) (by simp) (by simp) (by simp) E₂.get (srcPad (p n) (s n) (t n) SA)
    (by simp [hE₂, hE₁]) (by simp [hE₂, hE₁, hE.x.cB])
    (by simpa [hE₂, hE₁] using hE.m.ready.wn) (by simpa [hE₂, hE₁] using hE.m.ready.tmp)
  rw [src_pad_conj, SrcF.get_c, SrcF.upd_x, SrcF.upd_c, src_length_pad] at s3
  set E₃ : SrcF t₀ (prime + K) :=
    { E₂ with x := Function.update E₂.x .sb [],
              c := (Function.update E.c .str (cstream (prime + K) w
                (srcPad (p n) (s n) (t n) fun k => starRingEnd ℂ (SA k)))) } with hE₃
  replace s3 := s3.congr (ρ'' := E₃.get) (by
    congr 1
    simp only [hE₃, hE₂, hE₁, SrcF.get_c, hstr, List.append_nil])
  -- the inverse layout
  have s4 := srcCrtI_runs (body := body) M hA hbig (w := w) (by omega) E₃ (hC.upd_str _)
    (fun k => starRingEnd ℂ (SA k)) (by simp [hE₃])
  refine ((SrcRuns.of_rsa s1).seq hdisj hP (s2.seq hdisj hP ((SrcRuns.of_rsa s3).seq hdisj hP
    (SrcRuns.of_rsa s4)))).congr ?_ |>.mono (le_of_eq ?_)
  · congr 1
    refine SrcF.ext rfl rfl rfl rfl ?_ rfl rfl ?_
    · simp only [hE₃, Function.update_idem]
      rfl
    · simp only [hE₃, hE₂, hE₁, Function.update_idem]
  · simp only [oppPCost, srcConjCost]
    ring

end Transforms

/-! ### Runs in sequence -/

section Next

variable {K : ℕ}

/-- A loaded `Ã` file is again a base file. -/
lemma src_preBaseA_load {A w : ℕ} {V : RsaV (RsaX t₀) A} {hd : Fin 5 → Fin t₀}
    (h : PreBaseA V w hd) (D : PreAxA) (r : List (Fin (A + 4))) :
    PreBaseA (preLoadA V hd w D r) w hd := by
  have e : ∀ c, c ≠ .ys → c ≠ .pn → c ≠ .out → (preLoadA V hd w D r).cr c = V.cr c := by
    intro c h1 h2 h3
    simp [preLoadA, Function.update_of_ne h1, Function.update_of_ne h2, Function.update_of_ne h3]
  exact {
    free := h.free.load hd w D r
    wn := by rw [e _ (by decide) (by decide) (by decide)]; exact h.wn
    nn := by rw [e _ (by decide) (by decide) (by decide)]; exact h.nn
    cr := fun c h1 h2 h3 h4 h5 => by rw [e c h1 h2 h3]; exact h.cr c h1 h2 h3 h4 h5
    ob := h.ob
    bxa := h.bxa
    bya := h.bya
    bza := h.bza
    bank := fun j hj => by
      simp only [preLoadA, preBankA]
      rw [if_neg (fun ⟨k, e⟩ => hj k e)]
      exact h.bank j hj
    xt := h.xt
    e1 := h.e1
    e2 := h.e2 }

lemma src_preRecsA_end {A : ℕ} {n W : ℕ} (hd0 : 0 < d n) :
    (preRecsA (A := A) n W hd0 (d n - 1 + 1)) = [] := by
  rw [preRecsA, List.drop_eq_nil_of_le (by simp; omega)]
  rfl

lemma src_preRecsB_end' {A : ℕ} {n W : ℕ} (hd0 : 0 < d n) :
    (preRecsB (A := A) n W hd0 (d n)) = [] := by
  rw [preRecsB, List.drop_eq_nil_of_le (by simp)]
  rfl

/-- **Runs in sequence.** If the parameter registers hold the records of one run followed by
`restA`, `restB`, the register file after `srcP` or `oppP'` (configured resampling families,
any box registers, `c` and `x .sb`) is again a register file between runs, over the configured
base files, with `restA`, `restB` left. -/
theorem SrcBase.next {M : SrcMach t₀ T Q} {E E' : SrcF t₀ (prime + K)} {n w W : ℕ}
    {hd0 : 0 < d n} {V₀ : RsaV (RsaX t₀) (prime + K)}
    {σ₀ : RsbR ⊕ RsbX t₀ → List (Fin (prime + K + 4))}
    {restA restB axsA axsB : List (Fin (prime + K + 4))}
    (hA3 : 3 ≤ prime + K)
    (h : SrcBase M E n w W hd0 V₀ σ₀ (preRecsA n W hd0 0 ++ restA)
      (preRecsB n W hd0 0 ++ restB) axsA axsB)
    (ha : ∀ r, r ≠ .ln → E'.a r = (rsaWith (preCfgA V₀ M.hd n w W hd0
      (preRecsA n W hd0 0 ++ restA) (d n - 1)) [] axsA []).get r)
    (hb : E'.b = rsbWith (bandCfgB σ₀ M.hd n w W hd0 (preRecsB n W hd0 0 ++ restB) (d n - 1))
      [] axsB [])
    (hk : E'.k = E.k) (hv : E'.v = E.v) (hm : E'.m = E.m) (hx : ∀ j, j ≠ .sb → E'.x j = E.x j) :
    SrcBase M E' n w W hd0 (preCfgA V₀ M.hd n w W hd0 (preRecsA n W hd0 0 ++ restA) (d n - 1))
      (bandCfgB σ₀ M.hd n w W hd0 (preRecsB n W hd0 0 ++ restB) (d n - 1)) restA restB
      axsA axsB where
  a := ha
  aBase := src_preBaseA_load h.aBase _ _
  aOut := by
    simp only [preCfgA, preLoadA, Function.update_self, src_preRecsA_end hd0, List.nil_append]
  aAx := h.aAx
  b := hb
  bBase := bandCfgB_base h.bBase hA3 _
  bOut := by
    rw [bandCfgB_prm, Nat.sub_add_cancel (by omega : 1 ≤ d n), src_preRecsB_end' hd0, List.nil_append]
  bAx := h.bAx
  k := hk ▸ h.k
  v := hv ▸ h.v
  m := hm ▸ h.m
  x := h.x.of_eq hx

end Next

end

end IntegerMultBounds.MathlibTM2.Fast.Src
