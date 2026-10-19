module

public import IntegerMultBounds.NLogN.SynthEmbed
public import IntegerMultBounds.NLogN.BluesteinApprox
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Computed complex convolution by a coefficient twist

Paper §8, subsections "Complex convolution by a coefficient twist" and "Computed complex
convolution", and the phase-product and `M̃_ℂ` estimates of "Precision and exact recovery";
gaps M6 and M9 of `docs/assembly-map.md`.

## Conventions

`Q_p` is `NLogN.rhoC p` (componentwise truncation toward zero to `2^{-p} ℤ`), with
`NLogN.norm_rhoC_sub_lt` (`‖Q_p z − z‖ < √2·2^{-p}`) and `NLogN.norm_rhoC_le`
(`‖Q_p z‖ ≤ ‖z‖`). Arrays carry the sup norm of `Pi`; errors are scaled by `2^p`. The index
set is `G × Fin r` for a finite abelian group `G`; the last coordinate is the polynomial
coordinate, `ζ = e^{πi/r}` and `ζ^k = NLogN.twistRoot r k`.

## Phase products

* `norm_rhoC_mul_sub_lt'`: `|ẽ − e| < 2·2^{-p}` gives `|Q_p(ẽx) − ex| < (2|x| + √2)·2^{-p}`
  (`|e| = 1` and `|ẽ| ≤ 1` are not needed); `norm_rhoC_mul_le`: `|ẽ| ≤ 1` gives
  `|Q_p(ẽx)| ≤ |x|`; array forms `norm_rhoC_mul_arr_sub_le`, `norm_rhoC_mul_arr_le`.

## The exact identity

* `iota`, `iotaInv` (`ι`, `ι⁻¹`), `phaseMul` (`D_±`), `convNormG` (`(u ∗ v)/|A|`),
  `synthConvNormG` (`ℳ_r`, normalized by `r|G|` as in `Spec.SignedRingProduct.convM`).
* `convNormG_eq_twist`: `ℳ_ℂ(f, g) = D₋ ι⁻¹ ℳ_r(ι D₊ f, ι D₊ g) = (f ∗ g)/T`, from
  `NLogN.convG_eq_ofSynth`. `norm_synthConvNormG_le` and `synthConvNormG_sub` make `ℳ_r` a
  bilinear contraction.

## The computed convolution

* `PhaseApprox p θ e`: `2^p |θ_k − e_k| < 2` and `|θ_k| ≤ 1` for every `k`.
* `RingApprox p M̃_r E`: on disk-grid operands (`NLogN.IsFixed p`, modulus at most one) every
  coefficient of `M̃_r` is within `E·2^{-p}` of `ℳ_r`. This is the guarantee of
  `prop:synthetic-convolution` (`Spec.SignedRingProduct.MeetsConvolution` with
  `E = √2 M(3ℓ+1)`, or the paper's `E_ring = M(3L+2)`). The output norm bound of `M̃_r`
  follows from the error bound and is not a hypothesis.
* `cconvApprox p θ⁺ θ⁻ M̃_r f g = Q_p(θ⁻ · ι⁻¹ M̃_r(ι Q_p(θ⁺ f), ι Q_p(θ⁺ g)))`.
* `cconvApprox_spec`: for `‖f‖ ≤ X ≤ 1` and `‖g‖ ≤ Y ≤ 1`, scaled error at most
  `E + (2X+√2)Y + X(2Y+√2) + 2(XY + E·2^{-p}) + √2` and norm at most `XY + E·2^{-p}`.
* `cconvApprox_err`: for `‖f‖ ≤ 1`, `‖g‖ ≤ 7/10` and `1000 E ≤ 2^p`, scaled error at most
  `E + 9` and norm at most `701/1000`. With `E = E_ring < 5TL` and `9 ≤ TL` this gives the
  paper's `6TL`.
* `cconvApproxVia`, `cconvApproxVia_err`: the same along any `B ≃+ G × Fin r`. `boxSplit` and
  `cconvApprox_box`: the box `∏_{i ≤ d} ℤ/t_i` with `t_d = r`, compared with
  `NLogN.convNormD`; this is the hypothesis `hM'` of the source-transform assembly with
  `E + 9` in place of `6TL`.

## Roots of unity

* `phase_of_cos_sin`: component errors below `2^{-p}` give
  `|c + is − e^{iφ}| < √2·2^{-p} < 2·2^{-p}`.
* `diskPhase p z = Q_p((1 − 2^{-(p+2)}) z)`; `diskPhase_spec`: from `|z − e| ≤ 2^{-(p+2)}`
  and `|e| = 1`, a disk-grid phase with error below `2·2^{-p}`.
* `taylorTerm q x`: `u₀ = 1`, `u_{m+1} = Q_q(u_m x/(m+1))`; `taylorExpI q x n = ∑_{m<n} i^m u_m`
  (real part the cosine sum, imaginary part the sine sum, exact additions on the grid).
  `abs_term_sub_le`: for `|x| ≤ 4` and any rounding with per-step error at most `δ`, every
  term is within `6δ` of `x^m/m!`. `taylorExpI_err`: `n ≥ p + 12` terms and `16 n ≤ 2^g` give
  `2^p |taylorExpI (p+g) x n − e^{ix}| ≤ 5/8`; `taylor_cos_sin_err`: each component within
  `2^{-p}`; `taylorExpI_err_explicit`: `n = 2p`, `g = ⌈log₂ 2p⌉ + 4`, `p ≥ 12`.
* `twistPhase`, `twistPhase_spec`, `twistPhase_phaseApprox`: from angles `x_k` within
  `2^{-(p+4)}` of `πk/r`, the arrays `θ⁺_k = twistPhase(x_k)` and `θ⁻ = conj θ⁺` satisfy
  `PhaseApprox` for `ζ^k` and `ζ^{-k}`.

Outside this file: the fixed-point computation of the angles `x_k ≈ πk/r`, the identification
of Spec record arrays (`ℕ → Fin r → ℂ`, `digit`/`undigits`) with `G → Fin r → ℂ`, costs, and
tapes.
-/

@[expose] public section


open IntegerMultBounds IntegerMultBounds.NLogN Complex

namespace IntegerMultBounds.MathlibTM2.Mult.ComplexConv

/-! ### Phase products -/

/-- The phase-product bound with scaled errors: `2^p |Q_p(ẽx) − ex| < 2|x| + √2`. -/
theorem norm_rhoC_mul_sub_lt {p : ℕ} {e e' x : ℂ} (he : 2 ^ p * ‖e' - e‖ < 2) :
    2 ^ p * ‖rhoC p (e' * x) - e * x‖ < 2 * ‖x‖ + Real.sqrt 2 := by
  have hp : (0 : ℝ) < 2 ^ p := by positivity
  have h1 : 2 ^ p * ‖rhoC p (e' * x) - e' * x‖ < Real.sqrt 2 := by
    have := norm_rhoC_sub_lt p (e' * x)
    rw [lt_div_iff₀ hp] at this
    linarith
  have h2 : 2 ^ p * ‖e' * x - e * x‖ ≤ 2 * ‖x‖ := by
    rw [← sub_mul, norm_mul, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right he.le (norm_nonneg _)
  calc 2 ^ p * ‖rhoC p (e' * x) - e * x‖
      ≤ 2 ^ p * ‖rhoC p (e' * x) - e' * x‖ + 2 ^ p * ‖e' * x - e * x‖ := by
        rw [← mul_add]
        gcongr
        exact norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ < Real.sqrt 2 + 2 * ‖x‖ := add_lt_add_of_lt_of_le h1 h2
    _ = 2 * ‖x‖ + Real.sqrt 2 := add_comm _ _

/-- The phase-product bound of "Precision and exact recovery": if `|ẽ − e| < 2·2^{-p}` then
`|Q_p(ẽx) − ex| < (2|x| + √2) 2^{-p}`. Neither `|e| = 1` nor `|ẽ| ≤ 1` is used. -/
theorem norm_rhoC_mul_sub_lt' {p : ℕ} {e e' x : ℂ} (he : ‖e' - e‖ < 2 / 2 ^ p) :
    ‖rhoC p (e' * x) - e * x‖ < (2 * ‖x‖ + Real.sqrt 2) / 2 ^ p := by
  have hp : (0 : ℝ) < 2 ^ p := by positivity
  rw [lt_div_iff₀ hp, mul_comm] at he
  rw [lt_div_iff₀ hp, mul_comm]
  exact norm_rhoC_mul_sub_lt he

/-- A truncated phase product with a disk phase does not increase the norm. -/
theorem norm_rhoC_mul_le {p : ℕ} {e' x : ℂ} (he' : ‖e'‖ ≤ 1) : ‖rhoC p (e' * x)‖ ≤ ‖x‖ :=
  (norm_rhoC_le p _).trans (by rw [norm_mul]; exact mul_le_of_le_one_left (norm_nonneg _) he')

/-- The phase-product bounds for arrays of phases over any finite index set (sup norm). -/
theorem norm_rhoC_mul_arr_sub_le {ι : Type*} [Fintype ι] {p : ℕ} {θ e u : ι → ℂ}
    (h : ∀ i, 2 ^ p * ‖θ i - e i‖ < 2) :
    2 ^ p * ‖(fun i => rhoC p (θ i * u i)) - fun i => e i * u i‖ ≤ 2 * ‖u‖ + Real.sqrt 2 := by
  have hp : (0 : ℝ) < 2 ^ p := by positivity
  rw [mul_comm, ← le_div_iff₀ hp]
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
  rw [le_div_iff₀ hp, mul_comm, Pi.sub_apply]
  refine (norm_rhoC_mul_sub_lt (x := u i) (h i)).le.trans ?_
  have := norm_le_pi_norm u i
  linarith

theorem norm_rhoC_mul_arr_le {ι : Type*} [Fintype ι] {p : ℕ} {θ u : ι → ℂ}
    (h : ∀ i, ‖θ i‖ ≤ 1) : ‖fun i => rhoC p (θ i * u i)‖ ≤ ‖u‖ :=
  (pi_norm_le_iff_of_nonneg (norm_nonneg u)).2 fun i =>
    (norm_rhoC_mul_le (h i)).trans (norm_le_pi_norm u i)

/-! ### The twist, `ι`, and the exact identity -/

section Exact

variable {G : Type*} {r : ℕ}

/-- `ι`: the scalar array on `G × Fin r` as an array of `ℛ_r` records (no twist). -/
def iota (u : G × Fin r → ℂ) : G → Fin r → ℂ := fun j k => u (j, k)

/-- `ι⁻¹`. -/
def iotaInv (w : G → Fin r → ℂ) : G × Fin r → ℂ := fun x => w x.1 x.2

/-- `D_θ`: multiply coefficient `k` of every last-coordinate line by `θ k`. -/
def phaseMul (θ : Fin r → ℂ) (u : G × Fin r → ℂ) : G × Fin r → ℂ := fun x => θ x.2 * u x

/-- `Q_p(θ · u)`: the computed phase product on every last-coordinate line. -/
noncomputable def phaseQ (p : ℕ) (θ : Fin r → ℂ) (u : G × Fin r → ℂ) : G × Fin r → ℂ :=
  fun x => rhoC p (θ x.2 * u x)

end Exact

/-- The normalized cyclic convolution `(u ∗ v)/|A|` on a finite abelian group. -/
noncomputable def convNormG {A : Type*} [AddCommGroup A] [Fintype A] (u v : A → ℂ) : A → ℂ :=
  fun x => (1 / (Fintype.card A : ℂ)) * convG u v x

theorem convNormD_eq_convNormG {d : ℕ} {N : Fin d → ℕ} [∀ i, NeZero (N i)]
    (a b : ((i : Fin d) → ZMod (N i)) → ℂ) : convNormD N a b = convNormG a b := by
  funext k
  simp only [convNormD, convNormG, card_pi_zmod]

/-- Normalized convolution transports along additive isomorphisms. -/
theorem convNormG_comp_symm {A B : Type*} [AddCommGroup A] [Fintype A] [AddCommGroup B]
    [Fintype B] (e : A ≃+ B) (u v : A → ℂ) :
    convNormG (u ∘ e.symm) (v ∘ e.symm) = convNormG u v ∘ e.symm := by
  funext x
  simp only [convNormG, convG_comp_symm e, Function.comp, Fintype.card_congr e.toEquiv]

section Ring

variable {G : Type*} [AddCommGroup G] [Fintype G] {r : ℕ}

/-- `ℳ_r`: the normalized negacyclic convolution `(r |G|)⁻¹ ∑_i U_i V_{j−i}` over `ℛ_r`
(`Spec.SignedRingProduct.convM` with `G` for the address set). -/
noncomputable def synthConvNormG (U V : G → Fin r → ℂ) : G → Fin r → ℂ :=
  fun j => (1 / ((r * Fintype.card G : ℕ) : ℂ)) • synthConvG U V j

theorem synthConvNormG_apply (U V : G → Fin r → ℂ) (j : G) (k : Fin r) :
    synthConvNormG U V j k =
      (1 / ((r * Fintype.card G : ℕ) : ℂ)) * ∑ i, negacyclicMul (U i) (V (j - i)) k := by
  simp only [synthConvNormG, synthConvG, Pi.smul_apply, smul_eq_mul, Finset.sum_apply]

/-- `ℳ_r` is a bilinear contraction for the coefficient sup norm. -/
theorem norm_synthConvNormG_le {U V : G → Fin r → ℂ} {a b : ℝ} (hU : ∀ j k, ‖U j k‖ ≤ a)
    (hV : ∀ j k, ‖V j k‖ ≤ b) (ha : 0 ≤ a) (hb : 0 ≤ b) (j : G) (k : Fin r) :
    ‖synthConvNormG U V j k‖ ≤ a * b := by
  rcases Nat.eq_zero_or_pos r with hr | hr
  · exact (Fin.elim0 (hr ▸ k))
  have hU' : ∀ i, ‖U i‖ ≤ a := fun i => (pi_norm_le_iff_of_nonneg ha).2 (hU i)
  have hV' : ∀ i, ‖V i‖ ≤ b := fun i => (pi_norm_le_iff_of_nonneg hb).2 (hV i)
  have hT : (0 : ℝ) < ((r * Fintype.card G : ℕ) : ℝ) := by
    have : 0 < Fintype.card G := Fintype.card_pos
    positivity
  rw [synthConvNormG_apply, norm_mul, norm_one_div_nat]
  calc 1 / ((r * Fintype.card G : ℕ) : ℝ) * ‖∑ i, negacyclicMul (U i) (V (j - i)) k‖
      ≤ 1 / ((r * Fintype.card G : ℕ) : ℝ) * ∑ _i : G, (r : ℝ) * a * b := by
        gcongr
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
        calc ‖negacyclicMul (U i) (V (j - i)) k‖ ≤ ‖negacyclicMul (U i) (V (j - i))‖ :=
              norm_le_pi_norm _ k
          _ ≤ r * ‖U i‖ * ‖V (j - i)‖ := norm_negacyclicMul_le _ _
          _ ≤ r * a * b := by
              gcongr
              · exact hU' i
              · exact hV' _
    _ = a * b := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        push_cast
        field_simp

/-- Bilinearity of `ℳ_r` in the form used for error propagation. -/
theorem synthConvNormG_sub (U U' V V' : G → Fin r → ℂ) (j : G) (k : Fin r) :
    synthConvNormG U' V' j k - synthConvNormG U V j k =
      synthConvNormG (U' - U) V' j k + synthConvNormG U (V' - V) j k := by
  simp only [synthConvNormG_apply, negacyclicMul, Pi.sub_apply, mul_sub, sub_mul,
    Finset.sum_sub_distrib]
  ring

variable [NeZero r]

omit [AddCommGroup G] [NeZero r] in
theorem card_prod_fin : Fintype.card (G × Fin r) = r * Fintype.card G := by
  rw [Fintype.card_prod, Fintype.card_fin, mul_comm]

/-- The exact identity `ℳ_ℂ(f, g) = D₋ ι⁻¹ ℳ_r(ι D₊ f, ι D₊ g) = (f ∗ g)/T`, from
`NLogN.convG_eq_ofSynth`. -/
theorem convNormG_eq_ofSynth (u v : G × Fin r → ℂ) :
    convNormG u v = ofSynth (synthConvNormG (toSynth u) (toSynth v)) := by
  funext x
  simp only [convNormG, convG_eq_ofSynth u v, ofSynth, untwist, synthConvNormG, Pi.smul_apply,
    smul_eq_mul, card_prod_fin]
  ring

theorem convNormG_eq_twist (u v : G × Fin r → ℂ) :
    convNormG u v = phaseMul (fun k => (starRingEnd ℂ) (twistRoot r k.val))
      (iotaInv (synthConvNormG (iota (phaseMul (fun k => twistRoot r k.val) u))
        (iota (phaseMul (fun k => twistRoot r k.val) v)))) :=
  convNormG_eq_ofSynth u v

end Ring

/-! ### The computed complex convolution -/

section Computed

variable {G : Type*} [AddCommGroup G] [Fintype G] {r : ℕ}

/-- `θ` approximates the unit phases `e` with error less than `2·2^{-p}` and lies in the disk. -/
def PhaseApprox (p : ℕ) (θ e : Fin r → ℂ) : Prop :=
  ∀ k, 2 ^ p * ‖θ k - e k‖ < 2 ∧ ‖θ k‖ ≤ 1

/-- A disk-grid array of `ℛ_r` records: every coefficient lies on the `p`-bit grid and has
modulus at most one. -/
def DiskGridArr (p : ℕ) (U : G → Fin r → ℂ) : Prop :=
  ∀ j k, IsFixed p (U j k) ∧ ‖U j k‖ ≤ 1

/-- `M̃_r` approximates `ℳ_r` on disk-grid operands with scaled error `E` per coefficient: the
guarantee of `prop:synthetic-convolution` (there `E = √2 M (3ℓ+1)`; in §8 `E_ring = M(3L+2)`). -/
def RingApprox (p : ℕ) (Mr : (G → Fin r → ℂ) → (G → Fin r → ℂ) → (G → Fin r → ℂ)) (E : ℝ) :
    Prop :=
  ∀ U V, DiskGridArr p U → DiskGridArr p V →
    ∀ j k, 2 ^ p * ‖Mr U V j k - synthConvNormG U V j k‖ ≤ E

/-- `M̃_ℂ(f, g) = Q_p(θ̃⁻ · ι⁻¹ M̃_r(ι Q_p(θ̃⁺ f), ι Q_p(θ̃⁺ g)))`. -/
noncomputable def cconvApprox (p : ℕ) (θp θm : Fin r → ℂ)
    (Mr : (G → Fin r → ℂ) → (G → Fin r → ℂ) → (G → Fin r → ℂ)) (f g : G × Fin r → ℂ) :
    G × Fin r → ℂ :=
  phaseQ p θm (iotaInv (Mr (iota (phaseQ p θp f)) (iota (phaseQ p θp g))))

variable [NeZero r]

/-- Error and norm of `M̃_ℂ` for operands of norms at most `X, Y ≤ 1`. -/
theorem cconvApprox_spec {p : ℕ} {E X Y : ℝ} {θp θm : Fin r → ℂ}
    {Mr : (G → Fin r → ℂ) → (G → Fin r → ℂ) → (G → Fin r → ℂ)}
    (hθp : PhaseApprox p θp fun k => twistRoot r k.val)
    (hθm : PhaseApprox p θm fun k => (starRingEnd ℂ) (twistRoot r k.val))
    (hMr : RingApprox p Mr E) {f g : G × Fin r → ℂ}
    (hf : ‖f‖ ≤ X) (hg : ‖g‖ ≤ Y) (hX : X ≤ 1) (hY : Y ≤ 1) :
    2 ^ p * ‖cconvApprox p θp θm Mr f g - convNormG f g‖ ≤
        E + (2 * X + Real.sqrt 2) * Y + X * (2 * Y + Real.sqrt 2) +
          (2 * (X * Y + E / 2 ^ p) + Real.sqrt 2) ∧
      ‖cconvApprox p θp θm Mr f g‖ ≤ X * Y + E / 2 ^ p := by
  have hp : (0 : ℝ) < 2 ^ p := by positivity
  have hX0 : 0 ≤ X := (norm_nonneg _).trans hf
  have hY0 : 0 ≤ Y := (norm_nonneg _).trans hg
  have hs0 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  set U' := iota (phaseQ p θp f) with hU'def
  set V' := iota (phaseQ p θp g) with hV'def
  set U := toSynth (r := r) f with hUdef
  set V := toSynth (r := r) g with hVdef
  have hfx : ∀ x, ‖f x‖ ≤ X := fun x => (norm_le_pi_norm f x).trans hf
  have hgx : ∀ x, ‖g x‖ ≤ Y := fun x => (norm_le_pi_norm g x).trans hg
  have hU'n : ∀ j k, ‖U' j k‖ ≤ X := fun j k => (norm_rhoC_mul_le (hθp k).2).trans (hfx _)
  have hV'n : ∀ j k, ‖V' j k‖ ≤ Y := fun j k => (norm_rhoC_mul_le (hθp k).2).trans (hgx _)
  have hU'd : DiskGridArr p U' := fun j k => ⟨isFixed_rhoC _ _, (hU'n j k).trans hX⟩
  have hV'd : DiskGridArr p V' := fun j k => ⟨isFixed_rhoC _ _, (hV'n j k).trans hY⟩
  have hUn : ∀ j k, ‖U j k‖ ≤ X := fun j k => by
    simp only [hUdef, toSynth, norm_twist_apply]
    exact hfx _
  have hUU : ∀ j k, ‖(U' - U) j k‖ ≤ (2 * X + Real.sqrt 2) / 2 ^ p := fun j k => by
    rw [le_div_iff₀ hp, mul_comm]
    have h := norm_rhoC_mul_sub_lt (x := f (j, k)) (hθp k).1
    have : 2 * ‖f (j, k)‖ + Real.sqrt 2 ≤ 2 * X + Real.sqrt 2 := by linarith [hfx (j, k)]
    exact h.le.trans this
  have hVV : ∀ j k, ‖(V' - V) j k‖ ≤ (2 * Y + Real.sqrt 2) / 2 ^ p := fun j k => by
    rw [le_div_iff₀ hp, mul_comm]
    have h := norm_rhoC_mul_sub_lt (x := g (j, k)) (hθp k).1
    have : 2 * ‖g (j, k)‖ + Real.sqrt 2 ≤ 2 * Y + Real.sqrt 2 := by linarith [hgx (j, k)]
    exact h.le.trans this
  -- the two input twists, propagated through the exact `ℳ_r`
  have h01 : ∀ j k, 2 ^ p * ‖synthConvNormG U' V' j k - synthConvNormG U V j k‖ ≤
      (2 * X + Real.sqrt 2) * Y + X * (2 * Y + Real.sqrt 2) := fun j k => by
    rw [synthConvNormG_sub]
    have hA := norm_synthConvNormG_le hUU hV'n (by positivity) hY0 j k
    have hB := norm_synthConvNormG_le hUn hVV hX0 (by positivity) j k
    calc 2 ^ p * ‖synthConvNormG (U' - U) V' j k + synthConvNormG U (V' - V) j k‖
        ≤ 2 ^ p * ((2 * X + Real.sqrt 2) / 2 ^ p * Y + X * ((2 * Y + Real.sqrt 2) / 2 ^ p)) := by
          gcongr
          exact (norm_add_le _ _).trans (add_le_add hA hB)
      _ = (2 * X + Real.sqrt 2) * Y + X * (2 * Y + Real.sqrt 2) := by
          field_simp
  -- the ring approximation and its output norm
  have hh : ∀ j k, 2 ^ p * ‖Mr U' V' j k - synthConvNormG U' V' j k‖ ≤ E := hMr U' V' hU'd hV'd
  have hhn : ∀ j k, ‖Mr U' V' j k‖ ≤ X * Y + E / 2 ^ p := fun j k => by
    have h1 : ‖Mr U' V' j k - synthConvNormG U' V' j k‖ ≤ E / 2 ^ p := by
      rw [le_div_iff₀ hp, mul_comm]; exact hh j k
    have h2 := norm_synthConvNormG_le hU'n hV'n hX0 hY0 j k
    calc ‖Mr U' V' j k‖ ≤ ‖Mr U' V' j k - synthConvNormG U' V' j k‖ +
          ‖synthConvNormG U' V' j k‖ := norm_le_norm_sub_add _ _
      _ ≤ X * Y + E / 2 ^ p := by linarith
  have hB0 : 0 ≤ X * Y + E / 2 ^ p := (norm_nonneg _).trans (hhn 0 ⟨0, Nat.pos_of_neZero r⟩)
  have hex : convNormG f g = fun x =>
      (starRingEnd ℂ) (twistRoot r x.2.val) * synthConvNormG U V x.1 x.2 := by
    rw [convNormG_eq_ofSynth]
    rfl
  have hout : ∀ x : G × Fin r,
      cconvApprox p θp θm Mr f g x = rhoC p (θm x.2 * Mr U' V' x.1 x.2) := fun x => rfl
  constructor
  · set B := E + (2 * X + Real.sqrt 2) * Y + X * (2 * Y + Real.sqrt 2) +
      (2 * (X * Y + E / 2 ^ p) + Real.sqrt 2) with hBdef
    have hpt : ∀ x : G × Fin r,
        2 ^ p * ‖(cconvApprox p θp θm Mr f g - convNormG f g) x‖ ≤ B := by
      rintro ⟨j, k⟩
      rw [Pi.sub_apply, hout, hex]
      simp only
      set h := Mr U' V' j k
      set h₀ := synthConvNormG U' V' j k
      set h₁ := synthConvNormG U V j k
      set c := (starRingEnd ℂ) (twistRoot r k.val)
      have hc : ‖c‖ = 1 := by rw [Complex.norm_conj, norm_twistRoot]
      have e1 : 2 ^ p * ‖rhoC p (θm k * h) - c * h‖ < 2 * ‖h‖ + Real.sqrt 2 :=
        norm_rhoC_mul_sub_lt (hθm k).1
      have e2 : 2 ^ p * ‖c * h - c * h₁‖ ≤
          E + ((2 * X + Real.sqrt 2) * Y + X * (2 * Y + Real.sqrt 2)) := by
        rw [← mul_sub, norm_mul, hc, one_mul]
        calc 2 ^ p * ‖h - h₁‖ ≤ 2 ^ p * ‖h - h₀‖ + 2 ^ p * ‖h₀ - h₁‖ := by
              rw [← mul_add]
              gcongr
              exact norm_sub_le_norm_sub_add_norm_sub _ _ _
          _ ≤ _ := add_le_add (hh j k) (h01 j k)
      have e3 := hhn j k
      calc 2 ^ p * ‖rhoC p (θm k * h) - c * h₁‖
          ≤ 2 ^ p * ‖rhoC p (θm k * h) - c * h‖ + 2 ^ p * ‖c * h - c * h₁‖ := by
            rw [← mul_add]
            gcongr
            exact norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ ≤ B := by rw [hBdef]; nlinarith
    have hBn : 0 ≤ B / 2 ^ p := by
      have := hpt (0, ⟨0, Nat.pos_of_neZero r⟩)
      have : 0 ≤ B := le_trans (by positivity) this
      positivity
    have : ‖cconvApprox p θp θm Mr f g - convNormG f g‖ ≤ B / 2 ^ p := by
      refine (pi_norm_le_iff_of_nonneg hBn).2 fun x => ?_
      rw [le_div_iff₀ hp, mul_comm]
      exact hpt x
    rw [le_div_iff₀ hp, mul_comm] at this
    exact this
  · refine (pi_norm_le_iff_of_nonneg hB0).2 fun x => ?_
    rw [hout]
    exact (norm_rhoC_mul_le (hθm x.2).2).trans (hhn x.1 x.2)

theorem sqrt_two_le_1415 : Real.sqrt 2 ≤ 1.415 := by
  rw [Real.sqrt_le_left (by norm_num)]
  norm_num

/-- "Precision and exact recovery": for `‖f‖ ≤ 1`, `‖g‖ ≤ .7` and `E ≤ 2^p/1000`, the computed complex convolution has
error at most `E + 9` (paper: `E_ring + 12`) and norm at most `.701`. -/
theorem cconvApprox_err {p : ℕ} {E : ℝ} {θp θm : Fin r → ℂ}
    {Mr : (G → Fin r → ℂ) → (G → Fin r → ℂ) → (G → Fin r → ℂ)}
    (hθp : PhaseApprox p θp fun k => twistRoot r k.val)
    (hθm : PhaseApprox p θm fun k => (starRingEnd ℂ) (twistRoot r k.val))
    (hMr : RingApprox p Mr E) (hE : 1000 * E ≤ 2 ^ p) {f g : G × Fin r → ℂ}
    (hf : ‖f‖ ≤ 1) (hg : ‖g‖ ≤ 7 / 10) :
    2 ^ p * ‖cconvApprox p θp θm Mr f g - convNormG f g‖ ≤ E + 9 ∧
      ‖cconvApprox p θp θm Mr f g‖ ≤ 701 / 1000 := by
  have hp : (0 : ℝ) < 2 ^ p := by positivity
  obtain ⟨h1, h2⟩ := cconvApprox_spec hθp hθm hMr hf hg le_rfl (by norm_num)
  have hE' : E / 2 ^ p ≤ 1 / 1000 := by
    rw [div_le_iff₀ hp]; linarith
  have hs := sqrt_two_le_1415
  constructor
  · refine h1.trans ?_
    nlinarith
  · refine h2.trans ?_
    linarith

end Computed

/-! ### Transport to a box -/

section Transport

variable {G : Type*} [AddCommGroup G] [Fintype G] {r : ℕ} [NeZero r]
  {B : Type*} [AddCommGroup B] [Fintype B]

theorem norm_comp_le {α β : Type*} [Fintype α] [Fintype β] (F : β → ℂ) (e : α → β) :
    ‖F ∘ e‖ ≤ ‖F‖ :=
  (pi_norm_le_iff_of_nonneg (norm_nonneg F)).2 fun a => norm_le_pi_norm F (e a)

/-- `M̃_ℂ` on an index group `B ≅ G × Fin r`. -/
noncomputable def cconvApproxVia (e : B ≃+ G × Fin r) (p : ℕ) (θp θm : Fin r → ℂ)
    (Mr : (G → Fin r → ℂ) → (G → Fin r → ℂ) → (G → Fin r → ℂ)) (f g : B → ℂ) : B → ℂ :=
  cconvApprox p θp θm Mr (f ∘ e.symm) (g ∘ e.symm) ∘ e

theorem cconvApproxVia_err (e : B ≃+ G × Fin r) {p : ℕ} {E : ℝ} {θp θm : Fin r → ℂ}
    {Mr : (G → Fin r → ℂ) → (G → Fin r → ℂ) → (G → Fin r → ℂ)}
    (hθp : PhaseApprox p θp fun k => twistRoot r k.val)
    (hθm : PhaseApprox p θm fun k => (starRingEnd ℂ) (twistRoot r k.val))
    (hMr : RingApprox p Mr E) (hE : 1000 * E ≤ 2 ^ p) {f g : B → ℂ}
    (hf : ‖f‖ ≤ 1) (hg : ‖g‖ ≤ 7 / 10) :
    2 ^ p * ‖cconvApproxVia e p θp θm Mr f g - convNormG f g‖ ≤ E + 9 ∧
      ‖cconvApproxVia e p θp θm Mr f g‖ ≤ 701 / 1000 := by
  obtain ⟨h1, h2⟩ := cconvApprox_err hθp hθm hMr hE ((norm_comp_le f e.symm).trans hf)
    ((norm_comp_le g e.symm).trans hg)
  have hconv : convNormG f g = convNormG (f ∘ e.symm) (g ∘ e.symm) ∘ e := by
    rw [convNormG_comp_symm]
    funext x
    simp
  constructor
  · have : cconvApproxVia e p θp θm Mr f g - convNormG f g =
        (cconvApprox p θp θm Mr (f ∘ e.symm) (g ∘ e.symm) -
          convNormG (f ∘ e.symm) (g ∘ e.symm)) ∘ e := by
      rw [hconv]; rfl
    rw [this]
    exact (mul_le_mul_of_nonneg_left (norm_comp_le _ _) (by positivity)).trans h1
  · exact (norm_comp_le _ _).trans h2

/-- The box `∏_{i ≤ d} ℤ/t_i` with last length `t_d = r`, split as `G × Fin r` with
`G = ∏_{i < d} ℤ/t_i`; the last coordinate is the polynomial coordinate. -/
noncomputable def boxSplit {d : ℕ} (t : Fin (d + 1) → ℕ) (h : t (Fin.last d) = r) :
    ((i : Fin (d + 1)) → ZMod (t i)) ≃+ ((i : Fin d) → ZMod (t i.castSucc)) × Fin r :=
  let e₁ : ((i : Fin (d + 1)) → ZMod (t i)) ≃+
      ZMod (t (Fin.last d)) × ((i : Fin d) → ZMod (t i.castSucc)) :=
    { (Fin.snocEquiv (fun i => ZMod (t i))).symm with map_add' := fun _ _ => rfl }
  e₁.trans (AddEquiv.prodComm.trans (AddEquiv.prodCongr (AddEquiv.refl _)
    ((ZMod.ringEquivCongr h).toAddEquiv.trans (ZMod.finEquiv r).symm.toAddEquiv)))

/-- The hypothesis `hM'` of the source-transform assembly, on the box with last length `r`. -/
theorem cconvApprox_box {d : ℕ} (t : Fin (d + 1) → ℕ) [∀ i, NeZero (t i)]
    (h : t (Fin.last d) = r) {p : ℕ} {E : ℝ} {θp θm : Fin r → ℂ}
    {Mr : (((i : Fin d) → ZMod (t i.castSucc)) → Fin r → ℂ) →
      (((i : Fin d) → ZMod (t i.castSucc)) → Fin r → ℂ) →
        (((i : Fin d) → ZMod (t i.castSucc)) → Fin r → ℂ)}
    (hθp : PhaseApprox p θp fun k => twistRoot r k.val)
    (hθm : PhaseApprox p θm fun k => (starRingEnd ℂ) (twistRoot r k.val))
    (hMr : RingApprox p Mr E) (hE : 1000 * E ≤ 2 ^ p) :
    ∀ f g : ((i : Fin (d + 1)) → ZMod (t i)) → ℂ, ‖f‖ ≤ 1 → ‖g‖ ≤ 7 / 10 →
      2 ^ p * ‖cconvApproxVia (boxSplit t h) p θp θm Mr f g - convNormD t f g‖ ≤ E + 9 ∧
        ‖cconvApproxVia (boxSplit t h) p θp θm Mr f g‖ ≤ 701 / 1000 := by
  intro f g hf hg
  rw [convNormD_eq_convNormG]
  exact cconvApproxVia_err (boxSplit t h) hθp hθm hMr hE hf hg

end Transport

/-! ### Roots of unity -/

section Roots

/-- Component errors below `2^{-p}` give a complex error below `√2·2^{-p} < 2·2^{-p}`. -/
theorem phase_of_cos_sin {p : ℕ} {φ c s : ℝ} (hc : 2 ^ p * |c - Real.cos φ| < 1)
    (hs : 2 ^ p * |s - Real.sin φ| < 1) :
    2 ^ p * ‖(⟨c, s⟩ : ℂ) - Complex.exp (φ * I)‖ < Real.sqrt 2 ∧
      2 ^ p * ‖(⟨c, s⟩ : ℂ) - Complex.exp (φ * I)‖ < 2 := by
  have hp : (0 : ℝ) < 2 ^ p := by positivity
  set z : ℂ := ⟨c, s⟩ - Complex.exp (φ * I) with hz
  have hre : 2 ^ p * z.re = 2 ^ p * (c - Real.cos φ) := by
    simp [hz, Complex.exp_ofReal_mul_I_re]
  have him : 2 ^ p * z.im = 2 ^ p * (s - Real.sin φ) := by
    simp [hz, Complex.exp_ofReal_mul_I_im]
  have h1 : |2 ^ p * z.re| < 1 := by rw [hre, abs_mul, abs_of_pos hp]; exact hc
  have h2 : |2 ^ p * z.im| < 1 := by rw [him, abs_mul, abs_of_pos hp]; exact hs
  have a1 : (2 ^ p * z.re) * (2 ^ p * z.re) < 1 := by
    have := mul_self_lt_mul_self (abs_nonneg _) h1
    rwa [abs_mul_abs_self, one_mul] at this
  have a2 : (2 ^ p * z.im) * (2 ^ p * z.im) < 1 := by
    have := mul_self_lt_mul_self (abs_nonneg _) h2
    rwa [abs_mul_abs_self, one_mul] at this
  have hsq : (2 ^ p * ‖z‖) ^ 2 < 2 := by
    rw [mul_pow, Complex.sq_norm, Complex.normSq_apply]
    nlinarith
  have hlt : 2 ^ p * ‖z‖ < Real.sqrt 2 := (Real.lt_sqrt (by positivity)).2 hsq
  have hs2 : Real.sqrt 2 < 2 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
  exact ⟨hlt, hlt.trans hs2⟩

/-- Shrink by `1 − 2^{-(p+2)}`, then truncate: a disk-grid phase. -/
noncomputable def diskPhase (p : ℕ) (z : ℂ) : ℂ :=
  rhoC p (((1 - 1 / 2 ^ (p + 2) : ℝ) : ℂ) * z)

/-- An approximation within `2^{-(p+2)}` of a unit phase becomes a disk-grid phase with error
less than `2·2^{-p}`. -/
theorem diskPhase_spec {p : ℕ} {z e : ℂ} (he : ‖e‖ = 1) (hz : 2 ^ (p + 2) * ‖z - e‖ ≤ 1) :
    IsFixed p (diskPhase p z) ∧ ‖diskPhase p z‖ ≤ 1 ∧ 2 ^ p * ‖diskPhase p z - e‖ < 2 := by
  have hp : (0 : ℝ) < 2 ^ p := by positivity
  set η : ℝ := 1 / 2 ^ (p + 2) with hη
  have hη0 : 0 < η := by positivity
  have hpη : 2 ^ p * η = 1 / 4 := by rw [hη, pow_add]; field_simp; norm_num
  have hη4 : η ≤ 1 / 4 := by
    have : (1 : ℝ) ≤ 2 ^ p := one_le_pow₀ (by norm_num)
    nlinarith
  have hze : ‖z - e‖ ≤ η := by
    rw [hη, le_div_iff₀ (by positivity), mul_comm]; exact hz
  have hzn : ‖z‖ ≤ 1 + η := by
    have := norm_le_norm_sub_add z e
    linarith
  set w : ℂ := ((1 - η : ℝ) : ℂ) * z with hw
  have hwn : ‖w‖ ≤ 1 := by
    rw [hw, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
    nlinarith [norm_nonneg z]
  have hwe : ‖w - e‖ ≤ η + η * (1 + η) := by
    have : w - e = (z - e) - (η : ℂ) * z := by rw [hw]; push_cast; ring
    rw [this]
    calc ‖(z - e) - (η : ℂ) * z‖ ≤ ‖z - e‖ + ‖(η : ℂ) * z‖ := norm_sub_le _ _
      _ ≤ η + η * (1 + η) := by
          rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hη0.le]
          gcongr
  refine ⟨isFixed_rhoC _ _, (norm_rhoC_le _ _).trans hwn, ?_⟩
  have h1 : 2 ^ p * ‖rhoC p w - w‖ < Real.sqrt 2 := by
    have := norm_rhoC_sub_lt p w
    rw [lt_div_iff₀ hp] at this
    linarith
  have hs : Real.sqrt 2 < 23 / 16 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have h2 : 2 ^ p * ‖w - e‖ ≤ 1 / 2 + 1 / 16 := by
    calc 2 ^ p * ‖w - e‖ ≤ 2 ^ p * (η + η * (1 + η)) := by gcongr
      _ = 2 * (2 ^ p * η) + (2 ^ p * η) * η := by ring
      _ ≤ 1 / 2 + 1 / 16 := by rw [hpη]; nlinarith
  calc 2 ^ p * ‖diskPhase p z - e‖ ≤ 2 ^ p * ‖rhoC p w - w‖ + 2 ^ p * ‖w - e‖ := by
        rw [← mul_add]
        gcongr
        exact norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ < 2 := by linarith

/-- Truncation toward zero of a real at `q` fractional bits. -/
noncomputable def truncR (q : ℕ) (y : ℝ) : ℝ := (rho0 (2 ^ q * y) : ℝ) / 2 ^ q

theorem abs_truncR_sub_le (q : ℕ) (y : ℝ) : |truncR q y - y| ≤ 1 / 2 ^ q := by
  have hq : (0 : ℝ) < 2 ^ q := by positivity
  have h := abs_rho0_sub_lt (2 ^ q * y)
  have e : truncR q y - y = ((rho0 (2 ^ q * y) : ℝ) - 2 ^ q * y) / 2 ^ q := by
    unfold truncR; field_simp
  rw [e, abs_div, abs_of_pos hq]
  exact div_le_div_of_nonneg_right h.le hq.le

/-- Fixed-point Taylor terms of `e^{ix}` at `q` fractional bits: `u₀ = 1`,
`u_{m+1} = Q_q(u_m x / (m + 1))`, approximating `x^m / m!`. -/
noncomputable def taylorTerm (q : ℕ) (x : ℝ) : ℕ → ℝ
  | 0 => 1
  | m + 1 => truncR q (taylorTerm q x m * x / (m + 1))

/-- `∑_{m<n} i^m u_m`: real part `u₀ − u₂ + u₄ − ⋯ ≈ cos x`, imaginary part
`u₁ − u₃ + ⋯ ≈ sin x`. All additions are exact on the `q`-bit grid. -/
noncomputable def taylorExpI (q : ℕ) (x : ℝ) (n : ℕ) : ℂ :=
  ∑ m ∈ Finset.range n, I ^ m * (taylorTerm q x m : ℂ)

/-- One step of the term recursion. -/
theorem term_step {x δ : ℝ} {u : ℕ → ℝ} (hstep : ∀ m : ℕ, |u (m + 1) - u m * x / (m + 1)| ≤ δ)
    (m : ℕ) :
    |u (m + 1) - x ^ (m + 1) / (m + 1).factorial| ≤
      δ + |u m - x ^ m / m.factorial| * |x| / (m + 1) := by
  have hm : (0 : ℝ) < m + 1 := by positivity
  have hf : (0 : ℝ) < m.factorial := by exact_mod_cast Nat.factorial_pos m
  have e : u (m + 1) - x ^ (m + 1) / (m + 1).factorial =
      (u (m + 1) - u m * x / (m + 1)) + (u m - x ^ m / m.factorial) * x / (m + 1) := by
    rw [Nat.factorial_succ]
    push_cast
    field_simp
    ring
  rw [e]
  calc |(u (m + 1) - u m * x / (m + 1)) + (u m - x ^ m / m.factorial) * x / (m + 1)|
      ≤ |u (m + 1) - u m * x / (m + 1)| + |(u m - x ^ m / m.factorial) * x / (m + 1)| :=
        abs_add_le _ _
    _ ≤ δ + |u m - x ^ m / m.factorial| * |x| / (m + 1) := by
        rw [abs_div, abs_mul, abs_of_pos hm]
        exact add_le_add_left (hstep m) _

/-- Every computed term is within `6δ` of `x^m/m!` when `|x| ≤ 4` and each step errs by at
most `δ`. -/
theorem abs_term_sub_le {x δ : ℝ} {u : ℕ → ℝ} (hx : |x| ≤ 4) (hδ : 0 ≤ δ) (h0 : u 0 = 1)
    (hstep : ∀ m : ℕ, |u (m + 1) - u m * x / (m + 1)| ≤ δ) (m : ℕ) :
    |u m - x ^ m / m.factorial| ≤ 6 * δ := by
  set ε : ℕ → ℝ := fun m => |u m - x ^ m / m.factorial| with hε
  have hx0 : 0 ≤ |x| := abs_nonneg x
  have step : ∀ m : ℕ, ε (m + 1) ≤ δ + ε m * |x| / (m + 1) := term_step hstep
  have e0 : ε 0 = 0 := by simp [hε, h0]
  have e1 : ε 1 ≤ δ := by
    have := step 0; rw [e0] at this; simpa using this
  have e2 : ε 2 ≤ 3 * δ := by
    have := step 1
    have h : ε 1 * |x| / ((1 : ℕ) + 1 : ℝ) ≤ δ * 4 / 2 := by
      norm_num
      have := mul_le_mul e1 hx (abs_nonneg _) hδ
      linarith
    linarith
  have e3 : ε 3 ≤ 5 * δ := by
    have := step 2
    have h : ε 2 * |x| / ((2 : ℕ) + 1 : ℝ) ≤ 3 * δ * 4 / 3 := by
      norm_num
      have := mul_le_mul e2 hx (abs_nonneg _) (by linarith)
      linarith
    linarith
  have e4 : ε 4 ≤ 6 * δ := by
    have := step 3
    have h : ε 3 * |x| / ((3 : ℕ) + 1 : ℝ) ≤ 5 * δ * 4 / 4 := by
      norm_num
      have := mul_le_mul e3 hx (abs_nonneg _) (by linarith)
      linarith
    linarith
  have big : ∀ m, 4 ≤ m → ε m ≤ 6 * δ := by
    intro m hm
    induction m, hm using Nat.le_induction with
    | base => exact e4
    | succ m hm ih =>
      have := step m
      have hm5 : (5 : ℝ) ≤ m + 1 := by
        have : (4 : ℝ) ≤ m := by exact_mod_cast hm
        linarith
      have h : ε m * |x| / (m + 1) ≤ 6 * δ * 4 / 5 := by
        have hprod : ε m * |x| ≤ 6 * δ * 4 := mul_le_mul ih hx (abs_nonneg _) (by linarith)
        rw [div_le_div_iff₀ (by linarith) (by norm_num)]
        nlinarith [abs_nonneg (u m - x ^ m / m.factorial)]
      linarith
  rcases (by omega : m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3 ∨ 4 ≤ m) with h | h | h | h | h
  · subst h; rw [show |u 0 - x ^ 0 / (Nat.factorial 0)| = ε 0 from rfl, e0]; linarith
  · subst h; exact (show ε 1 ≤ 6 * δ by linarith)
  · subst h; exact (show ε 2 ≤ 6 * δ by linarith)
  · subst h; exact (show ε 3 ≤ 6 * δ by linarith)
  · exact big m h

theorem taylorTerm_step (q : ℕ) (x : ℝ) (m : ℕ) :
    |taylorTerm q x (m + 1) - taylorTerm q x m * x / (m + 1)| ≤ 1 / 2 ^ q :=
  abs_truncR_sub_le q _

theorem eight_pow_le (n : ℕ) : 8 ^ n ≤ 512 * n.factorial := by
  rcases (by omega : n < 8 ∨ 8 ≤ n) with h | h
  · interval_cases n <;> decide
  · induction n, h using Nat.le_induction with
    | base => decide
    | succ m hm ih =>
      rw [pow_succ, Nat.factorial_succ]
      calc 8 ^ m * 8 ≤ 512 * m.factorial * 8 := Nat.mul_le_mul_right _ ih
        _ ≤ 512 * m.factorial * (m + 1) := Nat.mul_le_mul_left _ (by omega)
        _ = 512 * ((m + 1) * m.factorial) := by ring

theorem four_pow_div_factorial_le (n : ℕ) : (4 : ℝ) ^ n / n.factorial ≤ 512 / 2 ^ n := by
  have hf : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  rw [div_le_div_iff₀ hf (by positivity)]
  have h : ((8 ^ n : ℕ) : ℝ) ≤ ((512 * n.factorial : ℕ) : ℝ) := by exact_mod_cast eight_pow_le n
  push_cast at h
  calc (4 : ℝ) ^ n * 2 ^ n = 8 ^ n := by rw [← mul_pow]; norm_num
    _ ≤ 512 * n.factorial := h

/-- Error of the fixed-point Taylor sum for `e^{ix}`, `|x| ≤ 4`, `n ≥ 7` terms. -/
theorem norm_taylorExpI_sub_le {q n : ℕ} {x : ℝ} (hx : |x| ≤ 4) (hn : 7 ≤ n) :
    ‖taylorExpI q x n - Complex.exp (x * I)‖ ≤ 6 * n / 2 ^ q + 1024 / 2 ^ n := by
  have hq : (0 : ℝ) < 2 ^ q := by positivity
  have hterm : ∀ m, |taylorTerm q x m - x ^ m / m.factorial| ≤ 6 * (1 / 2 ^ q) :=
    abs_term_sub_le hx (by positivity) rfl (taylorTerm_step q x)
  have hsum : ‖taylorExpI q x n -
      ∑ m ∈ Finset.range n, ((x : ℂ) * I) ^ m / (m.factorial : ℂ)‖ ≤ 6 * n / 2 ^ q := by
    unfold taylorExpI
    rw [← Finset.sum_sub_distrib]
    have e : ∀ m ∈ Finset.range n, I ^ m * (taylorTerm q x m : ℂ) -
        ((x : ℂ) * I) ^ m / (m.factorial : ℂ) =
          I ^ m * ((taylorTerm q x m - x ^ m / m.factorial : ℝ) : ℂ) := by
      intro m _
      push_cast
      rw [mul_pow]
      ring
    rw [Finset.sum_congr rfl e]
    calc ‖∑ m ∈ Finset.range n, I ^ m * ((taylorTerm q x m - x ^ m / m.factorial : ℝ) : ℂ)‖
        ≤ ∑ m ∈ Finset.range n, ‖I ^ m * ((taylorTerm q x m - x ^ m / m.factorial : ℝ) : ℂ)‖ :=
          norm_sum_le _ _
      _ ≤ ∑ _m ∈ Finset.range n, 6 * (1 / 2 ^ q) := by
          refine Finset.sum_le_sum fun m _ => ?_
          rw [norm_mul, norm_pow, Complex.norm_I, one_pow, one_mul, Complex.norm_real,
            Real.norm_eq_abs]
          exact hterm m
      _ = 6 * n / 2 ^ q := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          ring
  have hexp : ‖Complex.exp (x * I) -
      ∑ m ∈ Finset.range n, ((x : ℂ) * I) ^ m / (m.factorial : ℂ)‖ ≤ 1024 / 2 ^ n := by
    have hxI : ‖(x : ℂ) * I‖ = |x| := by
      rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
    have hb := Complex.exp_bound' (x := (x : ℂ) * I) (n := n) (by
      rw [hxI, div_le_iff₀ (by positivity)]
      have : (7 : ℝ) ≤ n := by exact_mod_cast hn
      push_cast
      linarith)
    refine hb.trans ?_
    rw [hxI]
    have h4 : |x| ^ n / n.factorial ≤ (4 : ℝ) ^ n / n.factorial := by
      gcongr
    have := four_pow_div_factorial_le n
    have e : (1024 : ℝ) / 2 ^ n = 2 * (512 / 2 ^ n) := by ring
    rw [e]
    linarith
  calc ‖taylorExpI q x n - Complex.exp (x * I)‖
      ≤ ‖taylorExpI q x n - ∑ m ∈ Finset.range n, ((x : ℂ) * I) ^ m / (m.factorial : ℂ)‖ +
        ‖∑ m ∈ Finset.range n, ((x : ℂ) * I) ^ m / (m.factorial : ℂ) - Complex.exp (x * I)‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ 6 * n / 2 ^ q + 1024 / 2 ^ n := by
        rw [norm_sub_rev _ (Complex.exp _)]
        exact add_le_add hsum hexp

/-- With `n ≥ p + 12` terms and `g` guard bits, `16 n ≤ 2^g`, the fixed-point Taylor sum at
`p + g` bits approximates `e^{ix}` within `(5/8)·2^{-p}` for `|x| ≤ 4`. -/
theorem taylorExpI_err {p g n : ℕ} {x : ℝ} (hx : |x| ≤ 4) (hn : p + 12 ≤ n)
    (hg : 16 * n ≤ 2 ^ g) :
    2 ^ p * ‖taylorExpI (p + g) x n - Complex.exp (x * I)‖ ≤ 5 / 8 := by
  have hp : (0 : ℝ) < 2 ^ p := by positivity
  have h := norm_taylorExpI_sub_le (q := p + g) hx (by omega : 7 ≤ n)
  have hg' : (16 : ℝ) * n ≤ 2 ^ g := by exact_mod_cast hg
  have hn' : (2 : ℝ) ^ (p + 12) ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) hn
  have hnpos : (0 : ℝ) < n := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
    linarith
  have a1 : (2 : ℝ) ^ p * (6 * n / 2 ^ (p + g)) ≤ 3 / 8 := by
    have e : (2 : ℝ) ^ p * (6 * n / 2 ^ (p + g)) = 6 * n / 2 ^ g := by
      rw [pow_add]; field_simp
    rw [e, div_le_iff₀ (by positivity)]
    linarith
  have a2 : (2 : ℝ) ^ p * (1024 / 2 ^ n) ≤ 1 / 4 := by
    have e : (2 : ℝ) ^ p * (1024 / 2 ^ n) = 2 ^ p * 1024 / 2 ^ n := by ring
    rw [e, div_le_iff₀ (by positivity)]
    rw [pow_add] at hn'
    nlinarith
  calc 2 ^ p * ‖taylorExpI (p + g) x n - Complex.exp (x * I)‖
      ≤ 2 ^ p * (6 * n / 2 ^ (p + g) + 1024 / 2 ^ n) := by gcongr
    _ = 2 ^ p * (6 * n / 2 ^ (p + g)) + 2 ^ p * (1024 / 2 ^ n) := by ring
    _ ≤ 5 / 8 := by linarith

/-- The cosine and sine components, each within `2^{-p}`. -/
theorem taylor_cos_sin_err {p g n : ℕ} {x : ℝ} (hx : |x| ≤ 4) (hn : p + 12 ≤ n)
    (hg : 16 * n ≤ 2 ^ g) :
    2 ^ p * |(taylorExpI (p + g) x n).re - Real.cos x| < 1 ∧
      2 ^ p * |(taylorExpI (p + g) x n).im - Real.sin x| < 1 := by
  have h := taylorExpI_err hx hn hg
  have hp : (0 : ℝ) < 2 ^ p := by positivity
  set z := taylorExpI (p + g) x n - Complex.exp (x * I)
  have hre : (taylorExpI (p + g) x n).re - Real.cos x = z.re := by
    simp [z, Complex.exp_ofReal_mul_I_re]
  have him : (taylorExpI (p + g) x n).im - Real.sin x = z.im := by
    simp [z, Complex.exp_ofReal_mul_I_im]
  rw [hre, him]
  constructor
  · calc 2 ^ p * |z.re| ≤ 2 ^ p * ‖z‖ := by gcongr; exact Complex.abs_re_le_norm z
      _ < 1 := by linarith
  · calc 2 ^ p * |z.im| ≤ 2 ^ p * ‖z‖ := by gcongr; exact Complex.abs_im_le_norm z
      _ < 1 := by linarith

/-- An explicit choice: `n = 2p` terms and `g = ⌈log₂(2p)⌉ + 4` guard bits, for `p ≥ 12`. -/
theorem taylorExpI_err_explicit {p : ℕ} (hp : 12 ≤ p) {x : ℝ} (hx : |x| ≤ 4) :
    2 ^ p * ‖taylorExpI (p + (Nat.clog 2 (2 * p) + 4)) x (2 * p) - Complex.exp (x * I)‖ ≤
      5 / 8 := by
  refine taylorExpI_err hx (by omega) ?_
  rw [pow_add]
  have := Nat.le_pow_clog (b := 2) (by norm_num) (2 * p)
  omega

theorem norm_exp_mul_I_sub_le (x y : ℝ) :
    ‖Complex.exp (x * I) - Complex.exp (y * I)‖ ≤ |x - y| := by
  have e : Complex.exp (x * I) - Complex.exp (y * I) =
      Complex.exp (y * I) * (Complex.exp (I * ((x - y : ℝ) : ℂ)) - 1) := by
    rw [mul_sub, ← Complex.exp_add, mul_one]
    congr 2
    push_cast
    ring
  rw [e, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul, ← Real.norm_eq_abs]
  exact Real.norm_exp_I_mul_ofReal_sub_one_le

theorem twistRoot_eq_exp (r k : ℕ) :
    twistRoot r k = Complex.exp (((Real.pi * k / r : ℝ) : ℂ) * I) := by
  unfold twistRoot
  congr 1
  push_cast
  ring

/-- The computed twist phase from an angle `x ≈ πk/r`: Taylor sum at `p + 2 + g` bits, then
`diskPhase`. -/
noncomputable def twistPhase (p g n : ℕ) (x : ℝ) : ℂ :=
  diskPhase p (taylorExpI (p + 2 + g) x n)

/-- `θ̃_k` for `ζ^k = e^{πik/r}`, `k ≤ r`, from an angle within `2^{-(p+4)}` of `πk/r`. -/
theorem twistPhase_spec {p g n r k : ℕ} (hkr : k ≤ r) {x : ℝ}
    (hxk : 2 ^ (p + 4) * |x - Real.pi * k / r| ≤ 1) (hn : p + 14 ≤ n) (hg : 16 * n ≤ 2 ^ g) :
    IsFixed p (twistPhase p g n x) ∧ ‖twistPhase p g n x‖ ≤ 1 ∧
      2 ^ p * ‖twistPhase p g n x - twistRoot r k‖ < 2 := by
  have hp4 : (0 : ℝ) < 2 ^ (p + 4) := by positivity
  have hxk' : |x - Real.pi * k / r| ≤ 1 / 16 := by
    have : (16 : ℝ) ≤ 2 ^ (p + 4) :=
      calc (16 : ℝ) = 2 ^ 4 := by norm_num
        _ ≤ 2 ^ (p + 4) := pow_le_pow_right₀ (by norm_num) (by omega)
    have h0 := abs_nonneg (x - Real.pi * k / r)
    nlinarith
  have hang : 0 ≤ Real.pi * k / r ∧ Real.pi * k / r ≤ Real.pi := by
    constructor
    · positivity
    · rcases Nat.eq_zero_or_pos r with hr | hr
      · subst hr; simp [Real.pi_pos.le]
      · rw [div_le_iff₀ (by exact_mod_cast hr)]
        have : (k : ℝ) ≤ r := by exact_mod_cast hkr
        nlinarith [Real.pi_pos]
  have hx : |x| ≤ 4 := by
    have hpi := Real.pi_lt_d2
    rw [abs_le] at hxk' ⊢
    constructor <;> nlinarith
  have hT := taylorExpI_err (p := p + 2) hx (by omega) hg
  have hA : 2 ^ (p + 2) * ‖Complex.exp (x * I) - twistRoot r k‖ ≤ 1 / 4 := by
    rw [twistRoot_eq_exp]
    have := norm_exp_mul_I_sub_le x (Real.pi * k / r)
    calc 2 ^ (p + 2) * ‖Complex.exp (x * I) - Complex.exp (((Real.pi * k / r : ℝ) : ℂ) * I)‖
        ≤ 2 ^ (p + 2) * |x - Real.pi * k / r| := by gcongr
      _ = (2 ^ (p + 4) * |x - Real.pi * k / r|) / 4 := by rw [show p + 4 = p + 2 + 2 by ring, pow_add]; ring
      _ ≤ 1 / 4 := by linarith
  apply diskPhase_spec (norm_twistRoot k)
  calc 2 ^ (p + 2) * ‖taylorExpI (p + 2 + g) x n - twistRoot r k‖
      ≤ 2 ^ (p + 2) * ‖taylorExpI (p + 2 + g) x n - Complex.exp (x * I)‖ +
        2 ^ (p + 2) * ‖Complex.exp (x * I) - twistRoot r k‖ := by
        rw [← mul_add]
        gcongr
        exact norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ 1 := by linarith

/-- Conjugate phases serve for `ζ^{-k}`. -/
theorem phaseApprox_conj {r p : ℕ} {θ e : Fin r → ℂ} (h : PhaseApprox p θ e) :
    PhaseApprox p (fun k => (starRingEnd ℂ) (θ k)) fun k => (starRingEnd ℂ) (e k) := fun k =>
  ⟨by rw [norm_conj_sub]; exact (h k).1, by rw [Complex.norm_conj]; exact (h k).2⟩

/-- The twist arrays `θ̃⁺_k = twistPhase(x_k)`, `θ̃⁻_k = conj θ̃⁺_k` meet the hypotheses of
`cconvApprox_err` when each angle `x_k` is within `2^{-(p+4)}` of `πk/r`. -/
theorem twistPhase_phaseApprox {p g n r : ℕ} {x : Fin r → ℝ}
    (hx : ∀ k : Fin r, 2 ^ (p + 4) * |x k - Real.pi * k.val / r| ≤ 1) (hn : p + 14 ≤ n)
    (hg : 16 * n ≤ 2 ^ g) :
    PhaseApprox p (fun k => twistPhase p g n (x k)) (fun k => twistRoot r k.val) ∧
      PhaseApprox p (fun k => (starRingEnd ℂ) (twistPhase p g n (x k)))
        (fun k => (starRingEnd ℂ) (twistRoot r k.val)) := by
  have h : PhaseApprox p (fun k => twistPhase p g n (x k)) (fun k => twistRoot r k.val) :=
    fun k => by
      obtain ⟨-, h1, h2⟩ := twistPhase_spec k.isLt.le (hx k) hn hg
      exact ⟨h2, h1⟩
  exact ⟨h, phaseApprox_conj h⟩

end Roots

end IntegerMultBounds.MathlibTM2.Mult.ComplexConv

