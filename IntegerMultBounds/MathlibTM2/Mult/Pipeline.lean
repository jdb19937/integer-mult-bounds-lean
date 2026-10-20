module

public import IntegerMultBounds.MathlibTM2.Mult.BandSpec
import IntegerMultBounds.MathlibTM2.Mult.SourceErrScaled
public import IntegerMultBounds.MathlibTM2.Mult.Chirp
public import IntegerMultBounds.MathlibTM2.Mult.SynthErr
public import IntegerMultBounds.MathlibTM2.Mult.SourceErr
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Algebra.Order.Ring.Star

/-!
# The numeric pipeline with concrete ingredients

Paper §8. Every ingredient of the computed product is a fixed function of the operand length
`n`: the sizes of `Mult/Sizes.lean` (`b`, `p = 6b`, `d`, `α`, `γ`, `s_i`, `t_i`, `r`,
`T = ∏ t_i`, `S = ∏ s_i`), the integer weight tables of `Resampling.WeightTable`, the chirp
kernel of `Mult/Chirp.lean`, and the twist tables below, all computed from Machin's `π`
(`WeightTable.piQ`) and fixed-point Taylor sums. `pipelineCoeffs n x y` is the list of `S`
natural coefficients of `x y` in radix `2^b`.

## Stages, in the order a machine computes them

Tables, once per `n`:

1. `tableA`, `tableE`, `tableD` on every axis (`WeightTable.tables_ok`: within two units of
   `2^p` times the exact weights).
2. The chirp axis tables `axisPhase` and the kernel `chirpKernel n = chirpProd p g t s` with the
   guard `g = ⌈log₂ d⌉ + 4`.
3. The twist tables `twistPlus p r`, `twistMinus p r`: angles
   `x_k = ⌊piQ (p+4) · k / r⌋ / 2^{5(p+4)}` within `2^{-(p+4)}` of `πk/r` (`twistAngle_err`),
   Taylor sums of `e^{i x_k}` with `p + 14` terms, rounded into the `p`-bit disk.

Per product:

4. `bitsMSB n x`, `bitsMSB n y`: the `n` input bits; `digitsOf b`: radix-`2^b` digits;
   `scaledDigits S b`: digits times `2^{-(b+2)}` on `ℤ/S`.
5. Source transform `srcMap n = F̃ ∘ Φ` on both operands: the CRT layout `u ↦ u ∘ Φ⁻¹`
   onto `∏ ℤ/s_i`; `Ã = lineA` along every axis (window `windowA p α = ⌊√(pα²)⌋ + 1`) onto
   `∏ ℤ/t_i`; the chirp step `Q_p(ā' · M̃_ℂ(a', Q_p(ā' · x)))`, where `M̃_ℂ = convBox n`
   twists by `θ̃⁺`, runs the synthetic convolution `synthMr` over `ℛ_r` (forward rounds,
   pointwise `Q_p(fg/r)`, opposite rounds, scaling by `M`) and untwists by `θ̃⁻`;
   `B̃₀ = lineB` along every axis (`α²` Horner steps, window `fastWindow p α`); the exact
   scale `2^γ`.
6. The pointwise product of the two transforms, truncated by `Q_p`.
7. Opposite transform `oppMap n = Φ⁻¹ ∘ F̃⁺` with `F̃⁺ = conj ∘ F̃ ∘ conj`.
8. The exact scale `16 S`, then `2^{2b} S`; coefficient `i < S` is the rounded real part.

## Result

`pipeline_correct`: for all large `n` and all `x y` with `Nat.size x, Nat.size y ≤ n`,
`evalBase (2^b) (pipelineCoeffs n x y) = x y`. The proof feeds the concrete ingredients to
`FastB0.sourceErr_of_tables_fast` (tables, chirp kernel, `convBox_spec`) and the result to
`exact_product_crt`; the size conditions are `Sizes.eventually_big`,
`Sizes.eventually_small` and `Sizes.eventually_margins` with `L = log₂ T`.
-/

@[expose] public section


open IntegerMultBounds IntegerMultBounds.NLogN Complex
open IntegerMultBounds.MathlibTM2.Mult.ComplexConv IntegerMultBounds.MathlibTM2.Mult.SynthErr IntegerMultBounds.MathlibTM2.Mult.Chirp
open IntegerMultBounds.Resampling.WeightTable (piQ piQ_err fdiv_err)
open scoped Function

namespace IntegerMultBounds.MathlibTM2.Mult.Pipeline

/-! ### Input bits -/

/-- The `n` low bits of `x`, most significant first. -/
def bitsMSB : ℕ → ℕ → List Bool
  | 0, _ => []
  | n + 1, x => x.testBit n :: bitsMSB n x

theorem length_bitsMSB (n x : ℕ) : (bitsMSB n x).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [bitsMSB, ih]

theorem binaryValue_bitsMSB (n x : ℕ) : binaryValue (bitsMSB n x) = x % 2 ^ n := by
  induction n with
  | zero => simp [bitsMSB, binaryValue, Nat.mod_one]
  | succ n ih =>
    simp only [bitsMSB, binaryValue, length_bitsMSB, ih, Nat.mod_pow_succ,
      Nat.testBit_eq_decide_div_mod_eq]
    have h := Nat.mod_two_eq_zero_or_one (x / 2 ^ n)
    rcases h with h | h <;> simp [h, Nat.add_comm]

theorem binaryValue_bitsMSB_of_size {n x : ℕ} (hx : Nat.size x ≤ n) :
    binaryValue (bitsMSB n x) = x := by
  rw [binaryValue_bitsMSB, Nat.mod_eq_of_lt (Nat.size_le.1 hx)]

/-! ### Twist angles -/

/-- The angle numerator `⌊piQ (p+4) · k / r⌋ ≈ 2^{5(p+4)} π k / r`. -/
def twistAngleNum (p r k : ℕ) : ℤ := (piQ (p + 4) * k) / r

/-- The twist angle `x_k = twistAngleNum / 2^{5(p+4)} ≈ π k / r`. -/
noncomputable def twistAngle (p r k : ℕ) : ℝ := (twistAngleNum p r k : ℝ) / 2 ^ (5 * (p + 4))

theorem twistAngle_err (p r k : ℕ) (hr : 0 < r) (hk : k ≤ r) :
    2 ^ (p + 4) * |twistAngle p r k - Real.pi * k / r| ≤ 1 := by
  set P := p + 4 with hP
  have hP2 : 2 ≤ P := by omega
  have hN : (0 : ℝ) < r := by exact_mod_cast hr
  have hcN1 : |(k : ℝ) / r| ≤ 1 := by
    rw [abs_div, abs_of_pos hN, abs_of_nonneg (Nat.cast_nonneg _), div_le_one hN]
    exact_mod_cast hk
  have h1 := fdiv_err (piQ P * k) r (by exact_mod_cast hr)
  have h2 := piQ_err P (by omega)
  have h3 : |(twistAngleNum p r k : ℝ) - 2 ^ (5 * P) * Real.pi * k / r| ≤ 100 * P + 2 := by
    have e : (twistAngleNum p r k : ℝ) - 2 ^ (5 * P) * Real.pi * k / r =
        ((((piQ P * k / r : ℤ) : ℝ)) - ((piQ P * k : ℤ) : ℝ) / ((r : ℤ) : ℝ)) +
          ((k : ℝ) / r) * ((piQ P : ℝ) - 2 ^ (5 * P) * Real.pi) := by
      unfold twistAngleNum
      rw [← hP]
      push_cast
      field_simp
      ring
    rw [e]
    have h4 : |(k : ℝ) / r * ((piQ P : ℝ) - 2 ^ (5 * P) * Real.pi)| ≤ 1 * (20 * (5 * P) + 1) := by
      rw [abs_mul]
      exact mul_le_mul hcN1 h2 (abs_nonneg _) zero_le_one
    calc _ ≤ |(((piQ P * k / r : ℤ) : ℝ)) - ((piQ P * k : ℤ) : ℝ) / ((r : ℤ) : ℝ)| +
          |(k : ℝ) / r * ((piQ P : ℝ) - 2 ^ (5 * P) * Real.pi)| := abs_add_le _ _
      _ ≤ 1 + 1 * (20 * (5 * P) + 1) := add_le_add h1 h4
      _ = 100 * P + 2 := by ring
  have hpow : (100 * (P : ℝ) + 2) ≤ 2 ^ (4 * P) := by exact_mod_cast lin_le_pow_four P hP2
  have e2 : twistAngle p r k - Real.pi * k / r =
      ((twistAngleNum p r k : ℝ) - 2 ^ (5 * P) * Real.pi * k / r) / 2 ^ (5 * P) := by
    unfold twistAngle
    rw [← hP]
    field_simp
  have h5 : (2 : ℝ) ^ (5 * P) = 2 ^ P * 2 ^ (4 * P) := by rw [← pow_add]; ring_nf
  rw [e2, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ (5 * P))]
  set A := |(twistAngleNum p r k : ℝ) - 2 ^ (5 * P) * Real.pi * k / r| with hA
  rw [h5, mul_div_assoc', div_le_one (by positivity)]
  have : (0 : ℝ) < 2 ^ P := by positivity
  nlinarith

/-- The twist table `θ̃⁺_k`: Taylor sum of `e^{i x_k}` with `p + 14` terms and
`⌈log₂ (p + 14)⌉ + 4` guard bits, rounded into the `p`-bit disk. -/
noncomputable def twistPlus (p r : ℕ) (k : Fin r) : ℂ :=
  twistPhase p (taylorGuard p 0) (taylorTerms p 0) (twistAngle p r k)

/-- The twist table `θ̃⁻_k = conj θ̃⁺_k`. -/
noncomputable def twistMinus (p r : ℕ) (k : Fin r) : ℂ := starRingEnd ℂ (twistPlus p r k)

theorem twist_phaseApprox (p r : ℕ) :
    PhaseApprox p (twistPlus p r) (fun k => twistRoot r k.val) ∧
      PhaseApprox p (twistMinus p r) (fun k => (starRingEnd ℂ) (twistRoot r k.val)) := by
  rcases Nat.eq_zero_or_pos r with hr | hr
  · subst hr
    exact ⟨fun k => k.elim0, fun k => k.elim0⟩
  exact twistPhase_phaseApprox (fun k => twistAngle_err p r k hr k.isLt.le)
    (by unfold taylorTerms; omega) (sixteen_taylorTerms_le p 0)

/-! ### The computed convolution on the box -/

/-- `M̃_ℂ` on a box `∏_{i ≤ D} ℤ/t_i`: the last axis `t_D = r` is the polynomial coordinate,
the twist tables are `twistPlus`, `twistMinus` for `r`, and `M̃_r = synthMr` with
`a_i = log₂ t_i` on the other axes. -/
noncomputable def boxConvSucc (p D : ℕ) (t : Fin (D + 1) → ℕ) [∀ i, NeZero (t i)] :
    (((i : Fin (D + 1)) → ZMod (t i)) → ℂ) → (((i : Fin (D + 1)) → ZMod (t i)) → ℂ) →
      (((i : Fin (D + 1)) → ZMod (t i)) → ℂ) :=
  cconvApproxVia (boxSplit t rfl) p (twistPlus p (t (Fin.last D)))
    (twistMinus p (t (Fin.last D)))
    (synthMr (fun i => Nat.log 2 (t i.castSucc)) (fun i => t i.castSucc) p)

/-- `boxConvSucc` for any number of axes (`0` on the empty box). -/
noncomputable def boxConv (p : ℕ) : (D : ℕ) → (t : Fin D → ℕ) → (∀ i, NeZero (t i)) →
    (((i : Fin D) → ZMod (t i)) → ℂ) → (((i : Fin D) → ZMod (t i)) → ℂ) →
      (((i : Fin D) → ZMod (t i)) → ℂ)
  | 0, _, _ => fun _ _ => 0
  | D + 1, t, _ => boxConvSucc p D t

theorem boxConvSucc_spec {p D : ℕ} (t : Fin (D + 1) → ℕ) [∀ i, NeZero (t i)] {ℓ0 L : ℕ}
    (hr2 : 2 ≤ t (Fin.last D)) (hpow : ∀ i, t i = 2 ^ Nat.log 2 (t i))
    (hdvd : ∀ i, t i ∣ 2 * t (Fin.last D)) (hlog : ∀ i, Nat.log 2 (t i) ≤ ℓ0) (hℓ0 : 1 ≤ ℓ0)
    (hℓL : ℓ0 ≤ L) (h9 : 9 ≤ ((∏ i, t i : ℕ) : ℝ) * L)
    (hE : 5000 * ((∏ i, t i : ℕ) : ℝ) * L ≤ 2 ^ p)
    (f g : ((i : Fin (D + 1)) → ZMod (t i)) → ℂ) (hf : ‖f‖ ≤ 1) (hg : ‖g‖ ≤ 7 / 10) :
    2 ^ p * ‖boxConvSucc p D t f g - convNormD t f g‖ ≤ 6 * ((∏ i, t i : ℕ) : ℝ) * L ∧
      ‖boxConvSucc p D t f g‖ ≤ 701 / 1000 := by
  set a : Fin D → ℕ := fun i => Nat.log 2 (t i.castSucc) with ha
  have hA : nRounds a ≤ ℓ0 := Finset.sup_le fun i _ => hlog _
  have hprod : ((t (Fin.last D) * ∏ i, (fun i : Fin D => t i.castSucc) i : ℕ) : ℝ) =
      ((∏ i, t i : ℕ) : ℝ) := by
    rw [Fin.prod_univ_castSucc, mul_comm]
  have hlt := eSynth_lt (r := t (Fin.last D)) a (fun i => t i.castSucc) hr2 hA hℓ0 hℓL
  rw [hprod] at hlt
  have hθ := twist_phaseApprox p (t (Fin.last D))
  have h := cconvApprox_box_synth t rfl a (fun i => hpow i.castSucc)
    (fun i => (hpow i.castSucc) ▸ hdvd i.castSucc) hθ.1 hθ.2 (by linarith) f g hf hg
  refine ⟨h.1.trans (by linarith), h.2⟩

theorem boxConv_spec {p : ℕ} :
    ∀ {D : ℕ} (t : Fin D → ℕ) [inst : ∀ i, NeZero (t i)] {ℓ0 L R : ℕ},
    0 < D → (∀ i : Fin D, (i : ℕ) + 1 = D → t i = R) → 2 ≤ R →
    (∀ i, t i = 2 ^ Nat.log 2 (t i)) → (∀ i, t i ∣ 2 * R) → (∀ i, Nat.log 2 (t i) ≤ ℓ0) →
    1 ≤ ℓ0 → ℓ0 ≤ L → 9 ≤ ((∏ i, t i : ℕ) : ℝ) * L →
    5000 * ((∏ i, t i : ℕ) : ℝ) * L ≤ 2 ^ p →
    ∀ f g : ((i : Fin D) → ZMod (t i)) → ℂ, ‖f‖ ≤ 1 → ‖g‖ ≤ 7 / 10 →
      2 ^ p * ‖boxConv p D t inst f g - convNormD t f g‖ ≤ 6 * ((∏ i, t i : ℕ) : ℝ) * L ∧
        ‖boxConv p D t inst f g‖ ≤ 701 / 1000
  | 0, _, _, _, _, _, hD, _, _, _, _, _, _, _, _, _, _, _, _, _ => absurd hD (lt_irrefl 0)
  | D + 1, t, _, ℓ0, L, R, _, hlast, hR, hpow, hdvd, hlog, hℓ0, hℓL, h9, hE, f, g, hf, hg => by
    have hl : t (Fin.last D) = R := hlast _ rfl
    subst hl
    exact boxConvSucc_spec t hR hpow hdvd hlog hℓ0 hℓL h9 hE f g hf hg

/-! ### Sizes -/

section SizeFacts

open Sizes Moduli

variable {n : ℕ}

/-- The source lengths are pairwise coprime for every `n`. -/
theorem s_pairwise (n : ℕ) : Pairwise (Nat.Coprime on (s n)) :=
  s_pairwise_coprime n

/-- The window of `Ã`: `m = ⌊√(p α²)⌋ + 1`, the least integer above `α √p`. -/
def windowA (p a : ℕ) : ℕ := Nat.sqrt (p * a ^ 2) + 1

theorem windowA_spec {p a : ℕ} (hap : a ^ 2 < p) :
    (p : ℝ) * (a : ℝ) ^ 2 ≤ (windowA p a : ℝ) ^ 2 ∧ 1 ≤ windowA p a ∧ windowA p a ≤ p := by
  have h1 := Nat.lt_succ_sqrt' (p * a ^ 2)
  rw [Nat.succ_eq_add_one] at h1
  refine ⟨?_, by unfold windowA; omega, ?_⟩
  · have : ((p * a ^ 2 : ℕ) : ℝ) ≤ ((windowA p a ^ 2 : ℕ) : ℝ) := by
      exact_mod_cast h1.le
    push_cast at this
    exact this
  · have hp : 0 < p := by omega
    have h2 : Nat.sqrt (p * a ^ 2) < p := by
      rw [Nat.sqrt_lt']
      rw [sq p]
      exact Nat.mul_lt_mul_of_pos_left hap hp
    unfold windowA
    omega

theorem alpha_sq_lt_p (h : Big n) : alpha n ^ 2 < p n := by
  have h1 := alpha_sq_lt n
  have h2 := h.alphaU_le_d
  have h3 := d_le_b n
  have hD := h.2
  unfold p; omega

theorem t_pow_log (n : ℕ) (i : Fin (d n)) : t n i = 2 ^ Nat.log 2 (t n i) := by
  unfold t
  split_ifs <;> rw [Nat.log_pow one_lt_two]

theorem log_t_le (n : ℕ) (i : Fin (d n)) : Nat.log 2 (t n i) ≤ ℓ n := by
  unfold t
  split_ifs
  · rw [Nat.log_pow one_lt_two]; omega
  · rw [Nat.log_pow one_lt_two]

theorem t_dvd_two_r (n : ℕ) (i : Fin (d n)) : t n i ∣ 2 * r n := by
  unfold t r
  split_ifs
  · exact Dvd.dvd.mul_left (Nat.pow_dvd_pow 2 (Nat.sub_le _ _)) 2
  · exact Dvd.intro_left 2 rfl

theorem t_of_last (h : Big n) (i : Fin (d n)) (hi : (i : ℕ) + 1 = d n) : t n i = r n := by
  have := numHalf_lt h.one_le_d
  unfold t r
  split_ifs with hh
  · omega
  · rfl

theorem ℓ_le_logT (h : Big n) : ℓ n ≤ logT n := by
  have hd := h.one_le_d
  have hL := h.one_le_logT
  unfold ℓ
  apply Nat.div_le_of_le_mul
  obtain ⟨L', hL'⟩ : ∃ L', logT n = L' + 1 := ⟨logT n - 1, by omega⟩
  obtain ⟨D', hD'⟩ : ∃ D', d n = D' + 1 := ⟨d n - 1, by omega⟩
  rw [hL', hD']
  have e : L' + 1 + (D' + 1) - 1 = L' + D' + 1 := by omega
  rw [e]
  nlinarith

theorem two_le_r (h : Big n) : 2 ≤ r n := by
  have := h.two_le_ℓ
  unfold r
  calc 2 = 2 ^ 1 := by norm_num
    _ ≤ 2 ^ ℓ n := Nat.pow_le_pow_right (by norm_num) (by omega)

theorem four_le_gamma (h : Big n) : 4 ≤ gamma n := by
  have := h.2
  unfold gamma
  nlinarith

end SizeFacts

/-! ### The pipeline -/

section Defs

open Sizes
open IntegerMultBounds.Resampling.WindowSum (termW)
open IntegerMultBounds.Resampling.WeightTable (tableA tableE tableD)

/-- `Ã` on axis `i`: the Gaussian window sum with radius `windowA p α` and the integer table
`tableA` at scale `2^p`. -/
noncomputable def lineA (n : ℕ) (i : Fin (d n)) : (ZMod (s n i) → ℂ) → ZMod (t n i) → ℂ :=
  resampANum (s n i) (t n i) (windowA (p n) (alpha n))
    (termW (p n) fun k j => (tableA (s n i) (t n i) (alpha n) (p n) k j : ℝ) / 2 ^ p n)

/-- `B̃₀` on axis `i`: the banded solve of the Gaussian window matrix (`BandSpec.bandA`), which
computes `2^-α² ℬ₀`. -/
noncomputable abbrev lineB (n : ℕ) (i : Fin (d n)) : (ZMod (t n i) → ℂ) → ZMod (s n i) → ℂ :=
  BandSpec.bandA n i

/-- The chirp kernel `ā'` with the product guard `⌈log₂ d⌉ + 4`. -/
noncomputable def chirpKernel (n : ℕ) : ((i : Fin (d n)) → ZMod (t n i)) → ℂ :=
  chirpProd (p n) (chirpGuard (d n)) (t n) (s n)

/-- The computed complex convolution `M̃_ℂ` on the box `∏ ℤ/t_i`. -/
noncomputable def convBox (n : ℕ) :
    (((i : Fin (d n)) → ZMod (t n i)) → ℂ) → (((i : Fin (d n)) → ZMod (t n i)) → ℂ) →
      (((i : Fin (d n)) → ZMod (t n i)) → ℂ) :=
  boxConv (p n) (d n) (t n) inferInstance

/-- The computed source transform `F' = F̃ ∘ Φ`. -/
noncomputable def srcMap (n : ℕ) :
    (ZMod (∏ i, s n i) → ℂ) → (((i : Fin (d n)) → ZMod (s n i)) → ℂ) :=
  SourceErr.crtSourceApprox (s_pairwise n) (p n) (gamma n) (lineA n) (lineB n) (chirpKernel n)
    (convBox n)

/-- The computed opposite transform `G' = Φ⁻¹ ∘ F̃⁺`. -/
noncomputable def oppMap (n : ℕ) :
    (((i : Fin (d n)) → ZMod (s n i)) → ℂ) → (ZMod (∏ i, s n i) → ℂ) :=
  SourceErr.crtOppApprox (s_pairwise n) (p n) (gamma n) (lineA n) (lineB n) (chirpKernel n)
    (convBox n)

/-- The coefficients of `x y` in radix `2^b`: the radix-`2^b` digits of the low `n` bits of
`x` and `y`, scaled by `2^{-(b+2)}`; `srcMap n` on both; their pointwise product truncated by
`Q_p`; `oppMap n`; the scale `2^{2b} S · 16 S`; rounding to the nearest integer. The module
docstring lists every stage and table in machine order. -/
noncomputable def pipelineCoeffs (n x y : ℕ) : List ℕ :=
  List.ofFn fun i : Fin (∏ i, s n i) =>
    (round (((2 : ℂ) ^ (2 * b n) * ((∏ i, s n i : ℕ) : ℂ)) *
      ExactRecovery.computedConv (p := p n) (k := b n) (srcMap n) (oppMap n) (bitsMSB n x)
        (bitsMSB n y) (i.val : ZMod (∏ i, s n i))).re).toNat

/-- The box convolution of a pipeline: `M̃_ℂ` on `∏ ℤ/t_i`. -/
abbrev BoxConvOf (n : ℕ) : Type :=
  (((i : Fin (d n)) → ZMod (t n i)) → ℂ) → (((i : Fin (d n)) → ZMod (t n i)) → ℂ) →
    (((i : Fin (d n)) → ZMod (t n i)) → ℂ)

/-- The computed source transform for any box convolution `cb`. -/
noncomputable def srcMapG (n : ℕ) (cb : BoxConvOf n) :
    (ZMod (∏ i, s n i) → ℂ) → (((i : Fin (d n)) → ZMod (s n i)) → ℂ) :=
  SourceErr.crtSourceApprox (s_pairwise n) (p n) (gamma n) (lineA n) (lineB n) (chirpKernel n) cb

/-- The computed opposite transform for any box convolution `cb`. -/
noncomputable def oppMapG (n : ℕ) (cb : BoxConvOf n) :
    (((i : Fin (d n)) → ZMod (s n i)) → ℂ) → (ZMod (∏ i, s n i) → ℂ) :=
  SourceErr.crtOppApprox (s_pairwise n) (p n) (gamma n) (lineA n) (lineB n) (chirpKernel n) cb

/-- The coefficients of the pipeline for any box convolution `cb`. -/
noncomputable def pipelineCoeffsG (n : ℕ) (cb : BoxConvOf n) (x y : ℕ) : List ℕ :=
  List.ofFn fun i : Fin (∏ i, s n i) =>
    (round (((2 : ℂ) ^ (2 * b n) * ((∏ i, s n i : ℕ) : ℂ)) *
      ExactRecovery.computedConv (p := p n) (k := b n) (srcMapG n cb) (oppMapG n cb) (bitsMSB n x)
        (bitsMSB n y) (i.val : ZMod (∏ i, s n i))).re).toNat

/-- The guarantee of a box convolution used by the source transforms: within `6 T log₂ T` of
the normalized convolution at scale `2^p`, and in the `0.701`-ball. -/
def BoxConvSpec (n : ℕ) (cb : BoxConvOf n) : Prop :=
  ∀ f g : ((i : Fin (d n)) → ZMod (t n i)) → ℂ, ‖f‖ ≤ 1 → ‖g‖ ≤ 7 / 10 →
    2 ^ p n * ‖cb f g - convNormD (t n) f g‖ ≤ 6 * ((∏ i, t n i : ℕ) : ℝ) * logT n ∧
      ‖cb f g‖ ≤ 701 / 1000

end Defs

/-! ### Correctness -/

section Correct

open Sizes
open IntegerMultBounds.Resampling.WeightTable (tables_ok)
open ContinuousLinearMap

variable {n : ℕ}

/-- `hM'` of the source-transform assembly for `convBox`, with `L = log₂ T`. -/
theorem convBox_spec (h : Big n) (hsmall : 2 * d n * p n ^ 2 ≤ T n * logT n)
    (hEs : 9 * (2 : ℝ) ^ gamma n * T n * logT n ≤ 2 ^ p n / 100)
    (f g : ((i : Fin (d n)) → ZMod (t n i)) → ℂ) (hf : ‖f‖ ≤ 1) (hg : ‖g‖ ≤ 7 / 10) :
    2 ^ p n * ‖convBox n f g - convNormD (t n) f g‖ ≤
        6 * ((∏ i, t n i : ℕ) : ℝ) * logT n ∧ ‖convBox n f g‖ ≤ 701 / 1000 := by
  have hd1 := h.one_le_d
  have hpT : ∏ i, t n i = T n := prod_t hd1
  have h9 : 9 ≤ ((∏ i, t n i : ℕ) : ℝ) * logT n := by
    have hp := h.thirteen_le_p
    have hD := h.2
    have : 9 ≤ (∏ i, t n i) * logT n := by
      rw [hpT]
      have : 9 ≤ 2 * d n * p n ^ 2 := by nlinarith
      omega
    exact_mod_cast this
  have hE : 5000 * ((∏ i, t n i : ℕ) : ℝ) * logT n ≤ 2 ^ p n := by
    have hg4 : (16 : ℝ) ≤ 2 ^ gamma n :=
      calc (16 : ℝ) = 2 ^ 4 := by norm_num
        _ ≤ 2 ^ gamma n := pow_le_pow_right₀ (by norm_num) (four_le_gamma h)
    have hX : (0 : ℝ) ≤ (T n : ℝ) * logT n := by positivity
    rw [hpT]
    nlinarith
  exact boxConv_spec (t n) (by omega) (t_of_last h) (two_le_r h) (t_pow_log n) (t_dvd_two_r n)
    (log_t_le n) (by have := h.two_le_ℓ; omega) (ℓ_le_logT h) h9 hE f g hf hg

/-- `source_approx` for any box convolution with the guarantee `BoxConvSpec`: the computed source
transform and its opposite approximate `R F_s` and `R F_s⁺` on the
`1/2`-ball within `E_s = 9 · 2^γ T log₂ T`. -/
theorem source_approxG (h : Big n) (hsmall : 2 * d n * p n ^ 2 ≤ T n * logT n)
    (hEs : 9 * (2 : ℝ) ^ gamma n * T n * logT n ≤ 2 ^ p n / 100) (cb : BoxConvOf n)
    (hcb : BoxConvSpec n cb) :
    SourceErr.ApproxOn (p n) (SourceErr.sourceApprox (s n) (t n) (p n) (gamma n) (lineA n)
        (lineB n) (chirpKernel n) cb) (permRCLM (s n) (t n) ∘L dftDCLM (s n)) (1 / 2)
        (9 * (2 : ℝ) ^ gamma n * T n * logT n) ∧
      SourceErr.ApproxOn (p n) (SourceErr.oppApprox (s n) (t n) (p n) (gamma n) (lineA n)
        (lineB n) (chirpKernel n) cb) (permRCLM (s n) (t n) ∘L dftDPlusCLM (s n))
        (1 / 2) (9 * (2 : ℝ) ^ gamma n * T n * logT n) := by
  have hg := h.good
  have hd1 := h.one_le_d
  have hpT : ∏ i, t n i = T n := prod_t hd1
  have hα2 : 2 ≤ alpha n := two_le_alpha h.1
  have hαR : (2 : ℝ) ≤ alpha n := by exact_mod_cast hα2
  have hαp : alpha n ^ 2 ≤ p n := h.alpha_sq_le_p
  have hαpR : ((alpha n : ℝ)) ^ 2 ≤ p n := by exact_mod_cast hαp
  have hp13 := h.thirteen_le_p
  obtain ⟨hm, hm1, hmp⟩ := windowA_spec (alpha_sq_lt_p h)
  have hj : 2 * (p n : ℝ) ≤ 2 ^ (alpha n * alpha n) := by
    have := h.band_width
    rw [← sq]
    exact_mod_cast (show 2 * p n ≤ 2 ^ (alpha n ^ 2) by omega)
  have hi0 : 0 < d n := by omega
  choose J hJ hfac hAn hBn hA' hA'1 using fun i =>
    BandSpec.band_factorization_sg (hg.lt i) (hg.coprime i) hαR (u := alpha n ^ 2)
      (by push_cast; ring) (alpha n * alpha n) h.band_width (h.quarter_p_le_theta i) hj hαpR hm
      hm1 hmp hp13
      (IntegerMultBounds.Resampling.WeightTable.tableA (s n i) (t n i) (alpha n) (p n))
      (tables_ok (s n i) (t n i) (alpha n) (p n) (hg.lt i) hp13 hα2 hαp).1
  have hexact : ∀ i, PhaseCellOperator.exact (s n i) (t n i) (alpha n : ℝ) =
      1 + offDiagCLM (s n i) (t n i) (alpha n : ℝ) := fun i => normN_clm _ _ _
  have hB' := fun i => (BandSpec.band_axis_full h h.band_width h.band_budget i).2 (J i)
    (by rw [hexact]; exact hJ i)
  have hB'1 := fun i => (BandSpec.band_axis_math h h.band_width h.band_budget i).ball
  have hsm : 2 * d n * p n ^ 2 ≤ (∏ i, t n i) * logT n := by rw [hpT]; exact hsmall
  have hEs' : 9 * (2 : ℝ) ^ (d n * (2 * ⌈((alpha n : ℝ)) ^ 2⌉₊ + 2 + alpha n * alpha n)) *
      ((∏ i, t n i : ℕ) : ℝ) * logT n ≤ 2 ^ p n / 100 := by
    rw [← gamma_eq_ceil, hpT]; exact hEs
  have hres := SourceErr.sourceErr_of_componentsC (s := s n) (t := t n) h.two_dvd_t
    (fun i => resampA (s n i) (t n i) (alpha n : ℝ))
    (fun i => ((2 : ℂ) ^ (alpha n * alpha n))⁻¹ • resampB₀ (s n i) (t n i) (alpha n : ℝ) (J i))
    hfac hAn hBn hA' hA'1 hB' hB'1 (chirpProd_ha'_explicit (t n) (s n) (p n))
    hcb hi0 (by omega) hsm hEs'
  rw [← gamma_eq_ceil, hpT] at hres
  exact hres

/-- The computed source transform and its opposite approximate `R F_s` and `R F_s⁺` on the
`1/2`-ball within `E_s = 9 · 2^γ T log₂ T`. -/
theorem source_approx (h : Big n) (hsmall : 2 * d n * p n ^ 2 ≤ T n * logT n)
    (hEs : 9 * (2 : ℝ) ^ gamma n * T n * logT n ≤ 2 ^ p n / 100) :
    SourceErr.ApproxOn (p n) (SourceErr.sourceApprox (s n) (t n) (p n) (gamma n) (lineA n)
        (lineB n) (chirpKernel n) (convBox n)) (permRCLM (s n) (t n) ∘L dftDCLM (s n)) (1 / 2)
        (9 * (2 : ℝ) ^ gamma n * T n * logT n) ∧
      SourceErr.ApproxOn (p n) (SourceErr.oppApprox (s n) (t n) (p n) (gamma n) (lineA n)
        (lineB n) (chirpKernel n) (convBox n)) (permRCLM (s n) (t n) ∘L dftDPlusCLM (s n))
        (1 / 2) (9 * (2 : ℝ) ^ gamma n * T n * logT n) :=
  source_approxG h hsmall hEs (convBox n) (convBox_spec h hsmall hEs)

/-- **Correctness of the numeric pipeline for any box convolution** with the guarantee
`BoxConvSpec`. -/
theorem pipeline_correctG :
    ∀ᶠ n in Filter.atTop, ∀ cb : BoxConvOf n, BoxConvSpec n cb → ∀ x y : ℕ, Nat.size x ≤ n →
      Nat.size y ≤ n → evalBase (2 ^ b n) (pipelineCoeffsG n cb x y) = x * y := by
  filter_upwards [eventually_big, eventually_small, eventually_margins] with n h hsmall hmarg
  intro cb hcb x y hx hy
  obtain ⟨hEs, hfinal⟩ := hmarg
  obtain ⟨hF, hG⟩ := source_approxG h hsmall hEs cb hcb
  have hg := h.good
  have hk : 0 < b n := one_le_b h.1
  have hS := h.digits_length_le (length_bitsMSB n x) (length_bitsMSB n y)
  have key := exact_product_crt (s n) (t n) (s_pairwise n) hg.coprime (srcMapG n cb) (oppMapG n cb)
    hk hS (SourceErr.crtSource_err (s_pairwise n) hF) (SourceErr.crtOpp_err (s_pairwise n) hG) hEs
    hfinal
  rw [binaryValue_bitsMSB_of_size hx, binaryValue_bitsMSB_of_size hy] at key
  exact key

/-- **Correctness of the numeric pipeline.** For all large `n` and all `x y < 2^n`, the
coefficients computed by the pipeline evaluate in radix `2^b` to `x y`. -/
theorem pipeline_correct :
    ∀ᶠ n in Filter.atTop, ∀ x y : ℕ, Nat.size x ≤ n → Nat.size y ≤ n →
      evalBase (2 ^ b n) (pipelineCoeffs n x y) = x * y := by
  filter_upwards [pipeline_correctG, eventually_big, eventually_small, eventually_margins]
    with n hG h hsmall hmarg
  exact hG (convBox n) (convBox_spec h hsmall hmarg.1)

end Correct

end IntegerMultBounds.MathlibTM2.Mult.Pipeline
