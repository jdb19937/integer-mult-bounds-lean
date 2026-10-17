module

public import IntegerMultBounds.MathlibTM2.Mult.SynthErrRounds
public import IntegerMultBounds.MathlibTM2.Mult.ComplexConv
import IntegerMultBounds.NLogN.SynthConvApproxD
public import IntegerMultBounds.Spec.SyntheticConvolution
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Data.List.GetD

/-!
# Computed synthetic convolution

Paper §6, numerical part of the proof of `prop:synthetic-convolution`, and the computed ring
convolution `M̃_r` of `IntegerMultBounds.MathlibTM2.Mult.ComplexConv` (§8) with its guarantee `RingApprox`.

## The computed convolution on record arrays

Axis lengths `tᵢ = 2^(aᵢ)` divide `2r`; `M = ∏ tᵢ` (`tsA a`) and `A = maxᵢ aᵢ` is the number of
rounds (`nRounds a`).

* `pwE u v = u v / r` and `pwC p u v = Q_p(u v / r)`, recordwise; `pwC_eq_gridPoly`: each record
  of `pwC` is the record `Q_p(f g / r)` of `lem:signed-ring-product`.
* `convC a p u v = M · oppRoundsC A (pwC (fwdRoundsC A u) (fwdRoundsC A v))`: both computed
  forward transforms retained in their common bit-reversed order `B`, the computed pointwise
  products, the computed opposite transform, and the exact scaling by `M`. `convE` is the exact
  counterpart.
* `convC_err_lt`: on disk operands `2^p |convC − convE| < √2 M (3A + 1)` on the first `M`
  records. Each forward error is at most `δ = √2 A 2^{-p}`; the bilinear pointwise product with
  disk factors and one truncation adds up to `2δ + √2 2^{-p}`; the opposite rounds are
  contractions with `A` truncations, giving `3δ + √2 2^{-p}`; the scaling multiplies by `M`.
* `convE_eq_pipeE`: `convE = M F⁺((F⁻u)(F⁻v)/r)` on the first `M` records (`fwd_rounds`,
  `opp_rounds`, and `B² = 1`: the pointwise products commute with the record permutation `B`).

## Box arrays

`Box N = ∏ᵢ ℤ/Nᵢ` is the index group of `ComplexConv`; `enc`, `dec` are its mixed-radix record
addresses (first axis most significant), `ιR U` reads a box array as a record array, and
`sum_box` turns sums over the box into sums over the first `M` addresses.

* `fwdT_synthConvNormG` (convolution theorem): `F⁻(ℳ_r(U, V)) = (F⁻U)(F⁻V)/r` recordwise, from
  `sum_shiftInv_synthConvG` and the additivity of the exponent modulo `2r`
  (`synthExpL_enc_add`).
* `pipeE_ιR`: `M F⁺((F⁻U)(F⁻V)/r) = ℳ_r(U, V)`, with `oppT_fwdT` (`F⁺F⁻ = I/M`).
* `synthMr a N p U V z = convC a p (ιR U) (ιR V) (enc z)` and `synthMr_ringApprox`:
  `RingApprox p (synthMr a N p) (eSynth a N)` with `eSynth a N = √2 M (3A + 1)`.
  `synthMr_ringApprox_ell`: the paper's `√2 M (3ℓ + 1)` for every `ℓ ≥ A`. `eSynth_lt`:
  `eSynth a N < 5TL` for `T = rM`, `r ≥ 2`, `A ≤ ℓ ≤ L` and `ℓ ≥ 1`.
* `cconvApprox_box_synth`: `ComplexConv.cconvApprox_box` instantiated with `M̃_r = synthMr`:
  scaled error at most `eSynth + 9` and norm at most `701/1000`.

## The vendored form

* `subAddr_enc`: cyclic address subtraction is subtraction in the box; `convM_ιR`.
* `convE_eq_convM`: `convE = convM` on the first `M` records.
* `convC_close`: `Close M (convC a p u v) (convM ts u v) (√2 M (3ℓ + 1) 2^{-p})` for disk
  operands and `ℓ ≥ A`, the error clause of `Spec.SignedRingProduct.MeetsConvolution`.
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2.Mult.SynthErr

open IntegerMultBounds IntegerMultBounds.NLogN IntegerMultBounds.Spec.SignedRingProduct
open IntegerMultBounds.MathlibTM2.Mult.Rounds

/-! ### Pointwise products -/

section Pointwise

variable {r : ℕ} [NeZero r]

/-- The exact pointwise product `P(u, v) = u v / r` of corresponding records. -/
noncomputable def pwE (u v : Recs r) : Recs r :=
  fun n => (1 / (r : ℂ)) • negacyclicMul (u n) (v n)

/-- The computed pointwise product `Q_p(u v / r)` of corresponding records. -/
noncomputable def pwC (p : ℕ) (u v : Recs r) : Recs r := rdR p (pwE u v)

omit [NeZero r] in
theorem pwC_apply (p : ℕ) (u v : Recs r) (n : ℕ) (c : Fin r) :
    pwC p u v n c = rhoC p (negacyclicMul (u n) (v n) c / r) := by
  simp only [pwC, rdR, pwE, Pi.smul_apply, smul_eq_mul]
  congr 1
  ring

omit [NeZero r] in
/-- Each record of `pwC` is the record `Q_p(f g / r)` of `lem:signed-ring-product`. -/
theorem pwC_eq_gridPoly (p : ℕ) (u v : Recs r) (n : ℕ) :
    pwC p u v n = gridPoly p (productRe p (u n) (v n)) (productIm p (u n) (v n)) := by
  rw [gridPoly_product]
  funext c
  exact pwC_apply p u v n c

theorem norm_rec_le {N : ℕ} {u : Recs r} {a : ℝ} (h : SupLe N u a) {n : ℕ} (hn : n < 2 ^ N) :
    ‖u n‖ ≤ a :=
  (pi_norm_le_iff_of_nonneg ((norm_nonneg _).trans (h n hn 0))).2 (h n hn)

/-- The computed pointwise product of disk arrays is a disk array. -/
theorem pwC_supLe {N : ℕ} (p : ℕ) {u v : Recs r} (hu : SupLe N u 1) (hv : SupLe N v 1) :
    SupLe N (pwC p u v) 1 := by
  intro n hn c
  refine (norm_rhoC_le p _).trans ((norm_le_pi_norm (pwE u v n) c).trans ?_)
  refine (norm_normProd_le _ _).trans ?_
  calc ‖u n‖ * ‖v n‖ ≤ 1 * 1 := by
        gcongr
        · exact norm_rec_le hu hn
        · exact norm_rec_le hv hn
    _ = 1 := one_mul 1

/-- The pointwise step of the convolution error: inputs within `δ` of disk arrays give an output
within less than `2δ + √2·2^{-p}` of the exact product. -/
theorem pwC_err_lt {N : ℕ} (p : ℕ) {u u' v v' : Recs r} {δ : ℝ} (hu : SupLe N u 1)
    (hv' : SupLe N v' 1) (huu : SupLe N (u' - u) δ) (hvv : SupLe N (v' - v) δ) :
    ∀ n < 2 ^ N, ∀ c, ‖(pwC p u' v' - pwE u v) n c‖ < 2 * δ + Real.sqrt 2 / 2 ^ p := by
  intro n hn c
  have h1 := norm_rhoC_sub_lt p (pwE u' v' n c)
  have h2 : ‖pwE u' v' n - pwE u v n‖ ≤ 2 * δ :=
    normProd_err_ball (norm_rec_le hu hn) (norm_rec_le hv' hn) (norm_rec_le huu hn)
      (norm_rec_le hvv hn)
  have h3 := (norm_le_pi_norm (pwE u' v' n - pwE u v n) c).trans h2
  calc ‖(pwC p u' v' - pwE u v) n c‖
      = ‖(rhoC p (pwE u' v' n c) - pwE u' v' n c) + (pwE u' v' n - pwE u v n) c‖ := by
        simp only [pwC, rdR, Pi.sub_apply]; congr 1; abel
    _ ≤ ‖rhoC p (pwE u' v' n c) - pwE u' v' n c‖ + ‖(pwE u' v' n - pwE u v n) c‖ :=
        norm_add_le _ _
    _ < Real.sqrt 2 / 2 ^ p + 2 * δ := add_lt_add_of_lt_of_le h1 h3
    _ = 2 * δ + Real.sqrt 2 / 2 ^ p := add_comm _ _

/-- The pointwise step of the convolution error: inputs within `δ` of disk arrays give an output
within `2δ + √2·2^{-p}` of the exact product. -/
theorem pwC_err {N : ℕ} (p : ℕ) {u u' v v' : Recs r} {δ : ℝ} (hu : SupLe N u 1)
    (hv' : SupLe N v' 1) (huu : SupLe N (u' - u) δ) (hvv : SupLe N (v' - v) δ) :
    SupLe N (pwC p u' v' - pwE u v) (2 * δ + Real.sqrt 2 / 2 ^ p) :=
  fun n hn c => (pwC_err_lt p hu hv' huu hvv n hn c).le

end Pointwise

/-! ### The computed synthetic convolution on record arrays -/

section Conv

variable {r : ℕ} [NeZero r] {d : ℕ} (a : Fin d → ℕ)

/-- The computed synthetic convolution `M · Q_p∘F⁺-rounds(Q_p(ũ ṽ / r))`, `ũ, ṽ` the computed
forward transforms retained in the bit-reversed order `B`, and `M = ∏ tᵢ`. -/
noncomputable def convC (p : ℕ) (u v : Recs r) : Recs r :=
  fun n => ((tsA a).prod : ℂ) • oppRoundsC p (List.ofFn a) (nRounds a)
    (pwC p (fwdRoundsC p (List.ofFn a) (nRounds a) u)
      (fwdRoundsC p (List.ofFn a) (nRounds a) v)) n

/-- The exact counterpart of `convC`. -/
noncomputable def convE (u v : Recs r) : Recs r :=
  fun n => ((tsA a).prod : ℂ) • oppRounds (List.ofFn a) (nRounds a)
    (pwE (fwdRounds (List.ofFn a) (nRounds a) u) (fwdRounds (List.ofFn a) (nRounds a) v)) n

/-- The error of the computed convolution on disk operands: less than `√2 M (3A + 1) 2^{-p}` per
coefficient. -/
theorem convC_err_lt (p : ℕ) {u v : Recs r} (hu : SupLe (List.ofFn a).sum u 1)
    (hv : SupLe (List.ofFn a).sum v 1) :
    ∀ n < (tsA a).prod, ∀ c, 2 ^ p * ‖convC a p u v n c - convE a u v n c‖ <
      Real.sqrt 2 * (tsA a).prod * (3 * nRounds a + 1) := by
  set es := List.ofFn a
  set A := nRounds a
  set η := Real.sqrt 2 / 2 ^ p with hη
  have hfu := fwdRoundsC_err p es A (supLe_sub_self es.sum u)
  have hfv := fwdRoundsC_err p es A (supLe_sub_self es.sum v)
  have hd := fwdRounds_supLe es A hu
  have hd' := fwdRoundsC_supLe p es A hv
  have hpw := pwC_err p hd hd' hfu hfv
  have hpw' := pwC_err_lt p hd hd' hfu hfv
  have key : ∀ k : ℕ, ∀ n < 2 ^ es.sum, ∀ c,
      ‖(oppRoundsC p es k (pwC p (fwdRoundsC p es A u) (fwdRoundsC p es A v)) -
        oppRounds es k (pwE (fwdRounds es A u) (fwdRounds es A v))) n c‖ <
        2 * (0 + A * η) + η + k * η := by
    intro k n hn c
    rcases k with _ | k
    · have := hpw' n hn c
      simp only [oppRoundsC, oppRounds, Nat.cast_zero, zero_mul, add_zero]
      simpa only [zero_add] using this
    · have := oppRoundsC_err_lt p es k hpw n hn c
      push_cast
      exact this
  intro n hn c
  rw [tsA_prod] at hn
  have h := key A n hn c
  have hp : (0 : ℝ) < 2 ^ p := by positivity
  have hM : (0 : ℝ) < (tsA a).prod := by
    rw [tsA_prod]; push_cast; positivity
  have e : convC a p u v n c - convE a u v n c = ((tsA a).prod : ℂ) *
      (oppRoundsC p es A (pwC p (fwdRoundsC p es A u) (fwdRoundsC p es A v)) -
        oppRounds es A (pwE (fwdRounds es A u) (fwdRounds es A v))) n c := by
    simp only [convC, convE, Pi.smul_apply, smul_eq_mul, Pi.sub_apply, mul_sub]
    rfl
  rw [e, norm_mul, Complex.norm_natCast]
  calc 2 ^ p * ((tsA a).prod * ‖_‖)
      < 2 ^ p * ((tsA a).prod * (2 * (0 + A * η) + η + A * η)) := by gcongr
    _ = Real.sqrt 2 * (tsA a).prod * (3 * A + 1) := by
        rw [hη]; field_simp; ring

/-- The error of the computed convolution on disk operands: `√2 M (3A + 1) 2^{-p}` per
coefficient. -/
theorem convC_err (p : ℕ) {u v : Recs r} (hu : SupLe (List.ofFn a).sum u 1)
    (hv : SupLe (List.ofFn a).sum v 1) :
    ∀ n < (tsA a).prod, ∀ c, 2 ^ p * ‖convC a p u v n c - convE a u v n c‖ ≤
      Real.sqrt 2 * (tsA a).prod * (3 * nRounds a + 1) :=
  fun n hn c => (convC_err_lt a p hu hv n hn c).le

/-- The exact normalized pipeline `M F⁺((F⁻u)(F⁻v)/r)` of `prop:synthetic-convolution`. -/
noncomputable def pipeE (ts : List ℕ) (u v : Recs r) : Recs r :=
  fun n => (ts.prod : ℂ) •
    oppT ts (fun j => (1 / (r : ℂ)) • negacyclicMul (fwdT ts u j) (fwdT ts v j)) n

/-- The exact part of the computed convolution is the pipeline in the natural order: the
pointwise products commute with the record permutation `B`. -/
theorem convE_eq_pipeE (hr : ∀ i, 2 ^ a i ∣ 2 * r) (u v : Recs r) {n : ℕ}
    (hn : n < (tsA a).prod) : convE a u v n = pipeE (tsA a) u v n := by
  simp only [convE, pipeE]
  rw [opp_rounds a hr _ hn]
  refine congrArg _ ?_
  unfold oppT
  refine congrArg _ ?_
  apply Finset.sum_congr rfl
  intro j hj
  have hP := powAxes_tsA a hr
  have hb := bitrevAddr_lt hP j
  simp only [pwE]
  rw [fwd_rounds a hr u hb, fwd_rounds a hr v hb,
    bitrevAddr_bitrevAddr hP (Finset.mem_range.mp hj)]

end Conv

/-! ### The box `∏ᵢ ℤ/Nᵢ` and record addresses -/

section Box

variable {d : ℕ} (N : Fin d → ℕ) [∀ i, NeZero (N i)]

/-- The box `∏ᵢ ℤ/Nᵢ`, the index group `G` of `ComplexConv`. -/
abbrev Box := (i : Fin d) → ZMod (N i)

/-- The digits of a box element, indexed by the axis number. -/
def boxDigits (x : Box N) (i : ℕ) : ℕ := if h : i < d then (x ⟨i, h⟩).val else 0

/-- The mixed-radix record address of a box element, first axis most significant. -/
def enc (x : Box N) : ℕ := undigits (List.ofFn N) (boxDigits N x)

/-- The box element at a record address. -/
def dec (n : ℕ) : Box N := fun i => (digit (List.ofFn N) i n : ZMod (N i))

/-- A box array as a record array. -/
def ιR {r : ℕ} (U : Box N → Fin r → ℂ) : Recs r := fun n => U (dec N n)

omit [∀ i, NeZero (N i)] in
theorem getD_ofFn (i : Fin d) : (List.ofFn N).getD i 1 = N i := by
  rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]

omit [∀ i, NeZero (N i)] in
theorem boxDigits_of_lt (x : Box N) {i : ℕ} (hi : i < d) : boxDigits N x i = (x ⟨i, hi⟩).val := by
  simp [boxDigits, hi]

theorem ofFn_pos : ∀ t ∈ List.ofFn N, 0 < t := by
  intro t ht
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ht
  exact NeZero.pos _

theorem boxDigits_lt (x : Box N) :
    ∀ i < (List.ofFn N).length, boxDigits N x i < (List.ofFn N).getD i 1 := by
  intro i hi
  rw [List.length_ofFn] at hi
  have h1 : (List.ofFn N).getD i 1 = N ⟨i, hi⟩ := getD_ofFn N ⟨i, hi⟩
  rw [h1, boxDigits_of_lt N x hi]
  exact ZMod.val_lt _

theorem digit_enc (x : Box N) (i : Fin d) : digit (List.ofFn N) i (enc N x) = (x i).val := by
  rw [enc, digit_undigits _ _ (boxDigits_lt N x) i (by simp), boxDigits_of_lt N x i.isLt]

theorem enc_lt (x : Box N) : enc N x < (List.ofFn N).prod :=
  undigits_lt _ _ (boxDigits_lt N x)

theorem dec_enc (x : Box N) : dec N (enc N x) = x := by
  funext i
  simp only [dec, digit_enc, ZMod.natCast_zmod_val]

theorem enc_dec {n : ℕ} (hn : n < (List.ofFn N).prod) : enc N (dec N n) = n := by
  rw [enc]
  conv_rhs => rw [← undigits_digit _ n hn]
  apply undigits_congr
  intro i hi
  rw [List.length_ofFn] at hi
  rw [boxDigits_of_lt _ _ hi, dec, ZMod.val_natCast]
  apply Nat.mod_eq_of_lt
  have h1 : (List.ofFn N).getD i 1 = N ⟨i, hi⟩ := getD_ofFn N ⟨i, hi⟩
  have := digit_lt (ofFn_pos N) i n
  rwa [h1] at this

theorem card_box : Fintype.card (Box N) = (List.ofFn N).prod := by
  rw [Fintype.card_pi, List.prod_ofFn]
  simp [ZMod.card]

/-- Sums over the box are sums over the first `M` record addresses. -/
theorem sum_box {M : Type*} [AddCommMonoid M] (F : ℕ → M) :
    ∑ x : Box N, F (enc N x) = ∑ k ∈ Finset.range (List.ofFn N).prod, F k := by
  apply Finset.sum_nbij' (enc N) (dec N)
  · intro x _; exact Finset.mem_range.2 (enc_lt N x)
  · intro k _; exact Finset.mem_univ _
  · intro x _; exact dec_enc N x
  · intro k hk; exact enc_dec N (Finset.mem_range.1 hk)
  · intro x _; rfl

theorem synthExpL_enc (r j : ℕ) (x : Box N) :
    synthExpL r (List.ofFn N) j (enc N x) =
      ∑ i : Fin d, 2 * r / N i * digit (List.ofFn N) i j * (x i).val := by
  unfold synthExpL
  rw [list_sum_range, List.length_ofFn, Finset.sum_range]
  apply Finset.sum_congr rfl
  intro i _
  rw [getD_ofFn, digit_enc]

omit [∀ i, NeZero (N i)] in
theorem mul_mod_mod_eq {c t D s m : ℕ} (h : c * t = m) : c * D * (s % t) % m = c * D * s % m := by
  conv_rhs => rw [← Nat.mod_add_div s t]
  rw [show c * D * (s % t + t * (s / t)) = c * D * (s % t) + m * (D * (s / t)) by rw [← h]; ring,
    Nat.add_mul_mod_self_left]

/-- The exponent of `F⁻` is additive modulo `2r` in the box argument. -/
theorem synthExpL_enc_add {r : ℕ} (hN : ∀ i, N i ∣ 2 * r) (j : ℕ) (x y : Box N) :
    synthExpL r (List.ofFn N) j (enc N (x + y)) % (2 * r) =
      (synthExpL r (List.ofFn N) j (enc N x) + synthExpL r (List.ofFn N) j (enc N y)) %
        (2 * r) := by
  rw [synthExpL_enc, synthExpL_enc, synthExpL_enc, ← Finset.sum_add_distrib]
  conv_lhs => rw [Finset.sum_nat_mod]
  conv_rhs => rw [Finset.sum_nat_mod]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [Pi.add_apply, ZMod.val_add, mul_mod_mod_eq (Nat.div_mul_cancel (hN i)), mul_add]

end Box

/-! ### The convolution theorem and the exact pipeline -/

section Exact

variable {r : ℕ} [NeZero r]

theorem shiftInv_congr_mod {e₁ e₂ : ℕ} (h : e₁ % (2 * r) = e₂ % (2 * r)) (a : Fin r → ℂ) :
    shiftInv e₁ a = shiftInv e₂ a := by
  unfold shiftInv; rw [h]

theorem shiftInv_negacyclicMul (e₁ e₂ : ℕ) (a b : Fin r → ℂ) :
    shiftInv e₁ (shiftInv e₂ (negacyclicMul a b)) =
      negacyclicMul (shiftInv e₁ a) (shiftInv e₂ b) := by
  unfold shiftInv
  rw [negacyclicMul_comm a b, shiftNegZ_negacyclicMul, negacyclicMul_comm,
    shiftNegZ_negacyclicMul]

/-- The convolution theorem for a twiddle exponent additive modulo `2r`: transforming
`∑_x U_x V_{z-x}` with `y^(-E z)` gives the product of the transforms. -/
theorem sum_shiftInv_synthConvG {G : Type*} [AddCommGroup G] [Fintype G] (E : G → ℕ)
    (hE : ∀ x y, E (x + y) % (2 * r) = (E x + E y) % (2 * r)) (U V : G → Fin r → ℂ) :
    ∑ z, shiftInv (E z) (synthConvG U V z) =
      negacyclicMul (∑ x, shiftInv (E x) (U x)) (∑ y, shiftInv (E y) (V y)) := by
  simp only [synthConvG, shiftInv_sum]
  rw [Finset.sum_comm, negacyclicMul_sum_left]
  apply Finset.sum_congr rfl
  intro x _
  rw [negacyclicMul_sum_right]
  refine (Fintype.sum_equiv (Equiv.addLeft x) _ _ fun y => ?_).symm
  simp only [Equiv.coe_addLeft, add_sub_cancel_left]
  rw [shiftInv_congr_mod (hE x y), shiftInv_add, shiftInv_negacyclicMul]

variable {d : ℕ} (N : Fin d → ℕ) [∀ i, NeZero (N i)]

/-- `F⁻` of a box array, as a sum over the box. -/
theorem fwdT_ιR (U : Box N → Fin r → ℂ) (j : ℕ) :
    fwdT (List.ofFn N) (ιR N U) j = (1 / ((List.ofFn N).prod : ℂ)) •
      ∑ x : Box N, shiftInv (synthExpL r (List.ofFn N) j (enc N x)) (U x) := by
  unfold fwdT
  refine congrArg _ ?_
  rw [← sum_box N]
  simp only [ιR, dec_enc]

/-- The convolution theorem: `F⁻(ℳ_r(U, V)) = (F⁻U)(F⁻V)/r` recordwise. -/
theorem fwdT_synthConvNormG (hN : ∀ i, N i ∣ 2 * r) (U V : Box N → Fin r → ℂ) (j : ℕ) :
    fwdT (List.ofFn N) (ιR N (ComplexConv.synthConvNormG U V)) j =
      (1 / (r : ℂ)) • negacyclicMul (fwdT (List.ofFn N) (ιR N U) j)
        (fwdT (List.ofFn N) (ιR N V) j) := by
  rw [fwdT_ιR, fwdT_ιR, fwdT_ιR]
  simp only [ComplexConv.synthConvNormG, shiftInv_smul, ← Finset.smul_sum]
  rw [sum_shiftInv_synthConvG (fun z => synthExpL r (List.ofFn N) j (enc N z))
      (synthExpL_enc_add N hN j) U V, negacyclicMul_smul_left, negacyclicMul_smul_right,
    smul_smul, smul_smul, smul_smul, card_box]
  congr 1
  have hM : ((List.ofFn N).prod : ℂ) ≠ 0 := by
    rw [Nat.cast_ne_zero]; exact (prod_pos (ofFn_pos N)).ne'
  have hr : (r : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne r)
  push_cast
  field_simp

omit [NeZero r] [∀ i, NeZero (N i)] in
theorem dvd_of_powAxes (hP : PowAxes r (List.ofFn N)) (i : Fin d) : N i ∣ 2 * r := by
  obtain ⟨e, he, hd⟩ := hP (N i) (List.mem_ofFn.mpr ⟨i, rfl⟩)
  rw [he]; exact hd

/-- The exact pipeline on box arrays is `ℳ_r`: `M F⁺((F⁻U)(F⁻V)/r) = (U ∗ V)/(rM)`, from the
convolution theorem and `F⁺F⁻ = I/M` (`oppT_fwdT`). -/
theorem pipeE_ιR (hP : PowAxes r (List.ofFn N)) (U V : Box N → Fin r → ℂ) (z : Box N) :
    pipeE (List.ofFn N) (ιR N U) (ιR N V) (enc N z) = ComplexConv.synthConvNormG U V z := by
  have hN : ∀ i, N i ∣ 2 * r := dvd_of_powAxes N hP
  have e : (fun j => (1 / (r : ℂ)) • negacyclicMul (fwdT (List.ofFn N) (ιR N U) j)
      (fwdT (List.ofFn N) (ιR N V) j)) =
      fwdT (List.ofFn N) (ιR N (ComplexConv.synthConvNormG U V)) := by
    funext j; rw [fwdT_synthConvNormG N hN]
  have hM : ((List.ofFn N).prod : ℂ) ≠ 0 := by
    rw [Nat.cast_ne_zero]; exact (prod_pos (ofFn_pos N)).ne'
  simp only [pipeE]
  rw [e, oppT_fwdT hP _ (enc_lt N z), smul_smul, mul_one_div_cancel hM, one_smul]
  simp only [ιR, dec_enc]

end Exact

/-! ### `M̃_r` on box arrays: the guarantee `RingApprox` -/

section Ring

open ComplexConv

variable {r : ℕ} [NeZero r] {d : ℕ} (a : Fin d → ℕ) (N : Fin d → ℕ) [∀ i, NeZero (N i)]

/-- `M̃_r` on box arrays: the computed synthetic convolution `convC` (both computed forward
transforms retained in the order `B`, the pointwise `Q_p(f g / r)`, the computed opposite
transform, and the scaling by `M`) read through the record addresses of the box. -/
noncomputable def synthMr (p : ℕ) (U V : Box N → Fin r → ℂ) : Box N → Fin r → ℂ :=
  fun z => convC a p (ιR N U) (ιR N V) (enc N z)

/-- The constant `E = √2 M (3A + 1)`, `M = ∏ Nᵢ`, `A = maxᵢ aᵢ` the number of rounds. -/
noncomputable def eSynth : ℝ := Real.sqrt 2 * ((∏ i, N i : ℕ) : ℝ) * (3 * (nRounds a : ℝ) + 1)

omit [NeZero r] [∀ i, NeZero (N i)] in
theorem ofFn_eq_tsA (hN : ∀ i, N i = 2 ^ a i) : List.ofFn N = tsA a :=
  congrArg List.ofFn (funext hN)

/-- `prop:synthetic-convolution` in the form of `ComplexConv.RingApprox`: on disk-grid operands
every coefficient of `M̃_r` is within `√2 M (3A + 1) 2^{-p}` of `ℳ_r`. -/
theorem synthMr_ringApprox (hN : ∀ i, N i = 2 ^ a i) (hr : ∀ i, 2 ^ a i ∣ 2 * r) (p : ℕ) :
    RingApprox p (synthMr (r := r) a N p) (eSynth a N) := by
  intro U V hU hV z k
  have hts := ofFn_eq_tsA a N hN
  have hlt : enc N z < (tsA a).prod := hts ▸ enc_lt N z
  have hU' : SupLe (List.ofFn a).sum (ιR N U) 1 := fun n _ c => (hU _ c).2
  have hV' : SupLe (List.ofFn a).sum (ιR N V) 1 := fun n _ c => (hV _ c).2
  have hP : PowAxes r (List.ofFn N) := hts ▸ powAxes_tsA a hr
  have hex : synthConvNormG U V z = convE a (ιR N U) (ιR N V) (enc N z) := by
    rw [convE_eq_pipeE a hr _ _ hlt, ← hts, pipeE_ιR N hP]
  have hM : (tsA a).prod = ∏ i, N i := by rw [← hts, List.prod_ofFn]
  have := convC_err a p hU' hV' (enc N z) hlt k
  rw [hM] at this
  rw [hex]
  exact this

omit [NeZero r] in
/-- `RingApprox` is monotone in the error constant. -/
theorem ringApprox_mono {G : Type*} [AddCommGroup G] [Fintype G] {p : ℕ}
    {Mr : (G → Fin r → ℂ) → (G → Fin r → ℂ) → (G → Fin r → ℂ)} {E E' : ℝ}
    (h : RingApprox p Mr E) (hE : E ≤ E') : RingApprox p Mr E' :=
  fun U V hU hV j k => (h U V hU hV j k).trans hE

/-- The paper's form `√2 M (3ℓ + 1)` for any `ℓ` at least the number of rounds. -/
theorem synthMr_ringApprox_ell (hN : ∀ i, N i = 2 ^ a i) (hr : ∀ i, 2 ^ a i ∣ 2 * r) (p : ℕ)
    {ℓ : ℕ} (hℓ : nRounds a ≤ ℓ) :
    RingApprox p (synthMr (r := r) a N p) (Real.sqrt 2 * ((∏ i, N i : ℕ) : ℝ) * (3 * ℓ + 1)) := by
  refine ringApprox_mono (synthMr_ringApprox a N hN hr p) ?_
  unfold eSynth
  have : (nRounds a : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  gcongr

omit [NeZero r] in
/-- The constant against the paper's `5TL`: with `T = rM`, `r ≥ 2` and `A ≤ ℓ ≤ L`, `ℓ ≥ 1`,
`√2 M (3A + 1) < 5 T L`. -/
theorem eSynth_lt (hr2 : 2 ≤ r) {ℓ L : ℕ} (hA : nRounds a ≤ ℓ) (hℓ : 1 ≤ ℓ) (hL : ℓ ≤ L) :
    eSynth a N < 5 * ((r * ∏ i, N i : ℕ) : ℝ) * L := by
  unfold eSynth
  have hM : 1 ≤ ∏ i, N i := Nat.one_le_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr fun i _ =>
    NeZero.ne (N i))
  set M := ∏ i, N i
  have hs := sqrt_two_le_1415
  have hs0 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hM' : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hA' : (nRounds a : ℝ) ≤ ℓ := by exact_mod_cast hA
  have hℓ' : (1 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  have hL' : (ℓ : ℝ) ≤ L := by exact_mod_cast hL
  have hr' : (2 : ℝ) ≤ r := by exact_mod_cast hr2
  have h1 : Real.sqrt 2 * M * (3 * (nRounds a : ℝ) + 1) ≤ 1.415 * M * (4 * ℓ) := by
    have : 3 * (nRounds a : ℝ) + 1 ≤ 4 * ℓ := by linarith
    have h0 : 0 ≤ 3 * (nRounds a : ℝ) + 1 := by positivity
    calc Real.sqrt 2 * M * (3 * (nRounds a : ℝ) + 1) ≤ 1.415 * M * (3 * (nRounds a : ℝ) + 1) := by
          gcongr
      _ ≤ 1.415 * M * (4 * ℓ) := by gcongr
  have h2 : (1.415 : ℝ) * M * (4 * ℓ) < 5 * (r * M) * L := by
    have hML : (0 : ℝ) < M * ℓ := by positivity
    have : (M : ℝ) * ℓ ≤ M * L := by gcongr
    nlinarith
  push_cast
  linarith

/-- The hypothesis `hM'` of the source-transform assembly, on the box `∏_{i ≤ d} ℤ/tᵢ` with
`t_d = r` and `tᵢ = 2^(aᵢ)` dividing `2r` for `i < d`, with `M̃_r = synthMr`. -/
theorem cconvApprox_box_synth {d : ℕ} (t : Fin (d + 1) → ℕ) [∀ i, NeZero (t i)]
    (h : t (Fin.last d) = r) (a : Fin d → ℕ) (ha : ∀ i, t i.castSucc = 2 ^ a i)
    (hr : ∀ i, 2 ^ a i ∣ 2 * r) {p : ℕ} {θp θm : Fin r → ℂ}
    (hθp : PhaseApprox p θp fun k => twistRoot r k.val)
    (hθm : PhaseApprox p θm fun k => (starRingEnd ℂ) (twistRoot r k.val))
    (hE : 1000 * eSynth a (fun i => t i.castSucc) ≤ 2 ^ p) :
    ∀ f g : ((i : Fin (d + 1)) → ZMod (t i)) → ℂ, ‖f‖ ≤ 1 → ‖g‖ ≤ 7 / 10 →
      2 ^ p * ‖cconvApproxVia (boxSplit t h) p θp θm (synthMr a (fun i => t i.castSucc) p) f g -
          convNormD t f g‖ ≤ eSynth a (fun i => t i.castSucc) + 9 ∧
        ‖cconvApproxVia (boxSplit t h) p θp θm (synthMr a (fun i => t i.castSucc) p) f g‖ ≤
          701 / 1000 :=
  cconvApprox_box t h hθp hθm (synthMr_ringApprox a (fun i => t i.castSucc) ha hr p) hE

end Ring

/-! ### The vendored form: `convM` and `Close` -/

section Vendored

variable {r : ℕ} [NeZero r] {d : ℕ} (a : Fin d → ℕ)

omit [NeZero r] in
theorem zmod_val_sub {n : ℕ} [NeZero n] (x y : ZMod n) :
    (x - y).val = (x.val + (n - y.val)) % n := by
  have h : ((x.val + (n - y.val) : ℕ) : ZMod n) = x - y := by
    rw [Nat.cast_add, Nat.cast_sub (ZMod.val_lt y).le, ZMod.natCast_self, ZMod.natCast_zmod_val,
      ZMod.natCast_zmod_val]
    ring
  rw [← h, ZMod.val_natCast]

omit [NeZero r] in
/-- Cyclic address subtraction is subtraction in the box. -/
theorem subAddr_enc (N : Fin d → ℕ) [∀ i, NeZero (N i)] (z x : Box N) :
    subAddr (List.ofFn N) (enc N z) (enc N x) = enc N (z - x) := by
  rw [subAddr]
  conv_rhs => rw [enc]
  apply undigits_congr
  intro i hi
  rw [List.length_ofFn] at hi
  have h1 : (List.ofFn N).getD i 1 = N ⟨i, hi⟩ := getD_ofFn N ⟨i, hi⟩
  have h2 : digit (List.ofFn N) i (enc N z) = (z ⟨i, hi⟩).val := digit_enc N z ⟨i, hi⟩
  have h3 : digit (List.ofFn N) i (enc N x) = (x ⟨i, hi⟩).val := digit_enc N x ⟨i, hi⟩
  rw [h1, h2, h3, boxDigits_of_lt _ _ hi, Pi.sub_apply, zmod_val_sub]

omit [NeZero r] in
/-- The vendored `convM` on box arrays is `ℳ_r`. -/
theorem convM_ιR (N : Fin d → ℕ) [∀ i, NeZero (N i)] (U V : Box N → Fin r → ℂ) (z : Box N) :
    convM (List.ofFn N) (ιR N U) (ιR N V) (enc N z) = ComplexConv.synthConvNormG U V z := by
  unfold convM
  rw [← sum_box N]
  simp only [ιR, dec_enc, subAddr_enc]
  rw [ComplexConv.synthConvNormG, synthConvG, card_box]

theorem fwdT_congr {ts : List ℕ} {u u' : Recs r} (h : ∀ k < ts.prod, u k = u' k) (j : ℕ) :
    fwdT ts u j = fwdT ts u' j := by
  unfold fwdT
  exact congrArg _ (Finset.sum_congr rfl fun k hk => by rw [h k (Finset.mem_range.1 hk)])

theorem pipeE_congr {ts : List ℕ} {u u' v v' : Recs r} (hu : ∀ k < ts.prod, u k = u' k)
    (hv : ∀ k < ts.prod, v k = v' k) (n : ℕ) : pipeE ts u v n = pipeE ts u' v' n := by
  unfold pipeE
  simp only [fwdT_congr hu, fwdT_congr hv]

omit [NeZero r] in
theorem subAddr_lt {ts : List ℕ} (hpos : ∀ t ∈ ts, 0 < t) (x y : ℕ) : subAddr ts x y < ts.prod :=
  undigits_lt _ _ fun i _ => Nat.mod_lt _ (getD_pos hpos i)

omit [NeZero r] in
theorem convM_congr {ts : List ℕ} (hpos : ∀ t ∈ ts, 0 < t) {u u' v v' : Recs r}
    (hu : ∀ k < ts.prod, u k = u' k) (hv : ∀ k < ts.prod, v k = v' k) (x : ℕ) :
    convM ts u v x = convM ts u' v' x := by
  unfold convM
  exact congrArg _ (Finset.sum_congr rfl fun y hy => by
    rw [hu y (Finset.mem_range.1 hy), hv _ (subAddr_lt hpos x y)])

/-- The exact part of the computed convolution is the vendored `convM = (f ∗ g)/(rM)` on the
first `M` records. -/
theorem convE_eq_convM (hr : ∀ i, 2 ^ a i ∣ 2 * r) (u v : Recs r) {n : ℕ}
    (hn : n < (tsA a).prod) : convE a u v n = convM (tsA a) u v n := by
  rw [convE_eq_pipeE a hr u v hn]
  show pipeE (List.ofFn fun i => 2 ^ a i) u v n = convM (List.ofFn fun i => 2 ^ a i) u v n
  have hu : ∀ k < (List.ofFn fun i => 2 ^ a i).prod,
      u k = ιR (fun i => 2 ^ a i) (fun x => u (enc _ x)) k := fun k hk => by
    simp only [ιR, enc_dec _ hk]
  have hv : ∀ k < (List.ofFn fun i => 2 ^ a i).prod,
      v k = ιR (fun i => 2 ^ a i) (fun x => v (enc _ x)) k := fun k hk => by
    simp only [ιR, enc_dec _ hk]
  have hP : PowAxes r (List.ofFn fun i => 2 ^ a i) := powAxes_tsA a hr
  rw [pipeE_congr hu hv, convM_congr hP.pos hu hv, ← enc_dec (fun i => 2 ^ a i) hn,
    pipeE_ιR _ hP, convM_ιR]

/-- `prop:synthetic-convolution`, numerical part, in the vendored form of
`Spec.SignedRingProduct.MeetsConvolution`: on disk operands the computed convolution is within
less than `√2 M (3ℓ + 1) 2^{-p}` of `convM` on the first `M` records, for every `ℓ ≥ A`. -/
theorem convC_close (hr : ∀ i, 2 ^ a i ∣ 2 * r) (p : ℕ) {ℓ : ℕ} (hA : nRounds a ≤ ℓ)
    {u v : Recs r} (hu : SupLe (List.ofFn a).sum u 1) (hv : SupLe (List.ofFn a).sum v 1) :
    Close (tsA a).prod (convC a p u v) (convM (tsA a) u v)
      (Real.sqrt 2 * (tsA a).prod * (3 * ℓ + 1) / 2 ^ p) := by
  intro n hn c
  have h := convC_err_lt a p hu hv n hn c
  rw [convE_eq_convM a hr u v hn] at h
  have hp : (0 : ℝ) < 2 ^ p := by positivity
  have hA' : (nRounds a : ℝ) ≤ ℓ := by exact_mod_cast hA
  rw [lt_div_iff₀ hp, mul_comm]
  refine h.trans_le ?_
  gcongr

end Vendored

end IntegerMultBounds.MathlibTM2.Mult.SynthErr
