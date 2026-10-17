module

public import IntegerMultBounds.MathlibTM2.Mult.SynthErrRoundsQ
public import IntegerMultBounds.MathlibTM2.Mult.SynthErr

/-!
# Computed synthetic convolution with approximate rounds

`convC` of `SynthErr` with the forward and opposite rounds replaced by computed rounds `F`, `O`
(`RoundOp`) within `η = √2 (1 + t) 2^{-p}` of the exact rounds. The pointwise products keep the
truncation `Q_p`.

* `convQ_err`: on disk operands `2^p |convQ − convE| ≤ √2 M (3A(1 + t) + 1)` on the first `M`
  records, the bound of `convC_err` with every round error scaled by `1 + t`.
* `synthMrQ_ringApprox`: `RingApprox p (synthMrQ a N p F O) (eSynthQ a N t)`.
* `eSynthQ_lt`: for `t ≤ 1/8` the constant stays below the paper's `5TL`, as in `eSynth_lt`.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.SynthErr

open IntegerMultBounds IntegerMultBounds.NLogN IntegerMultBounds.Spec.SignedRingProduct
open IntegerMultBounds.MathlibTM2.Mult.Rounds

section Conv

variable {r : ℕ} [NeZero r] {d : ℕ} (a : Fin d → ℕ) {p : ℕ} {t : ℝ}

/-- The round error of an approximate round with relative slack `t`. -/
noncomputable def etaQ (p : ℕ) (t : ℝ) : ℝ := Real.sqrt 2 * (1 + t) / 2 ^ p

/-- The computed synthetic convolution with computed forward rounds `F` and opposite rounds `O`. -/
noncomputable def convQ (F : RoundOp (List.ofFn a).sum p (fwdRound (r := r) (List.ofFn a)) (etaQ p t))
    (O : RoundOp (List.ofFn a).sum p (oppRound (r := r) (List.ofFn a)) (etaQ p t)) (u v : Recs r) :
    Recs r :=
  fun n => ((tsA a).prod : ℂ) • oppRoundsQ O (nRounds a)
    (pwC p (fwdRoundsQ F (nRounds a) u) (fwdRoundsQ F (nRounds a) v)) n

/-- The error of the computed convolution on disk operands. -/
theorem convQ_err
    (F : RoundOp (List.ofFn a).sum p (fwdRound (r := r) (List.ofFn a)) (etaQ p t))
    (O : RoundOp (List.ofFn a).sum p (oppRound (r := r) (List.ofFn a)) (etaQ p t)) {u v : Recs r}
    (hu : SupLe (List.ofFn a).sum u 1) (hv : SupLe (List.ofFn a).sum v 1)
    (hug : GridR p u) (hvg : GridR p v) :
    ∀ n < (tsA a).prod, ∀ c, 2 ^ p * ‖convQ a F O u v n c - convE a u v n c‖ ≤
      Real.sqrt 2 * (tsA a).prod * (3 * nRounds a * (1 + t) + 1) := by
  have hfu := fwdRoundsQ_err (List.ofFn a) F (nRounds a) hu hug
    (supLe_sub_self (List.ofFn a).sum u)
  have hfv := fwdRoundsQ_err (List.ofFn a) F (nRounds a) hv hvg
    (supLe_sub_self (List.ofFn a).sum v)
  have hd := fwdRounds_supLe (List.ofFn a) (nRounds a) hu
  have hdu := (fwdRoundsQ_dom (List.ofFn a) F (nRounds a) hu hug).1
  have hd' := (fwdRoundsQ_dom (List.ofFn a) F (nRounds a) hv hvg).1
  have hpw := pwC_err p hd hd' hfu hfv
  have ho := oppRoundsQ_err (List.ofFn a) O (nRounds a) (pwC_supLe p hdu hd') (gridR_rdR p _) hpw
  intro n hn c
  rw [tsA_prod] at hn
  have h := ho n hn c
  have hp : (0 : ℝ) < 2 ^ p := by positivity
  have e : convQ a F O u v n c - convE a u v n c = ((tsA a).prod : ℂ) *
      (oppRoundsQ O (nRounds a) (pwC p (fwdRoundsQ F (nRounds a) u) (fwdRoundsQ F (nRounds a) v)) -
        oppRounds (List.ofFn a) (nRounds a) (pwE (fwdRounds (List.ofFn a) (nRounds a) u)
          (fwdRounds (List.ofFn a) (nRounds a) v))) n c := by
    simp only [convQ, convE, Pi.smul_apply, smul_eq_mul, Pi.sub_apply, mul_sub]
  rw [e, norm_mul, Complex.norm_natCast]
  calc 2 ^ p * ((tsA a).prod * ‖_‖)
      ≤ 2 ^ p * ((tsA a).prod * (2 * (0 + nRounds a * etaQ p t) + Real.sqrt 2 / 2 ^ p +
          nRounds a * etaQ p t)) := by gcongr
    _ = Real.sqrt 2 * (tsA a).prod * (3 * nRounds a * (1 + t) + 1) := by
        rw [etaQ]; field_simp; ring

end Conv

section Ring

open ComplexConv

variable {r : ℕ} [NeZero r] {d : ℕ} (a : Fin d → ℕ) (N : Fin d → ℕ) [∀ i, NeZero (N i)]
  {p : ℕ} {t : ℝ}

/-- `M̃_r` on box arrays with computed rounds `F`, `O`. -/
noncomputable def synthMrQ (F : RoundOp (List.ofFn a).sum p (fwdRound (r := r) (List.ofFn a)) (etaQ p t))
    (O : RoundOp (List.ofFn a).sum p (oppRound (r := r) (List.ofFn a)) (etaQ p t))
    (U V : Box N → Fin r → ℂ) : Box N → Fin r → ℂ :=
  fun z => convQ a F O (ιR N U) (ιR N V) (enc N z)

/-- The constant `√2 M (3A(1 + t) + 1)`. -/
noncomputable def eSynthQ (t : ℝ) : ℝ :=
  Real.sqrt 2 * ((∏ i, N i : ℕ) : ℝ) * (3 * (nRounds a : ℝ) * (1 + t) + 1)

/-- `prop:synthetic-convolution` with computed rounds, in the form of `RingApprox`. -/
theorem synthMrQ_ringApprox (hN : ∀ i, N i = 2 ^ a i) (hr : ∀ i, 2 ^ a i ∣ 2 * r)
    (F : RoundOp (List.ofFn a).sum p (fwdRound (r := r) (List.ofFn a)) (etaQ p t))
    (O : RoundOp (List.ofFn a).sum p (oppRound (r := r) (List.ofFn a)) (etaQ p t)) :
    RingApprox p (synthMrQ (r := r) a N F O) (eSynthQ a N t) := by
  intro U V hU hV z k
  have hts := ofFn_eq_tsA a N hN
  have hlt : enc N z < (tsA a).prod := hts ▸ enc_lt N z
  have hU' : SupLe (List.ofFn a).sum (ιR N U) 1 := fun n _ c => (hU _ c).2
  have hV' : SupLe (List.ofFn a).sum (ιR N V) 1 := fun n _ c => (hV _ c).2
  have hUg : GridR p (ιR N U) := fun n c => (hU _ c).1
  have hVg : GridR p (ιR N V) := fun n c => (hV _ c).1
  have hP : PowAxes r (List.ofFn N) := hts ▸ powAxes_tsA a hr
  have hex : synthConvNormG U V z = convE a (ιR N U) (ιR N V) (enc N z) := by
    rw [convE_eq_pipeE a hr _ _ hlt, ← hts, pipeE_ιR N hP]
  have hM : (tsA a).prod = ∏ i, N i := by rw [← hts, List.prod_ofFn]
  have := convQ_err a F O hU' hV' hUg hVg (enc N z) hlt k
  rw [hM] at this
  rw [hex]
  exact this

omit [NeZero r] in
/-- For `t ≤ 1/8`, `√2 M (3A(1 + t) + 1) < 5 T L` with `T = rM`, `r ≥ 2`, `A ≤ ℓ ≤ L`, `ℓ ≥ 1`. -/
theorem eSynthQ_lt (hr2 : 2 ≤ r) {ℓ L : ℕ} (hA : nRounds a ≤ ℓ) (hℓ : 1 ≤ ℓ) (hL : ℓ ≤ L)
    (ht : 0 ≤ t) (ht8 : t ≤ 1 / 8) :
    eSynthQ a N t < 5 * ((r * ∏ i, N i : ℕ) : ℝ) * L := by
  unfold eSynthQ
  have hM : 1 ≤ ∏ i, N i := Nat.one_le_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr fun i _ =>
    NeZero.ne (N i))
  set M := ∏ i, N i
  have hs := sqrt_two_le_1415
  have hM' : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hA' : (nRounds a : ℝ) ≤ ℓ := by exact_mod_cast hA
  have hA0 : (0 : ℝ) ≤ nRounds a := Nat.cast_nonneg _
  have hℓ' : (1 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  have hL' : (ℓ : ℝ) ≤ L := by exact_mod_cast hL
  have hr' : (2 : ℝ) ≤ r := by exact_mod_cast hr2
  have h0 : 3 * (nRounds a : ℝ) * (1 + t) + 1 ≤ 5 * ℓ := by nlinarith
  have h1 : Real.sqrt 2 * M * (3 * (nRounds a : ℝ) * (1 + t) + 1) ≤ 1.415 * M * (5 * ℓ) := by
    have h0' : 0 ≤ 3 * (nRounds a : ℝ) * (1 + t) + 1 := by nlinarith
    calc Real.sqrt 2 * M * (3 * (nRounds a : ℝ) * (1 + t) + 1)
        ≤ 1.415 * M * (3 * (nRounds a : ℝ) * (1 + t) + 1) := by gcongr
      _ ≤ 1.415 * M * (5 * ℓ) := by gcongr
  have h2 : (1.415 : ℝ) * M * (5 * ℓ) < 5 * (r * M) * L := by
    have hML : (0 : ℝ) < M * ℓ := by positivity
    have : (M : ℝ) * ℓ ≤ M * L := by gcongr
    nlinarith
  push_cast
  linarith

end Ring

end IntegerMultBounds.MathlibTM2.Mult.SynthErr
