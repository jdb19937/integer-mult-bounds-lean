module

public import IntegerMultBounds.Schoenhage.ConvProgram
public import IntegerMultBounds.Spec.SyntheticConvolutionFacts

/-! The synthetic convolution program meets `prop:synthetic-convolution` on
every admissible instance on which the given forward and opposite programs meet
`lem:synthetic-transform-cost`, with an explicit step count
(`conv_instance`). -/

@[expose] public section

namespace IntegerMultBounds.Schoenhage

open Machine Strm Tp Schedule Spec.SignedRingProduct NLogN

/-- Rounded products of disk records are disk records. -/
theorem prodRec_disk {r : ℕ} [NeZero r] {p : ℕ} {f g : Rec r} (hf : DiskGrid p f.1 f.2)
    (hg : DiskGrid p g.1 g.2) : DiskGrid p (prodRec p f g).1 (prodRec p f g).2 := by
  intro j
  set F := gridPoly p f.1 f.2
  set G := gridPoly p g.1 g.2
  have hF : ‖F‖ ≤ 1 := (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun k => DiskGrid.norm_le hf k
  have hG : ‖G‖ ≤ 1 := (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun k => DiskGrid.norm_le hg k
  have hr : (0 : ℝ) < r := by exact_mod_cast NeZero.pos r
  set u := negacyclicMul F G j / (r : ℂ)
  have hu : ‖u‖ ≤ 1 := by
    have h1 := (norm_le_pi_norm (negacyclicMul F G) j).trans (norm_negacyclicMul_le F G)
    rw [norm_div, Complex.norm_natCast, div_le_one hr]
    have hFG : ‖F‖ * ‖G‖ ≤ 1 := (mul_le_mul hF hG (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
    have := mul_le_mul_of_nonneg_left hFG hr.le
    rw [mul_assoc] at h1
    linarith
  have hp : (0 : ℝ) < 2 ^ p := by positivity
  have hre := abs_rho0_le (2 ^ p * u.re)
  have him := abs_rho0_le (2 ^ p * u.im)
  have hsq : u.re ^ 2 + u.im ^ 2 ≤ 1 := by
    have := Complex.sq_norm u
    rw [Complex.normSq_apply] at this
    nlinarith [norm_nonneg u]
  have hreal : ((rho0 (2 ^ p * u.re) : ℝ)) ^ 2 + ((rho0 (2 ^ p * u.im) : ℝ)) ^ 2 ≤ ((2 : ℝ) ^ p) ^ 2 := by
    have a1 : ((rho0 (2 ^ p * u.re) : ℝ)) ^ 2 ≤ (2 ^ p * u.re) ^ 2 := sq_le_sq.mpr (by simpa using hre)
    have a2 : ((rho0 (2 ^ p * u.im) : ℝ)) ^ 2 ≤ (2 ^ p * u.im) ^ 2 := sq_le_sq.mpr (by simpa using him)
    nlinarith
  show (rho0 (2 ^ p * u.re)) ^ 2 + (rho0 (2 ^ p * u.im)) ^ 2 ≤ (2 : ℤ) ^ (2 * p)
  have e : ((2 : ℤ) ^ (2 * p) : ℤ) = ((2 ^ p) ^ 2 : ℤ) := by rw [← pow_mul, mul_comm]
  rw [e]
  exact_mod_cast hreal

theorem axisLengths_pow {d ℓ : ℕ} {ts : List ℕ} (h : AxisLengths d ℓ ts) : ∀ t ∈ ts, ∃ e, t = 2 ^ e :=
  fun t ht => by rcases h.2 t ht with rfl | rfl <;> exact ⟨_, rfl⟩

theorem powAxes_of_axisLengths {d ℓ : ℕ} {ts : List ℕ} (h : AxisLengths d ℓ ts) : PowAxes (2 ^ ℓ) ts := by
  intro t ht
  rcases h.2 t ht with rfl | rfl
  · refine ⟨ℓ - 1, rfl, ?_⟩
    exact Dvd.dvd.mul_left (pow_dvd_pow 2 (Nat.sub_le ℓ 1)) 2
  · exact ⟨ℓ, rfl, Dvd.intro_left 2 rfl⟩

theorem arrayVec_scale {r : ℕ} (p k : ℕ) (vs : List (Rec r)) (n : ℕ) :
    arrayVec p (vs.map (scaleRec k)) n = (2 ^ k : ℂ) • arrayVec p vs n := by
  unfold arrayVec
  rw [List.getElem?_map]
  cases vs[n]? with
  | none => simp
  | some f =>
    funext j
    simp only [Option.map_some, gridPoly, scaleRec, Pi.smul_apply, smul_eq_mul]
    have hre : ((2 : ℂ) ^ k).re = 2 ^ k := by
      rw [← Complex.ofReal_ofNat, ← Complex.ofReal_pow, Complex.ofReal_re]
    have him : ((2 : ℂ) ^ k).im = 0 := by
      rw [← Complex.ofReal_ofNat, ← Complex.ofReal_pow, Complex.ofReal_im]
    apply Complex.ext <;> simp [hre, him] <;> ring

/-! ### One instance -/

/-- The steps beyond the transforms: pointwise products, scaling and data movement. -/
def convExtra (p d ℓ K w H M : ℕ) : ℕ :=
  pwCost p d ℓ K w H M (2 * 2 ^ ℓ * w * M) +
    convScaleCost p (2 ^ ℓ) w H (2 * 2 ^ ℓ * w * M) (2 * 2 ^ ℓ * M) (Nat.log 2 M) +
    coreExtra H (2 * 2 ^ ℓ * w * M) (2 * 2 ^ ℓ * w * M) (2 * 2 ^ ℓ * w * M) (2 * 2 ^ ℓ * w * M)
      (2 * 2 ^ ℓ * w * M) (2 * 2 ^ ℓ * w * M) +
    4 * (H + 2 * (2 * 2 ^ ℓ * w * M) + 2 * 2 ^ ℓ * (w + Nat.log 2 M) * M + (gamma (w + Nat.log 2 M)).length) + 60

set_option maxHeartbeats 8000000 in
theorem conv_instance {t q₁ q₂ a : ℕ} (Mf : Program t q₁ a) (Mo : Program t q₂ a) (ht : 4 ≤ t)
    (P : TransformParams) (L : Layout) (C : ℝ) {p d ℓ K w : ℕ} {ts : List ℕ}
    (hadm : Admissible P p d ℓ K w ts) (hMF : MeetsForward P Mf L C p d ℓ K w ts)
    (hMO : MeetsOpposite P Mo L C p d ℓ K w ts) (fs gs : List (Rec (2 ^ ℓ)))
    (hfl : fs.length = ts.prod) (hgl : gs.length = ts.prod)
    (hfd : ∀ f ∈ fs, DiskGrid p f.1 f.2) (hgd : ∀ g ∈ gs, DiskGrid p g.1 g.2) :
    ∃ (hs : List (Rec (2 ^ ℓ))) (k : ℕ), hs.length = ts.prod ∧
      Close ts.prod (arrayVec p hs) (convM ts (arrayVec p fs) (arrayVec p gs))
        (Real.sqrt 2 * ts.prod * (3 * ℓ + 1) / 2 ^ p) ∧
      (k : ℝ) ≤ 3 * C * transformCost P p d ℓ K ts +
        (convExtra p d ℓ K w (transformHeader p d (2 ^ ℓ) K w ts).length ts.prod : ℕ) ∧
      HoareTime (convProg Mf Mo ht) (· = bank5 (transformHeader p d (2 ^ ℓ) K w ts) (array w fs) (array w gs) [] [])
        (· = bank5 (transformHeader p d (2 ^ ℓ) K w ts) (array w fs) (array w gs)
          (array (outWidth w ts) hs) (gamma (outWidth w ts))) k := by
  obtain ⟨-, -, -, -, hd2, hℓ2, hℓp, -, -, hK1, -, hax, hpw, -⟩ := hadm
  have hpow := powAxes_of_axisLengths hax
  obtain ⟨hkz, hM2⟩ := axes_zeros (axisLengths_pow hax)
  set M := ts.prod
  set k := Nat.log 2 M
  set hdr := transformHeader p d (2 ^ ℓ) K w ts
  obtain ⟨Fs, kF, hFl, hFd, hFc, hFk, hFh⟩ := hMF fs hfl hfd
  obtain ⟨Gs, kG, hGl, hGd, hGc, hGk, hGh⟩ := hMF gs hgl hgd
  set Us := List.zipWith (prodRec p) Fs Gs
  have hUl : Us.length = M := by simp only [Us, List.length_zipWith, hFl, hGl, min_self]; rfl
  have hUd : ∀ u ∈ Us, DiskGrid p u.1 u.2 := by
    intro u hu
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hu
    simp only [Us, List.getElem_zipWith]
    exact prodRec_disk (hFd _ (List.getElem_mem _)) (hGd _ (List.getElem_mem _))
  obtain ⟨Vs, kO, hVl, hVd, hVc, hVk, hVh⟩ := hMO Us hUl hUd
  have hP := pwCoreProg_hoare (ts := ts) (p := p) (d := d) (l := ℓ) (K := K) (w := w) (by omega) (by omega)
    hK1 hpw (hFl.trans hGl.symm) hFd hGd
  have hw1 : 1 ≤ w := by omega
  obtain ⟨σ', kS, hx, hq, hkS⟩ := runs_convScale (p := p) (d := d) (l := ℓ) (K := K) (w := w) (ts := ts)
    (x := array w Vs) (by omega) (by omega) hK1 hw1 (axisLengths_pow hax) (scaleStart hdr (array w Vs))
    (by funext i; simp [scaleStart, ι_ne_high (show 64 ≤ (zH : Fin 𝕌).val by decide),
      ι_ne_high (show 64 ≤ (zF : Fin 𝕌).val by decide)])
    (by tsimp [scaleStart, hdr]) (by tsimp [scaleStart]) (by tsimp [scaleStart]) (by tsimp [scaleStart])
    (by tsimp [scaleStart]) (by tsimp [scaleStart]) (by tsimp [scaleStart]) (by tsimp [scaleStart])
    (by tsimp [scaleStart])
  subst hq
  have hS := (compile_correct (a := 0) (by decide) hx).consequence (fun v h => h) (fun v h => h) hkS
  have hconv := convProg_hoare Mf Mo ht hFh hGh hP hVh hS
  have hout : (cut w (array w Vs)).flatMap (· ++ List.replicate k false) =
      array (outWidth w ts) (Vs.map (scaleRec k)) := (array_scale hw1 k Vs).symm
  rw [hout] at hconv
  refine ⟨Vs.map (scaleRec k), _, by rw [List.length_map, hVl], ?_, ?_, hconv⟩
  · have hc := conv_error hpow (L p d ℓ K w ts) fs gs Fs Gs Vs hfd hFl hGl hGd hFc hGc hVc
    intro n hn j
    have := hc n hn j
    rw [arrayVec_scale]
    have hMc : ((M : ℕ) : ℂ) = (2 : ℂ) ^ k := by rw [hM2]; push_cast; rfl
    rw [← hMc]
    exact this
  · have hlenF : (array w Fs).length = 2 * 2 ^ ℓ * w * M := by rw [length_array, hFl]
    have hlenG : (array w Gs).length = 2 * 2 ^ ℓ * w * M := by rw [length_array, hGl]
    have hlenU : (array w Us).length = 2 * 2 ^ ℓ * w * M := by rw [length_array, hUl]
    have hlenV : (array w Vs).length = 2 * 2 ^ ℓ * w * M := by rw [length_array, hVl]
    have hlenf : (array w fs).length = 2 * 2 ^ ℓ * w * M := by rw [length_array, hfl]
    have hleng : (array w gs).length = 2 * 2 ^ ℓ * w * M := by rw [length_array, hgl]
    have hlenO : (array (outWidth w ts) (Vs.map (scaleRec k))).length = 2 * 2 ^ ℓ * (w + k) * M := by
      rw [length_array, List.length_map, hVl]; rfl
    have hcut : (cut w (array w Vs)).length = 2 * 2 ^ ℓ * M := by
      rw [length_cut hw1 _ (by rw [hlenV]; exact ⟨2 * 2 ^ ℓ * M, by ring⟩), hlenV]
      rw [show 2 * 2 ^ ℓ * w * M = (2 * 2 ^ ℓ * M) * w by ring, Nat.mul_div_cancel _ (by omega)]
    have hcost : (kF : ℝ) + kG + kO ≤ 3 * C * transformCost P p d ℓ K ts := by linarith
    rw [hlenF, hlenG, hlenU, hlenV, hlenf, hleng, hlenO, hcut, hFl] at *
    unfold convExtra
    push_cast
    simp only [outWidth] at *
    linarith

end IntegerMultBounds.Schoenhage
