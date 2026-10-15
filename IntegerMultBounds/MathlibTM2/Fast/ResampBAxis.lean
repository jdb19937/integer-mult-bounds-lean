module

public import IntegerMultBounds.MathlibTM2.Fast.ResampBLine

/-!
# The fast `B̃₀` along the innermost axis of a padded box

The register `src` holds a box array as a coefficient stream whose lines along the innermost
axis are contiguous: `lines.flatten`, every line `t` records long. `rsbAxisP` runs the line
machine `rsbLineP` (`Fast/ResampBLine`) while `src` is nonempty, collecting the outputs (reversed)
on `dst`, and moves them back onto `src`.

* `rsbLineG p K m E D L`: the `t` outputs of one line `L` of `t` records, the numerators
  `rsbLineNum p K m E D` of `B̃₀` followed by `t - s` zero records.
* `RsbLineOk w p K m E L`: the conditions under which the line machine computes `rsbLineG` on `L`:
  every record of `L` and every Horner iterate fits `w` bits.
* `rsb_axis_runs`: `src = cstream (lines.flatten)` becomes `cstream (lines.flatMap rsbLineG)`,
  every other register restored (`dst` empty before and after), within
  `|lines| (rsbLineCost T w s t m K + 2) + 2 |lines| t w + 4` steps.
* `rsbLineOk_of_ball`: a line whose grid values and whose Horner iterates have norm at most one
  is admissible at width `w ≥ p + 2`.
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2.Fast

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.NLogN (rowIndex)

set_option linter.unusedSimpArgs false

noncomputable section

section Axis

variable {s t : ℕ} [NeZero s] [NeZero t]

/-- The line `L` as an array on `ZMod t` (entries past the end are zero). -/
def rsbVec (L : List GaussianInt) : ZMod t → GaussianInt := fun j => L.getD j.val 0

omit [NeZero t] in
lemma rsbArr_rsbVec (L : List GaussianInt) (hL : L.length = t) :
    rsbArr (rsbVec (t := t) L) = L := by
  apply List.ext_getElem (by simp [length_rsbArr, hL])
  intro i h₁ h₂
  have hi : i < t := by simpa [length_rsbArr] using h₁
  simp [rsbArr, rsbVec, ZMod.val_natCast_of_lt hi, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem h₂, Nat.mod_eq_of_lt hi]

variable (s t) in
/-- The `t` outputs of `B̃₀` on one line of `t` records: `s` numerators and `t - s` zeros. -/
def rsbLineG (p K m : ℕ) (E : ZMod s → ℤ → ℤ) (D : ZMod s → ℤ) (L : List GaussianInt) :
    List GaussianInt :=
  rsbArr (rsbLineNum p K m E D (rsbVec (t := t) L)) ++ List.replicate (t - s) 0

omit [NeZero s] [NeZero t] in
lemma length_rsbLineG (p K m : ℕ) (E : ZMod s → ℤ → ℤ) (D : ZMod s → ℤ) (L : List GaussianInt)
    (hst : s ≤ t) : (rsbLineG s t p K m E D L).length = t := by
  simp [rsbLineG, length_rsbArr]; omega

variable (s t) in
/-- The fit conditions of one line. -/
def RsbLineOk (w p K m : ℕ) (E : ZMod s → ℤ → ℤ) (L : List GaussianInt) : Prop :=
  L.length = t ∧ (∀ x ∈ L, Fits w x) ∧
    ∀ k ≤ K, ∀ ℓ, Fits w (rsbIter p m E (rsbHalf (rsbVec (t := t) L)) k ℓ)

variable {T Q A : ℕ} {U : Type} {P : Type}

variable (rg : RsbR → Fin T) {ι : Fin 64 → Fin T} (hι : Function.Injective ι) (hT : 64 ≤ T)
  (hQ : SS.states ≤ Q)

/-- `B̃₀` along the innermost axis: one line per iteration while `src` is nonempty, then the
outputs back onto `src`. -/
def rsbAxisP : Pr P T Q A U :=
  .seq (rsbWhile (rg .src) (rsbLineP rg hι hT hQ)) (moveR (rg .dst) (rg .src) id)

variable {body : P → Pr P T Q A U} {rg}

/-- **`B̃₀` along the innermost axis.** The register `src` holds the lines `lines` (each of `t`
records, `RsbLineOk`), `dst` is empty, and the other registers are as for `rsb_line_runs`.
Afterwards `src` holds the outputs `lines.flatMap (rsbLineG s t p K m E D)` and every other
register is as before. -/
theorem rsb_axis_runs (hrg : Function.Injective rg) (hdisj : ∀ r j, rg r ≠ ι j) (hA : 96 ≤ A)
    {w p m K : ℕ} (hst : s < t) (hm : m ≤ s) (hp1 : 1 ≤ p) (hpw : p < w)
    (E : ZMod s → ℤ → ℤ) (D : ZMod s → ℤ)
    (hfE : ∀ ℓ, ∀ h ∈ rsbHs m, Fits w (rsbReal (E ℓ h))) (hfD : ∀ ℓ, Fits w (rsbReal (D ℓ)))
    (lines : List (List GaussianInt)) (hok : ∀ L ∈ lines, RsbLineOk s t w p K m E L)
    (σ : RsbR → List (Fin (A + 4))) (henv : RsbEnv σ w p s m)
    (hsrc : σ .src = cstream A w lines.flatten) (hdst : σ .dst = [])
    (hmsk : σ .msk = (rsbMask s t).map bitSymbol)
    (hef : σ .ef = cstream A w (rsbETab s m E))
    (hdf : σ .df = cstream A w (rsbArr fun ℓ => rsbReal (D ℓ)))
    (hhf : σ .hf = csyms A w (rsbReal (2 ^ (p - 1))))
    (hkn : (σ .kn).length = K) (htswn : (σ .tswn).length = (t - s) * w)
    (hms : σ .ms = []) (hsr : σ .sr = []) (hsel : σ .sel = []) (hhv : σ .hv = [])
    (hvk : σ .vk = []) (hdout : σ .dout = []) (htK : σ .tK = []) :
    RsbRuns body rg ι (rsbAxisP rg hι hT hQ) σ
      (Function.update σ .src (cstream A w (lines.flatMap (rsbLineG s t p K m E D))))
      (lines.length * (rsbLineCost T w s t m K + 2) + 2 * (lines.length * t * w) + 4) := by
  have hw : 1 ≤ w := by have := henv.ready.wn; omega
  have ht : 1 ≤ t := by omega
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : ℕ → RsbR → List (Fin (A + 4)), Ψ = fun j =>
      Function.update (Function.update σ .src (cstream A w (lines.drop j).flatten)) .dst
        (cstream A w ((lines.take j).flatMap (rsbLineG s t p K m E D))).reverse := ⟨_, rfl⟩
  have hbody : ∀ j < lines.length, RsbRuns body rg ι (rsbLineP rg hι hT hQ) (Ψ j) (Ψ (j + 1))
      (rsbLineCost T w s t m K) := by
    intro j hj
    obtain ⟨hlen, hfx, hfit⟩ := hok lines[j] (List.getElem_mem hj)
    have hsrcj : Ψ j .src = cstream A w (rsbArr (rsbVec (t := t) lines[j])) ++
        cstream A w (lines.drop (j + 1)).flatten := by
      rw [rsbArr_rsbVec _ hlen, ← cstream_append, ← List.flatten_cons,
        ← List.drop_eq_getElem_cons hj]
      simp [hΨ]
    have henv' : RsbEnv (Ψ j) w p s m := by
      rw [hΨ]
      exact (henv.update (by simp [RsbFreeReg]) _).update (by simp [RsbFreeReg]) _
    refine (rsb_line_runs hrg hdisj hι hT hQ hA hst hm hp1 hpw E D (rsbVec lines[j])
      (fun i => by
        simp only [rsbVec]
        by_cases hi : i.val < lines[j].length
        · rw [List.getD_eq_getElem _ _ hi]; exact hfx _ (List.getElem_mem hi)
        · rw [List.getD_eq_default _ _ (by omega)]; exact ⟨by simp, by simp⟩)
      hfE hfD hfit (Ψ j) henv' _ hsrcj (by simp [hΨ, hmsk]) (by simp [hΨ, hef])
      (by simp [hΨ, hdf]) (by simp [hΨ, hhf]) (by simp [hΨ, hkn]) (by simp [hΨ, htswn])
      (by simp [hΨ, hms]) (by simp [hΨ, hsr]) (by simp [hΨ, hsel]) (by simp [hΨ, hhv])
      (by simp [hΨ, hvk]) (by simp [hΨ, hdout]) (by simp [hΨ, htK])).congr ?_
    have htk : (lines.take (j + 1)).flatMap (rsbLineG s t p K m E D) =
        (lines.take j).flatMap (rsbLineG s t p K m E D) ++ rsbLineG s t p K m E D lines[j] := by
      rw [List.take_succ, List.getElem?_eq_getElem hj, Option.toList_some, List.flatMap_append]
      simp
    funext r
    cases r <;> simp [hΨ, htk, reverse_cstream_append, rsbLineG]
  have H := rsb_while_runs (body := body) hdisj (ra := .src) (rsbLineP rg hι hT hQ) Ψ
    lines.length (rsbLineCost T w s t m K)
    (fun j hj => by
      obtain ⟨hlen, -, -⟩ := hok lines[j] (List.getElem_mem hj)
      rw [hΨ]
      simp only [Function.update_of_ne (show RsbR.src ≠ .dst by decide), Function.update_self]
      rw [List.drop_eq_getElem_cons hj, List.flatten_cons, cstream_append]
      intro h
      have := congrArg List.length h
      simp [hlen] at this
      have : 0 < t * w := Nat.mul_pos (by omega) (by omega)
      omega)
    (by simp [hΨ]) hbody
  have e₀ : Ψ 0 = σ := by
    funext r; cases r <;> simp [hΨ, hsrc, hdst]
  rw [e₀] at H
  have H₂ := rsb_moveR_runs (body := body) (ι := ι) hrg (a := .dst) (b := .src) (by decide)
    (Ψ lines.length)
  refine ((RsbRuns.seq hdisj H H₂).congr ?_).mono ?_
  · funext r; cases r <;> simp [hΨ, hdst]
  · have hlg : ((lines.take lines.length).flatMap (rsbLineG s t p K m E D)).length =
        lines.length * t := by
      rw [List.take_length, rsb_length_flatMap_const _ _ t
        (fun L => length_rsbLineG p K m E D L hst.le)]
    simp only [hΨ, Function.update_self, List.length_reverse, length_cstream, hlg]
    nlinarith

end Axis

/-! ### Admissible lines from the unit disk -/

section Ball

open IntegerMultBounds.NLogN
open IntegerMultBounds.Resampling.OffDiagSum (offTermW)

/-- The numerator of a grid value of norm at most one fits `w ≥ p + 2` bits. -/
lemma rsb_fits_of_norm_le {w p : ℕ} (hw : p + 2 ≤ w) (N : GaussianInt)
    (h : ‖rsbGrid p N‖ ≤ 1) : Fits w N := by
  have hp : (0 : ℝ) < 2 ^ p := by positivity
  have hlt : (2 : ℝ) ^ p < 2 ^ (w - 1) := pow_lt_pow_right₀ (by norm_num) (by omega)
  have hre : |(N.re : ℝ)| ≤ 2 ^ p := by
    have h1 := (Complex.abs_re_le_norm (rsbGrid p N)).trans h
    rw [rsbGrid, two_pow_complex, toComplex_div_re, abs_div, abs_of_pos hp, div_le_one hp] at h1
    exact h1
  have him : |(N.im : ℝ)| ≤ 2 ^ p := by
    have h1 := (Complex.abs_im_le_norm (rsbGrid p N)).trans h
    rw [rsbGrid, two_pow_complex, toComplex_div_im, abs_div, abs_of_pos hp, div_le_one hp] at h1
    exact h1
  constructor
  · have : (|N.re| : ℝ) < 2 ^ (w - 1) := by linarith
    exact_mod_cast this
  · have : (|N.im| : ℝ) < 2 ^ (w - 1) := by linarith
    exact_mod_cast this

variable {s t : ℕ} [NeZero s] [NeZero t]

omit [NeZero t] in
/-- **Admissible lines.** A line of `t` records whose grid values have norm at most one, and
whose first `K + 1` rounded Horner iterates have norm at most one, is admissible for the line
machine at width `w ≥ p + 2`. `rsb_iter_ball` gives the second condition from the first in the
regime of `FastB0.resampB₀NumK_spec`. -/
theorem rsbLineOk_of_ball {w p K m : ℕ} (hw : p + 2 ≤ w) (E : ZMod s → ℤ → ℤ)
    (L : List GaussianInt) (hL : L.length = t)
    (hLn : ∀ j : ZMod t, ‖rsbGrid p (rsbVec (t := t) L j)‖ ≤ 1)
    (hball : ∀ k ≤ K, ‖hornerNeumannR (rdV p)
      (offDiagNum m (offTermW p fun ℓ h => (E ℓ h : ℝ) / 2 ^ p))
      (rdV p ((1 / 2 : ℂ) • rowSelect s t (fun j => rsbGrid p (rsbVec (t := t) L j)))) k‖ ≤ 1) :
    RsbLineOk s t w p K m E L := by
  refine ⟨hL, fun x hx => ?_, fun k hk ℓ => ?_⟩
  · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
    have h := hLn (i : ZMod t)
    have hv : rsbVec (t := t) L (i : ZMod t) = L[i] := by
      simp [rsbVec, ZMod.val_natCast, Nat.mod_eq_of_lt (hL ▸ hi), List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem hi]
    rw [hv] at h
    exact rsb_fits_of_norm_le hw _ h
  · have h := hball k hk
    rw [rsb_half_grid, hornerNeumannR_rsbGrid] at h
    exact rsb_fits_of_norm_le hw _ ((norm_le_pi_norm _ ℓ).trans h)

end Ball

end

end IntegerMultBounds.MathlibTM2.Fast
