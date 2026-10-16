module

public import IntegerMultBounds.MathlibTM2.Fast.ResampBAll
public import IntegerMultBounds.MathlibTM2.Mult.Pipeline

/-!
# `B̃₀` of the pipeline on the padded box

`lineBN n i` is `resampB₀NumK (p n) (α²) (fastWindow (p n) α)` with the integer weight
tables `tableE`, `tableD` of axis `i`. `rsbLineBData n Lb hs i` is the axis data of the machine
for these tables, and `rsb_lineB_eq` says that the numeric maps of the machine's axis data are
`lineB n`.

* `rsb_all_lineB`: `rsb_all_tensor` for this data: the machine `rsbAllP` turns the padded stream
  of the numerators of `u` into the padded stream of the numerators of
  `tensorZR (d n) (t n) (s n) (lineB n) u`.
* In the regime `Big n` at width `w ≥ p n + 2`: `rsb_fitsE`, `rsb_fitsD` (the table entries fit),
  `rsb_pipe_lineOk` (every line in the unit disk is admissible, for any number of Horner steps),
  `rsb_pipe_lineG_ball` (the line map keeps the unit disk), `rsb_flat_mem` (a property of the
  entries kept by every line map holds for every intermediate box).
* `rsb_all_lineB_disk`: `rsb_all_lineB` for an input array in the unit disk, with all fit
  conditions discharged.
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2.Fast

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.NLogN
open IntegerMultBounds.Networks.Shared50ModularControl (prime)

noncomputable section

/-- The Neumann `B̃₀` line map of axis `i` (superseded in the pipeline by the banded line). -/
noncomputable def lineBN (n : ℕ) (i : Fin (Mult.Sizes.d n)) :
    (ZMod (Mult.Sizes.t n i) → ℂ) → ZMod (Mult.Sizes.s n i) → ℂ :=
  Mult.FastB0.resampB₀NumK (Mult.Sizes.p n) (Mult.Sizes.alpha n ^ 2)
    (Mult.FastB0.fastWindow (Mult.Sizes.p n) (Mult.Sizes.alpha n))
    (fun ℓ h => (Resampling.WeightTable.tableE (Mult.Sizes.s n i) (Mult.Sizes.t n i)
      (Mult.Sizes.alpha n) (Mult.Sizes.p n) ℓ h : ℝ) / 2 ^ Mult.Sizes.p n)
    (fun ℓ => (Resampling.WeightTable.tableD (Mult.Sizes.s n i) (Mult.Sizes.t n i)
      (Mult.Sizes.alpha n) (Mult.Sizes.p n) ℓ : ℝ) / 2 ^ Mult.Sizes.p n)

/-- The axis data of `lineB n` on axis `i`: source length `s n i`, target width `Lb i`, the
weight tables `tableE`, `tableD`, the interchange headers `hs i`. -/
def rsbLineBData (n : ℕ) (Lb : Fin (Mult.Sizes.d n) → ℕ)
    (hs : Fin (Mult.Sizes.d n) → Fin 5 → List Bool) (i : Fin (Mult.Sizes.d n)) : RsbAxisData :=
  ⟨Mult.Sizes.s n i, Lb i,
    Resampling.WeightTable.tableE (Mult.Sizes.s n i) (Mult.Sizes.t n i) (Mult.Sizes.alpha n)
      (Mult.Sizes.p n),
    Resampling.WeightTable.tableD (Mult.Sizes.s n i) (Mult.Sizes.t n i) (Mult.Sizes.alpha n)
      (Mult.Sizes.p n), hs i⟩

instance rsbLineBData_neZero (n : ℕ) (Lb : Fin (Mult.Sizes.d n) → ℕ)
    (hs : Fin (Mult.Sizes.d n) → Fin 5 → List Bool) (i : Fin (Mult.Sizes.d n)) :
    NeZero (rsbLineBData n Lb hs i).s :=
  Mult.Pipeline.neZero_s n i

/-- The numeric maps of the machine's axis data are `lineB n`. -/
theorem rsb_lineB_eq (n : ℕ) (Lb : Fin (Mult.Sizes.d n) → ℕ)
    (hs : Fin (Mult.Sizes.d n) → Fin 5 → List Bool) :
    (fun i => Mult.FastB0.resampB₀NumK (t := Mult.Sizes.t n i) (Mult.Sizes.p n)
      (Mult.Sizes.alpha n ^ 2) (Mult.FastB0.fastWindow (Mult.Sizes.p n) (Mult.Sizes.alpha n))
      (fun ℓ h => ((rsbLineBData n Lb hs i).E ℓ h : ℝ) / 2 ^ Mult.Sizes.p n)
      (fun ℓ => ((rsbLineBData n Lb hs i).D ℓ : ℝ) / 2 ^ Mult.Sizes.p n)) =
      lineBN n := rfl

section Machine

variable {t₀ T Q K : ℕ} {U F : Type}
variable {body : F → Pr F T Q (prime + K) U} {rg : RsbR → Fin T} {rgx : RsbX t₀ → Fin T}
  {ι : Fin 64 → Fin T}

set_option maxHeartbeats 4000000 in
/-- **`B̃₀` of the pipeline along all axes of the padded box, exactly.** `rsb_all_tensor` for the
axis data `rsbLineBData n Lb hs` (the weight tables `tableE`, `tableD`, `α²` Horner steps, window
`fastWindow (p n) α`): the machine turns the padded stream `rsbBox (d n) (t n) F` of the numerators
of `u` at scale `2^(p n)` into the padded stream `rsbBox (d n) (t n) G` of the numerators of
`tensorZR (d n) (t n) (s n) (lineB n) u`, with zeros at the addresses with some `x i ≥ s n i`. -/
theorem rsb_all_lineB (n : ℕ) (Lb : Fin (Mult.Sizes.d n) → ℕ)
    (hs : Fin (Mult.Sizes.d n) → Fin 5 → List Bool) (prep : Pr F T Q (prime + K) U)
    (hrg₂ : Function.Injective (Sum.elim rg rgx)) (hdisj₂ : ∀ r j, Sum.elim rg rgx r ≠ ι j)
    (hι : Function.Injective ι) (hT : 64 ≤ T) (hQ : SS.states ≤ Q) (hA : 96 ≤ prime + K)
    (hd : Fin 5 → Fin t₀) (pay : Fin t₀) (hi : Function.Injective hd)
    (hQs : swapStates hd pay hi ≤ Q) (hsw : Function.Injective fun j => rgx (.sw j))
    (hTs : swapT t₀ ≤ T) (hdpay : ∀ k, hd k ≠ pay)
    (hd0 : 0 < Mult.Sizes.d n) {w : ℕ} (hp1 : 1 ≤ Mult.Sizes.p n) (hpw : Mult.Sizes.p n < w)
    (hDt : ∀ i, Mult.Sizes.t n i = 2 ^ Lb i ∧ Mult.Sizes.s n i < Mult.Sizes.t n i ∧
      Mult.FastB0.fastWindow (Mult.Sizes.p n) (Mult.Sizes.alpha n) ≤ Mult.Sizes.s n i ∧
      0 < Mult.Sizes.s n i ∧
      (∀ ℓ, ∀ h ∈ rsbHs (Mult.FastB0.fastWindow (Mult.Sizes.p n) (Mult.Sizes.alpha n)),
        Fits w (rsbReal ((rsbLineBData n Lb hs i).E ℓ h))) ∧
      ∀ ℓ, Fits w (rsbReal ((rsbLineBData n Lb hs i).D ℓ)))
    (hDw : ∀ i : Fin (Mult.Sizes.d n), (i : ℕ) + 1 < Mult.Sizes.d n →
      Lb i ≤ Lb (rsbAx hd0 0) + 1 ∧ Lb (rsbAx hd0 0) ≤ Lb i + 1 ∧
      (∀ k, Counter.value (hs i k) = BinaryInterchangeRun.values (rsbPre (Mult.Sizes.t n) i)
        (rsbMid (Mult.Sizes.t n) i) (3 * w) (Lb i) (Lb (rsbAx hd0 0)) k) ∧
      ∀ k, GrowingCounterData.Canonical (hs i k))
    (V₀ : RsbR ⊕ RsbX t₀ → List (Fin (prime + K + 4)))
    (cfg : ℕ → RsbR ⊕ RsbX t₀ → List (Fin (prime + K + 4)))
    (hcfg : ∀ k < Mult.Sizes.d n, RsbAxisCfg (fun r => cfg k (.inl r)) w (Mult.Sizes.p n)
        (Mult.Sizes.s n (rsbAx hd0 k)) (Mult.Sizes.t n (rsbAx hd0 k))
        (Mult.FastB0.fastWindow (Mult.Sizes.p n) (Mult.Sizes.alpha n)) (Mult.Sizes.alpha n ^ 2)
        (rsbLineBData n Lb hs (rsbAx hd0 k)).E (rsbLineBData n Lb hs (rsbAx hd0 k)).D ∧
      (0 < k → (∀ j, cfg k (.inr (.sw j)) = rsbBank hd (hs (rsbAx hd0 k)) j) ∧
        cfg k (.inr .xt) = [] ∧ cfg k (.inr .e1) = [] ∧ cfg k (.inr .e2) = []))
    (cp : ℕ → ℕ)
    (hprep₀ : ∀ l a a', RsbRuns body (Sum.elim rg rgx) ι prep (rsbWith V₀ l a a')
      (rsbWith (cfg 0) l a a') (cp 0))
    (hprep : ∀ k, k + 1 < Mult.Sizes.d n → ∀ l a a', RsbRuns body (Sum.elim rg rgx) ι prep
      (rsbWith (cfg k) l a a') (rsbWith (cfg (k + 1)) l a a') (cp (k + 1)))
    (u : ((i : Fin (Mult.Sizes.d n)) → ZMod (Mult.Sizes.t n i)) → ℂ)
    (Fn : ((i : Fin (Mult.Sizes.d n)) → Fin (Mult.Sizes.t n i)) → GaussianInt)
    (hF : ∀ x : (i : Fin (Mult.Sizes.d n)) → Fin (Mult.Sizes.t n i),
      u (fun i => ((x i : ℕ) : ZMod (Mult.Sizes.t n i))) =
        GaussianInt.toComplex (Fn x) / 2 ^ Mult.Sizes.p n)
    (hok : ∀ i : Fin (Mult.Sizes.d n), ∀ p' < rsbPre (Mult.Sizes.t n) i,
      ∀ q < rsbSuf (Mult.Sizes.t n) i,
      RsbLineOk (Mult.Sizes.s n i) (Mult.Sizes.t n i) w (Mult.Sizes.p n) (Mult.Sizes.alpha n ^ 2)
        (Mult.FastB0.fastWindow (Mult.Sizes.p n) (Mult.Sizes.alpha n))
        (rsbLineBData n Lb hs i).E
        (rsbLineAt (Mult.Sizes.t n i) (rsbSuf (Mult.Sizes.t n) i)
          (rsbFlat (Mult.Sizes.d n) (Mult.Sizes.t n)
            (fun i => (rsbLineBData n Lb hs i).g (Mult.Sizes.p n) (Mult.Sizes.alpha n ^ 2)
              (Mult.FastB0.fastWindow (Mult.Sizes.p n) (Mult.Sizes.alpha n)) (Mult.Sizes.t n i))
            (i + 1) (rsbBox (Mult.Sizes.d n) (Mult.Sizes.t n) Fn)) p' q))
    (axs : List (Fin (prime + K + 4))) (haxs : axs.length = Mult.Sizes.d n - 1) :
    ∃ G : ((i : Fin (Mult.Sizes.d n)) → Fin (Mult.Sizes.t n i)) → GaussianInt,
      (∀ x : (i : Fin (Mult.Sizes.d n)) → Fin (Mult.Sizes.t n i),
        (∀ i, (x i : ℕ) < Mult.Sizes.s n i) →
        tensorZR (Mult.Sizes.d n) (Mult.Sizes.t n) (Mult.Sizes.s n) (lineBN n) u
          (fun i => ((x i : ℕ) : ZMod (Mult.Sizes.s n i))) =
          GaussianInt.toComplex (G x) / 2 ^ Mult.Sizes.p n) ∧
      (∀ x : (i : Fin (Mult.Sizes.d n)) → Fin (Mult.Sizes.t n i),
        (∃ i, Mult.Sizes.s n i ≤ x i) → G x = 0) ∧
      RsbRuns body (Sum.elim rg rgx) ι (rsbAllP prep rg rgx hι hT hQ hd pay hi hQs hsw hTs)
        (rsbWith V₀ (cstream (prime + K) w (rsbBox (Mult.Sizes.d n) (Mult.Sizes.t n) Fn)) axs [])
        (rsbWith (cfg (Mult.Sizes.d n - 1))
          (cstream (prime + K) w (rsbBox (Mult.Sizes.d n) (Mult.Sizes.t n) G)) axs [])
        (rsbAllCost T t₀ w (Mult.FastB0.fastWindow (Mult.Sizes.p n) (Mult.Sizes.alpha n))
          (Mult.Sizes.alpha n ^ 2) (Mult.Sizes.d n) (Mult.Sizes.t n) hd0 (rsbLineBData n Lb hs)
          (prime + K) hd cp (∏ i, Mult.Sizes.t n i)) :=
  rsb_all_tensor (body := body) prep hrg₂ hdisj₂ hι hT hQ hA hd pay hi hQs hsw hTs hdpay hd0
    (Mult.Sizes.t n) hp1 hpw (rsbLineBData n Lb hs) hDt hDw V₀ cfg hcfg cp hprep₀ hprep u Fn hF
    hok axs haxs

end Machine

/-! ### Admissibility in the regime of the pipeline -/

section Regime

open Mult.Sizes Mult.FastB0 IntegerMultBounds.Resampling.WeightTable
open IntegerMultBounds.Resampling.OffDiagSum (offTermW)

/-- The off-diagonal weights are at most one: `exp (normExp …) ≤ 1` for `h ≠ 0`. -/
lemma rsb_exp_normExp_le_one {s t : ℕ} [NeZero s] (hst : s < t) (α : ℝ) (ℓ : ZMod s) {h : ℤ}
    (hh : h ≠ 0) : Real.exp (normExp s t α ℓ.val h) ≤ 1 := by
  rw [Real.exp_le_one_iff]
  have hx := exponent_ge_full s t hst (beta s t ℓ.val) (beta s t (ℓ.val + h))
    (abs_beta_le s t _) (abs_beta_le s t _) h hh
  have hs : (0 : ℝ) < s := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne s)
  have hθ : 0 ≤ (t : ℝ) / s - 1 := by
    rw [sub_nonneg, le_div_iff₀ hs, one_mul]; exact_mod_cast hst.le
  have h1 : (1 : ℝ) ≤ |(h : ℝ)| := by
    have := Int.one_le_abs hh; exact_mod_cast this
  have h2 : (1 / 4 : ℝ) ≤ (|(h : ℝ)| - 1 / 2) ^ 2 := by nlinarith
  have h3 : 0 ≤ ((t : ℝ) * h / s + beta s t ℓ.val) ^ 2 - beta s t (ℓ.val + h) ^ 2 := by
    have : 0 ≤ 2 * ((t : ℝ) / s - 1) * (|(h : ℝ)| - 1 / 2) ^ 2 := by positivity
    linarith
  unfold normExp
  have hπ : 0 ≤ Real.pi * α ^ 2 := by positivity
  nlinarith [mul_nonneg hπ h3]

variable (n : ℕ) (h : Big n) (i : Fin (d n))
include h

lemma rsb_regime :
    s n i < t n i ∧ (0 : ℝ) < alpha n ∧
      1 ≤ (alpha n : ℝ) ^ 2 * ((t n i : ℝ) / s n i - 1) ∧
      (p n : ℝ) ≤ 4 * (alpha n : ℝ) ^ 2 * (fastWindow (p n) (alpha n) : ℝ) ^ 2 ∧
      13 ≤ p n ∧ 3 * fastWindow (p n) (alpha n) ≤ p n := by
  obtain ⟨-, hm, hmp, hp⟩ := fastB0_conditions h i
  have ha := two_le_alpha h.1
  exact ⟨(h.good).lt i, by exact_mod_cast (by omega : 0 < alpha n),
    h.one_le_alpha_sq_theta i, hm, hp, hmp⟩

/-- The weight table `tableE` within two units at scale `2^p`. -/
lemma rsb_hef : ∀ ℓ k, 2 ^ p n *
    ‖rhoC (p n) ((((tableE (s n i) (t n i) (alpha n) (p n) ℓ k : ℤ) : ℝ) /
      2 ^ p n : ℝ) : ℂ) - (Real.exp (normExp (s n i) (t n i) (alpha n) ℓ.val k) : ℂ)‖ ≤ 2 := by
  obtain ⟨hst, -, -, -, hp, -⟩ := rsb_regime n h i
  intro ℓ k
  exact IntegerMultBounds.Resampling.TabledMaps.tol_of_int (p n) _ _
    (tableE_err (s n i) (t n i) (alpha n) (p n) hst hp ℓ k)

/-- The entries of `tableE` in the window fit `w ≥ p + 2` bits. -/
lemma rsb_fitsE {w : ℕ} (hw : p n + 2 ≤ w) :
    ∀ ℓ, ∀ k ∈ rsbHs (fastWindow (p n) (alpha n)),
      Fits w (rsbReal (tableE (s n i) (t n i) (alpha n) (p n) ℓ k)) := by
  obtain ⟨hst, -, -, -, hp, -⟩ := rsb_regime n h i
  intro ℓ k hk
  have hk0 : k ≠ 0 := (mem_rsbHs.mp hk).1
  have he := tableE_err (s n i) (t n i) (alpha n) (p n) hst hp ℓ k
  have hx1 := rsb_exp_normExp_le_one hst (alpha n : ℝ) ℓ hk0
  have hx0 := Real.exp_pos (normExp (s n i) (t n i) (alpha n) ℓ.val k)
  have hP : (0 : ℝ) < 2 ^ p n := by positivity
  have hlt : (2 : ℝ) ^ p n + 2 < 2 ^ (w - 1) := by
    have h4 : (4 : ℝ) ≤ 2 ^ p n := by
      calc (4 : ℝ) = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ p n := pow_le_pow_right₀ (by norm_num) (by omega)
    have h5 : (2 : ℝ) ^ (p n + 1) ≤ 2 ^ (w - 1) := pow_le_pow_right₀ (by norm_num) (by omega)
    rw [pow_succ] at h5
    linarith
  refine ⟨?_, by simp [rsbReal]⟩
  simp only [rsbReal]
  have hb : |(tableE (s n i) (t n i) (alpha n) (p n) ℓ k : ℝ)| < 2 ^ (w - 1) := by
    rw [abs_le] at he
    rw [abs_lt]
    constructor <;> nlinarith
  exact_mod_cast hb

/-- The entries of `tableD` fit `w ≥ p + 2` bits, and their rounded values have norm at most
one. -/
lemma rsb_fitsD {w : ℕ} (hw : p n + 2 ≤ w) (ℓ : ZMod (s n i)) :
    Fits w (rsbReal (tableD (s n i) (t n i) (alpha n) (p n) ℓ)) ∧
      0 ≤ tableD (s n i) (t n i) (alpha n) (p n) ℓ ∧
      tableD (s n i) (t n i) (alpha n) (p n) ℓ ≤ 2 ^ p n := by
  obtain ⟨-, -, -, -, hp, -⟩ := rsb_regime n h i
  have ha := two_le_alpha h.1
  obtain ⟨-, h0, h1⟩ := tableD_spec (s n i) (t n i) (alpha n) (p n) hp (by omega)
    h.alpha_sq_le_p ℓ
  refine ⟨⟨?_, by simp [rsbReal]⟩, h0, h1⟩
  simp only [rsbReal]
  rw [abs_of_nonneg h0]
  calc tableD (s n i) (t n i) (alpha n) (p n) ℓ ≤ 2 ^ p n := h1
    _ < 2 ^ (w - 1) := pow_lt_pow_right₀ (by norm_num) (by omega)

end Regime

/-! ### Lines in the unit disk -/

section Disk

open Mult.Sizes Mult.FastB0 IntegerMultBounds.Resampling.WeightTable
open IntegerMultBounds.Resampling.OffDiagSum (offTermW)
open IntegerMultBounds.Resampling.TabledMaps (diagW)

variable (n : ℕ) (h : Big n) (i : Fin (d n))
include h

omit h in
/-- The grid line of `rsbVec L`, for a line `L` whose entries have norm at most one. -/
lemma rsb_vec_ball {q : ℕ} (L : List GaussianInt) (hL : ∀ x ∈ L, ‖rsbGrid q x‖ ≤ 1) :
    ∀ j : ZMod (t n i), ‖rsbGrid q (rsbVec (t := t n i) L j)‖ ≤ 1 := by
  intro j
  simp only [rsbVec]
  by_cases hj : j.val < L.length
  · rw [List.getD_eq_getElem _ _ hj]; exact hL _ (List.getElem_mem hj)
  · rw [List.getD_eq_default _ _ (by omega)]; simp [rsbGrid]

/-- **Admissible lines in the pipeline.** Every line of `t n i` records in the unit disk is
admissible for the line machine of axis `i` at width `w ≥ p n + 2`, for any number of Horner
steps. -/
theorem rsb_pipe_lineOk {w K : ℕ} (hw : p n + 2 ≤ w) (L : List GaussianInt) (hL : L.length = t n i)
    (hLn : ∀ x ∈ L, ‖rsbGrid (p n) x‖ ≤ 1) :
    RsbLineOk (s n i) (t n i) w (p n) K (fastWindow (p n) (alpha n))
      (tableE (s n i) (t n i) (alpha n) (p n)) L := by
  obtain ⟨hst, hα, hθ, hm, hp, hmp⟩ := rsb_regime n h i
  have hvb := rsb_vec_ball n i L hLn
  refine rsbLineOk_of_ball hw _ L hL hvb (fun k _ => ?_)
  exact rsb_iter_ball hst hα hθ hm hp hmp _ (rsb_hef n h i) _
    ((pi_norm_le_iff_of_nonneg zero_le_one).2 hvb) k

/-- **`B̃₀` keeps the unit disk.** The outputs of the line map of axis `i` on a line of
`t n i` records in the unit disk are in the unit disk. -/
theorem rsb_pipe_lineG_ball {K : ℕ} (L : List GaussianInt) (hLn : ∀ x ∈ L, ‖rsbGrid (p n) x‖ ≤ 1) :
    ∀ x ∈ rsbLineG (s n i) (t n i) (p n) K (fastWindow (p n) (alpha n))
      (tableE (s n i) (t n i) (alpha n) (p n)) (tableD (s n i) (t n i) (alpha n) (p n)) L,
      ‖rsbGrid (p n) x‖ ≤ 1 := by
  obtain ⟨hst, hα, hθ, hm, hp, hmp⟩ := rsb_regime n h i
  have hvb := rsb_vec_ball n i L hLn
  intro x hx
  rw [rsbLineG, List.mem_append] at hx
  rcases hx with hx | hx
  · simp only [rsbArr, List.mem_map, List.mem_range] at hx
    obtain ⟨ℓ, -, rfl⟩ := hx
    have e := congrFun (rsb_resampB₀NumK (p n) K (fastWindow (p n) (alpha n))
      (tableE (s n i) (t n i) (alpha n) (p n)) (tableD (s n i) (t n i) (alpha n) (p n))
      (rsbVec (t := t n i) L)) (ℓ : ZMod (s n i))
    rw [← e]
    unfold resampB₀NumK diagW
    refine (norm_rhoC_le _ _).trans ?_
    rw [norm_mul]
    have hD : ‖rhoC (p n) ((((tableD (s n i) (t n i) (alpha n) (p n) (ℓ : ZMod (s n i)) : ℤ) :
        ℝ) / 2 ^ p n : ℝ) : ℂ)‖ ≤ 1 := by
      have hP : (0 : ℝ) < 2 ^ p n := by positivity
      obtain ⟨-, h0, h1⟩ := rsb_fitsD n h i (w := p n + 2) le_rfl (ℓ : ZMod (s n i))
      rw [Resampling.WindowSum.rhoC_real, mul_div_cancel₀ _ hP.ne',
        Resampling.NeumannWords.rho0_int, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (div_nonneg (by exact_mod_cast h0) hP.le), div_le_one hP]
      exact_mod_cast h1
    have hy := rsb_iter_ball hst hα hθ hm hp hmp _ (rsb_hef n h i) _
      ((pi_norm_le_iff_of_nonneg zero_le_one).2 hvb) K
    calc _ ≤ 1 * 1 := mul_le_mul hD ((norm_le_pi_norm _ _).trans hy) (norm_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  · rw [List.mem_replicate] at hx
    rw [hx.2]; simp [rsbGrid]

end Disk

/-! ### Entries of box streams -/

section Entries

lemma rsb_mem_rsbBox {α : Type} : ∀ (d : ℕ) (t : Fin d → ℕ) (F : ((i : Fin d) → Fin (t i)) → α)
    {y : α}, y ∈ rsbBox d t F → ∃ a, F a = y
  | 0, _, F, y, hy => by
      simp only [rsbBox, List.mem_singleton] at hy
      exact ⟨_, hy.symm⟩
  | d + 1, t, F, y, hy => by
      simp only [rsbBox, List.mem_flatMap, List.mem_finRange, true_and] at hy
      obtain ⟨x₀, hx₀⟩ := hy
      obtain ⟨a, ha⟩ := rsb_mem_rsbBox d _ _ hx₀
      exact ⟨_, ha⟩

lemma rsb_mem_rsbLineAt {H Q : ℕ} {L : List GaussianInt} {p q : ℕ} {y : GaussianInt}
    (hy : y ∈ rsbLineAt H Q L p q) : y = 0 ∨ y ∈ L := by
  simp only [rsbLineAt, List.mem_map, List.mem_range] at hy
  obtain ⟨h, -, rfl⟩ := hy
  rw [List.getD_eq_getElem?_getD]
  cases hh : L[(p * H + h) * Q + q]? with
  | none => left; rfl
  | some a => right; exact List.mem_of_getElem? hh

lemma rsb_mem_getD {L : List GaussianInt} {k : ℕ} : L.getD k 0 = 0 ∨ L.getD k 0 ∈ L := by
  rw [List.getD_eq_getElem?_getD]
  cases hh : L[k]? with
  | none => left; rfl
  | some a => right; exact List.mem_of_getElem? hh

/-- An entry of a line map is an entry of the image of a line, or zero. -/
lemma rsb_mem_rsbAxisL {P H Q : ℕ} {g : List GaussianInt → List GaussianInt}
    {l : List GaussianInt} {x : GaussianInt} (hx : x ∈ rsbAxisL P H Q g l) :
    x = 0 ∨ ∃ L', L'.length = H ∧ (∀ y ∈ L', y = 0 ∨ y ∈ l) ∧ x ∈ g L' := by
  simp only [rsbAxisL, rsbChunkMap, rsbChunks, List.mem_flatMap, List.mem_map,
    List.mem_range] at hx
  obtain ⟨b, ⟨c, -, rfl⟩, hxb⟩ := hx
  simp only [rsbBlockOp, List.mem_map, List.mem_range] at hxb
  obtain ⟨z, -, rfl⟩ := hxb
  rcases rsb_mem_getD (L := g ((List.range H).map fun h =>
      ((l.drop (c * (H * Q))).take (H * Q)).getD (h * Q + z % Q) 0)) (k := z / Q) with h0 | h1
  · exact Or.inl h0
  · refine Or.inr ⟨_, by simp, fun y hy => ?_, h1⟩
    simp only [List.mem_map, List.mem_range] at hy
    obtain ⟨h, -, rfl⟩ := hy
    rcases rsb_mem_getD (L := (l.drop (c * (H * Q))).take (H * Q)) (k := h * Q + z % Q) with
      e | e
    · exact Or.inl e
    · exact Or.inr (List.mem_of_mem_drop (List.mem_of_mem_take e))

/-- A property of the entries kept by every line map is kept along all axes. -/
lemma rsb_flat_mem {d : ℕ} (t : Fin d → ℕ) (g : Fin d → List GaussianInt → List GaussianInt)
    (P : GaussianInt → Prop) (h0 : P 0)
    (hg : ∀ i L, L.length = t i → (∀ y ∈ L, P y) → ∀ x ∈ g i L, P x)
    (l : List GaussianInt) (hl : ∀ x ∈ l, P x) : ∀ k, ∀ x ∈ rsbFlat d t g k l, P x := by
  intro k
  rw [rsbFlat]
  induction ((List.finRange d).drop k) with
  | nil => exact hl
  | cons j js ih =>
      intro x hx
      rw [List.foldr_cons, rsbAxisOp] at hx
      rcases rsb_mem_rsbAxisL hx with e | ⟨L', hL', hy, hx'⟩
      · rw [e]; exact h0
      · exact hg j L' hL' (fun y hyL => (hy y hyL).elim (fun e => e ▸ h0) (ih y)) x hx'

end Entries

section MachineDisk

variable {t₀ T Q K : ℕ} {U F : Type}
variable {body : F → Pr F T Q (prime + K) U} {rg : RsbR → Fin T} {rgx : RsbX t₀ → Fin T}
  {ι : Fin 64 → Fin T}

set_option maxHeartbeats 4000000 in
/-- **`B̃₀` of the pipeline along all axes, for inputs in the unit disk.** `rsb_all_lineB` in the
regime `Big n` at width `w ≥ p n + 2`, with every entry of the input array `u` of norm at most one:
the fit conditions on the weight tables and on all lines of the intermediate boxes hold. -/
theorem rsb_all_lineB_disk (n : ℕ) (hbig : Mult.Sizes.Big n) (Lb : Fin (Mult.Sizes.d n) → ℕ)
    (hs : Fin (Mult.Sizes.d n) → Fin 5 → List Bool) (prep : Pr F T Q (prime + K) U)
    (hrg₂ : Function.Injective (Sum.elim rg rgx)) (hdisj₂ : ∀ r j, Sum.elim rg rgx r ≠ ι j)
    (hι : Function.Injective ι) (hT : 64 ≤ T) (hQ : SS.states ≤ Q) (hA : 96 ≤ prime + K)
    (hd : Fin 5 → Fin t₀) (pay : Fin t₀) (hi : Function.Injective hd)
    (hQs : swapStates hd pay hi ≤ Q) (hsw : Function.Injective fun j => rgx (.sw j))
    (hTs : swapT t₀ ≤ T) (hdpay : ∀ k, hd k ≠ pay)
    (hd0 : 0 < Mult.Sizes.d n) {w : ℕ} (hw : Mult.Sizes.p n + 2 ≤ w)
    (hLb : ∀ i, Mult.Sizes.t n i = 2 ^ Lb i)
    (hms : ∀ i, Mult.FastB0.fastWindow (Mult.Sizes.p n) (Mult.Sizes.alpha n) ≤ Mult.Sizes.s n i)
    (hDw : ∀ i : Fin (Mult.Sizes.d n), (i : ℕ) + 1 < Mult.Sizes.d n →
      Lb i ≤ Lb (rsbAx hd0 0) + 1 ∧ Lb (rsbAx hd0 0) ≤ Lb i + 1 ∧
      (∀ k, Counter.value (hs i k) = BinaryInterchangeRun.values (rsbPre (Mult.Sizes.t n) i)
        (rsbMid (Mult.Sizes.t n) i) (3 * w) (Lb i) (Lb (rsbAx hd0 0)) k) ∧
      ∀ k, GrowingCounterData.Canonical (hs i k))
    (V₀ : RsbR ⊕ RsbX t₀ → List (Fin (prime + K + 4)))
    (cfg : ℕ → RsbR ⊕ RsbX t₀ → List (Fin (prime + K + 4)))
    (hcfg : ∀ k < Mult.Sizes.d n, RsbAxisCfg (fun r => cfg k (.inl r)) w (Mult.Sizes.p n)
        (Mult.Sizes.s n (rsbAx hd0 k)) (Mult.Sizes.t n (rsbAx hd0 k))
        (Mult.FastB0.fastWindow (Mult.Sizes.p n) (Mult.Sizes.alpha n)) (Mult.Sizes.alpha n ^ 2)
        (rsbLineBData n Lb hs (rsbAx hd0 k)).E (rsbLineBData n Lb hs (rsbAx hd0 k)).D ∧
      (0 < k → (∀ j, cfg k (.inr (.sw j)) = rsbBank hd (hs (rsbAx hd0 k)) j) ∧
        cfg k (.inr .xt) = [] ∧ cfg k (.inr .e1) = [] ∧ cfg k (.inr .e2) = []))
    (cp : ℕ → ℕ)
    (hprep₀ : ∀ l a a', RsbRuns body (Sum.elim rg rgx) ι prep (rsbWith V₀ l a a')
      (rsbWith (cfg 0) l a a') (cp 0))
    (hprep : ∀ k, k + 1 < Mult.Sizes.d n → ∀ l a a', RsbRuns body (Sum.elim rg rgx) ι prep
      (rsbWith (cfg k) l a a') (rsbWith (cfg (k + 1)) l a a') (cp (k + 1)))
    (u : ((i : Fin (Mult.Sizes.d n)) → ZMod (Mult.Sizes.t n i)) → ℂ)
    (Fn : ((i : Fin (Mult.Sizes.d n)) → Fin (Mult.Sizes.t n i)) → GaussianInt)
    (hF : ∀ x : (i : Fin (Mult.Sizes.d n)) → Fin (Mult.Sizes.t n i),
      u (fun i => ((x i : ℕ) : ZMod (Mult.Sizes.t n i))) =
        GaussianInt.toComplex (Fn x) / 2 ^ Mult.Sizes.p n)
    (hu : ∀ x : (i : Fin (Mult.Sizes.d n)) → Fin (Mult.Sizes.t n i),
      ‖u (fun i => ((x i : ℕ) : ZMod (Mult.Sizes.t n i)))‖ ≤ 1)
    (axs : List (Fin (prime + K + 4))) (haxs : axs.length = Mult.Sizes.d n - 1) :
    ∃ G : ((i : Fin (Mult.Sizes.d n)) → Fin (Mult.Sizes.t n i)) → GaussianInt,
      (∀ x : (i : Fin (Mult.Sizes.d n)) → Fin (Mult.Sizes.t n i),
        (∀ i, (x i : ℕ) < Mult.Sizes.s n i) →
        tensorZR (Mult.Sizes.d n) (Mult.Sizes.t n) (Mult.Sizes.s n) (lineBN n) u
          (fun i => ((x i : ℕ) : ZMod (Mult.Sizes.s n i))) =
          GaussianInt.toComplex (G x) / 2 ^ Mult.Sizes.p n) ∧
      (∀ x : (i : Fin (Mult.Sizes.d n)) → Fin (Mult.Sizes.t n i),
        (∃ i, Mult.Sizes.s n i ≤ x i) → G x = 0) ∧
      RsbRuns body (Sum.elim rg rgx) ι (rsbAllP prep rg rgx hι hT hQ hd pay hi hQs hsw hTs)
        (rsbWith V₀ (cstream (prime + K) w (rsbBox (Mult.Sizes.d n) (Mult.Sizes.t n) Fn)) axs [])
        (rsbWith (cfg (Mult.Sizes.d n - 1))
          (cstream (prime + K) w (rsbBox (Mult.Sizes.d n) (Mult.Sizes.t n) G)) axs [])
        (rsbAllCost T t₀ w (Mult.FastB0.fastWindow (Mult.Sizes.p n) (Mult.Sizes.alpha n))
          (Mult.Sizes.alpha n ^ 2) (Mult.Sizes.d n) (Mult.Sizes.t n) hd0 (rsbLineBData n Lb hs)
          (prime + K) hd cp (∏ i, Mult.Sizes.t n i)) := by
  have hp13 := hbig.thirteen_le_p
  have hbox : ∀ y ∈ rsbBox (Mult.Sizes.d n) (Mult.Sizes.t n) Fn,
      ‖rsbGrid (Mult.Sizes.p n) y‖ ≤ 1 := by
    intro y hy
    obtain ⟨a, rfl⟩ := rsb_mem_rsbBox _ _ _ hy
    rw [rsbGrid, ← hF a]
    exact hu a
  have hflat := rsb_flat_mem (Mult.Sizes.t n)
    (fun i => (rsbLineBData n Lb hs i).g (Mult.Sizes.p n) (Mult.Sizes.alpha n ^ 2)
      (Mult.FastB0.fastWindow (Mult.Sizes.p n) (Mult.Sizes.alpha n)) (Mult.Sizes.t n i))
    (fun y => ‖rsbGrid (Mult.Sizes.p n) y‖ ≤ 1) (by simp [rsbGrid])
    (fun i L _ hL => rsb_pipe_lineG_ball n hbig i L hL) _ hbox
  refine rsb_all_lineB n Lb hs prep hrg₂ hdisj₂ hι hT hQ hA hd pay hi hQs hsw hTs hdpay hd0
    (by omega) (by omega)
    (fun i => ⟨hLb i, (hbig.good).lt i, hms i, (hbig.good.odd i).pos, rsb_fitsE n hbig i hw,
      fun ℓ => (rsb_fitsD n hbig i hw ℓ).1⟩) hDw V₀ cfg hcfg cp hprep₀ hprep u Fn hF
    (fun i p' _ q _ => rsb_pipe_lineOk n hbig i hw _ (length_rsbLineAt _ _ _ _ _)
      (fun y hy => (rsb_mem_rsbLineAt hy).elim (fun e => by rw [e]; simp [rsbGrid])
        (fun hy' => hflat _ y hy'))) axs haxs

end MachineDisk

end

end IntegerMultBounds.MathlibTM2.Fast
