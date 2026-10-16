module

public import IntegerMultBounds.MathlibTM2.Fast.BandPrep
public import IntegerMultBounds.MathlibTM2.Fast.BandFits

/-!
# The banded `B̃₀` stage

The loader `bandPreB` never reads the box register `src` (it parks it and puts it back) or the
axis counters `ax`, `ax'`, so it commutes with `rsbWith` (`bandLoad_rsbWith`) and its step bound
ignores them (`bandPreCost_rsbWith`): the contract `hprep` of the generic driver
`rsb_allG_tensor`.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Fast

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.Resampling.WeightTable (tableE tableD)
open IntegerMultBounds.Networks.Shared50ModularControl (prime)

set_option linter.unusedSimpArgs false

noncomputable section

variable {t₀ A K : ℕ}

/-! ### Agreement off the box and axis registers -/

section Agree

/-- Two register files agree off `src`, `ax`, `ax'`. -/
def AgreeOff (σ τ : RsbR ⊕ RsbX t₀ → List (Fin (A + 4))) : Prop :=
  ∀ x, x ≠ .inl .src → x ≠ .inr .ax → x ≠ .inr .ax' → σ x = τ x

variable {σ τ : RsbR ⊕ RsbX t₀ → List (Fin (A + 4))}

lemma AgreeOff.upd (h : AgreeOff σ τ) (x : RsbR ⊕ RsbX t₀) {v v' : List (Fin (A + 4))}
    (hv : x ≠ .inl .src → x ≠ .inr .ax → x ≠ .inr .ax' → v = v') :
    AgreeOff (Function.update σ x v) (Function.update τ x v') := by
  intro y h1 h2 h3
  by_cases hy : y = x
  · subst hy; simp [hv h1 h2 h3]
  · simp [Function.update_of_ne hy, h y h1 h2 h3]

lemma AgreeOff.upd' (h : AgreeOff σ τ) (x : RsbR ⊕ RsbX t₀) (v : List (Fin (A + 4))) :
    AgreeOff (Function.update σ x v) (Function.update τ x v) := h.upd x fun _ _ _ => rfl

lemma AgreeOff.ite (h : AgreeOff σ τ) (L : List (RsbR ⊕ RsbX t₀)) [DecidablePred (· ∈ L)] :
    AgreeOff (fun r => if r ∈ L then [] else σ r) (fun r => if r ∈ L then [] else τ r) :=
  fun y h1 h2 h3 => by simp only [h y h1 h2 h3]

lemma rsbWith_agree (σ : RsbR ⊕ RsbX t₀ → List (Fin (A + 4))) (l a a' : List (Fin (A + 4))) :
    AgreeOff (rsbWith σ l a a') σ := by
  intro y h1 h2 h3
  rcases y with r | x
  · simp only [rsbWith, Sum.elim_inl]
    rw [Function.update_of_ne (fun e => h1 (by rw [e]))]
  · simp only [rsbWith, Sum.elim_inr]
    rw [Function.update_of_ne (fun e => h3 (by rw [e])), Function.update_of_ne (fun e => h2 (by rw [e]))]

lemma agree_preBankB (h : AgreeOff σ τ) (hd : Fin 5 → Fin t₀) (hs : Fin 5 → List Bool) :
    AgreeOff (preBankB σ hd hs) (preBankB τ hd hs) := by
  intro y h1 h2 h3
  rcases y with r | x
  · exact h _ h1 h2 h3
  · cases x <;> simp only [preBankB] <;> (try split_ifs) <;> first | rfl | exact h _ h1 h2 h3

end Agree

section Layers

variable {σ τ : RsbR ⊕ RsbX t₀ → List (Fin (A + 4))}

open Classical in
lemma agree_bandFA (h : AgreeOff σ τ) (hd : Fin 5 → Fin t₀) (w : ℕ) (D : PreAxB)
    (rest : List (Fin (A + 4))) : AgreeOff (bandFA σ hd w D rest) (bandFA τ hd w D rest) := by
  unfold bandFA bandF0
  refine agree_preBankB ?_ hd _
  exact ((((((h.ite _).upd' _ _).upd' _ _).upd' _ _).upd' _ _).upd' _ _).upd' _ _ |>.upd' _ _

lemma agree_bandFF1 (h : AgreeOff σ τ) (D : PreAxB) : AgreeOff (bandFF1 σ D) (bandFF1 τ D) := by
  unfold bandFF1
  exact ((((h.upd' _ _).upd' _ _).upd' _ _).upd' _ _).upd' _ _

lemma agree_bandFF2 (h : AgreeOff σ τ) (D : PreAxB) (w : ℕ) (z : Fin (A + 4)) :
    AgreeOff (bandFF2 σ D w z) (bandFF2 τ D w z) := by
  unfold bandFF2 bandFF2a bandFF2b bandFF2c bandFF2d
  exact ((((((((((h.upd' _ _).upd' _ _).upd' _ _).upd' _ _).upd' _ _).upd' _ _).upd' _ _).upd' _ _).upd'
    _ _).upd' _ _).upd' _ _

lemma agree_bandFB1 (h : AgreeOff σ τ) (hd : Fin 5 → Fin t₀) (w : ℕ) (D : PreAxB) [NeZero D.s]
    (rest : List (Fin (A + 4))) : AgreeOff (bandFB1 σ hd w D rest) (bandFB1 τ hd w D rest) := by
  unfold bandFB1
  refine (agree_bandFF2 (((agree_bandFF1 (agree_bandFA h hd w D rest) D).upd (.inl .src)
    fun h1 _ _ => absurd rfl h1)) D w _).upd' _ _

lemma agree_bandFB2a (h : AgreeOff σ τ) (D : PreAxB) (w : ℕ) :
    AgreeOff (bandFB2a σ D w) (bandFB2a τ D w) := by
  unfold bandFB2a
  exact ((((((h.upd' _ _).upd' _ _).upd' _ _).upd' _ _).upd' _ _).upd' _ _).upd' _ _

lemma agree_bandFB2b {σ τ : RsbR ⊕ RsbX t₀ → List (Fin (prime + K + 4))} (h : AgreeOff σ τ)
    (D : PreAxB) [NeZero D.s] (w : ℕ) : AgreeOff (bandFB2b σ D w) (bandFB2b τ D w) := by
  intro y h1 h2 h3
  simp only [bandFB2b]
  split_ifs
  · rfl
  · exact (h.upd' _ _) y h1 h2 h3

lemma agree_bandFP (h : AgreeOff σ τ) (D : PreAxB) [NeZero D.s] (w : ℕ) (l l' : List (Fin (A + 4))) :
    AgreeOff (bandFP σ D w l) (bandFP τ D w l') := by
  unfold bandFP
  have hv : ∀ r : RsbR, r ≠ .src → σ (.inl r) = τ (.inl r) := fun r hr =>
    h _ (by simpa using hr) (by simp) (by simp)
  have h1 := (((((h.upd (.inl .src) (v := l) (v' := l') fun h1 _ _ => absurd rfl h1).upd' (.inl .bo)
    (cstream A w (((bandLc D.bP D.bK D.bWd D.s (Mult.BandFactor.coefZ D.s D.t D.α D.bP)).map
      colC).flatten))).upd' (.inl .hf) (cstream A w (((bandUc D.bP D.bK D.bWd D.s
        (Mult.BandFactor.coefZ D.s D.t D.α D.bP)).map colC).flatten))).upd' (.inl .df)
      (cstream A w ((bandRcs D.bP D.bK D.bWd D.s
        (Mult.BandFactor.coefZ D.s D.t D.α D.bP)).map fun x => (⟨x, 0⟩ : GaussianInt)))).upd'
      (.inl .dout) []).upd' (.inl .vk) []
  have h2 := ((h1.upd (.inl .m2n) (v := σ (.inl .ms)) (v' := τ (.inl .ms))
    fun _ _ _ => hv .ms (by decide)).upd (.inl .kn) (v := (List.replicate D.s (σ (.inl .ms))).flatten)
      (v' := (List.replicate D.s (τ (.inl .ms))).flatten) fun _ _ _ => by rw [hv .ms (by decide)])
  have h3 := ((h2.upd (.inl .ms) (v := σ (.inl .dst)) (v' := τ (.inl .dst))
    fun _ _ _ => hv .dst (by decide)).upd (.inl .mwn) (v := σ (.inl (.cm .wn)) ++ σ (.inl .m2wn))
      (v' := τ (.inl (.cm .wn)) ++ τ (.inl .m2wn)) fun _ _ _ => by
        rw [hv (.cm .wn) (by decide), hv .m2wn (by decide)])
  exact (h3.upd' (.inl .ef) []).upd' (.inl .xs) []

lemma agree_bandMvF (h : AgreeOff σ τ) (a b : RsbR ⊕ RsbX t₀) (ha1 : a ≠ .inl .src)
    (ha2 : a ≠ .inr .ax) (ha3 : a ≠ .inr .ax') :
    AgreeOff (bandMvF σ a b) (bandMvF τ a b) := by
  unfold bandMvF
  exact (h.upd' _ _).upd _ fun h1 h2 h3 => by
    rw [h a ha1 ha2 ha3, h b h1 h2 h3]

open Classical in
lemma agree_bandFE (h : AgreeOff σ τ) : AgreeOff (bandFE σ) (bandFE τ) := by
  unfold bandFE bandFE0
  refine agree_bandMvF (agree_bandMvF (agree_bandMvF (agree_bandMvF (agree_bandMvF (agree_bandMvF
    (agree_bandMvF (agree_bandMvF (agree_bandMvF (h.ite _) _ _ ?_ ?_ ?_) _ _ ?_ ?_ ?_) _ _ ?_ ?_ ?_)
    _ _ ?_ ?_ ?_) _ _ ?_ ?_ ?_) _ _ ?_ ?_ ?_) _ _ ?_ ?_ ?_) _ _ ?_ ?_ ?_) _ _ ?_ ?_ ?_ <;> simp

lemma agree_bandLoad {σ τ : RsbR ⊕ RsbX t₀ → List (Fin (prime + K + 4))} (h : AgreeOff σ τ)
    (hd : Fin 5 → Fin t₀) (w : ℕ) (D : PreAxB) [NeZero D.s] (rest : List (Fin (prime + K + 4))) :
    AgreeOff (bandLoad σ hd w D rest) (bandLoad τ hd w D rest) :=
  agree_bandFE (agree_bandFP (agree_bandFB2b (agree_bandFB2a (agree_bandFB1 h hd w D rest) D w) D w)
    D w _ _)

end Layers

section Commute

variable {σ τ : RsbR ⊕ RsbX t₀ → List (Fin (prime + K + 4))}

lemma bandLoad_src (σ : RsbR ⊕ RsbX t₀ → List (Fin (prime + K + 4))) (hd : Fin 5 → Fin t₀)
    (w : ℕ) (D : PreAxB) [NeZero D.s] (rest : List (Fin (prime + K + 4))) :
    bandLoad σ hd w D rest (.inl .src) = σ (.inl .src) := by
  simp [bandLoad, bandFE, bandMvF, bandFE0, bandClrE, bandFP, Function.update_apply]

open Classical in
lemma bandLoad_axr (σ : RsbR ⊕ RsbX t₀ → List (Fin (prime + K + 4))) (hd : Fin 5 → Fin t₀)
    (w : ℕ) (D : PreAxB) [NeZero D.s] (rest : List (Fin (prime + K + 4))) (x : RsbX t₀)
    (hx : x = .ax ∨ x = .ax') : bandLoad σ hd w D rest (.inr x) = σ (.inr x) := by
  rcases hx with rfl | rfl <;>
  simp [bandLoad, bandFE, bandMvF, bandFE0, bandClrE, bandFP, bandFB2b, bandScrL, bandFB2a, bandFB1,
    bandFF2, bandFF2a, bandFF2b, bandFF2c, bandFF2d, bandFF1, bandFA, preBankB, bandF0, bandClrB,
    preHB, Function.update_apply]

/-- **The loader commutes with the box and axis registers.** -/
theorem bandLoad_rsbWith (σ : RsbR ⊕ RsbX t₀ → List (Fin (prime + K + 4))) (hd : Fin 5 → Fin t₀)
    (w : ℕ) (D : PreAxB) [NeZero D.s] (rest l a a' : List (Fin (prime + K + 4))) :
    bandLoad (rsbWith σ l a a') hd w D rest = rsbWith (bandLoad σ hd w D rest) l a a' := by
  funext x
  by_cases h1 : x = .inl .src
  · subst h1
    rw [bandLoad_src]; simp [rsbWith]
  by_cases h2 : x = .inr .ax
  · subst h2
    rw [bandLoad_axr _ _ _ _ _ _ (Or.inl rfl)]; simp [rsbWith]
  by_cases h3 : x = .inr .ax'
  · subst h3
    rw [bandLoad_axr _ _ _ _ _ _ (Or.inr rfl)]; simp [rsbWith]
  rw [agree_bandLoad (rsbWith_agree σ l a a') hd w D rest x h1 h2 h3,
    rsbWith_agree (bandLoad σ hd w D rest) l a a' x h1 h2 h3]

lemma costs_agree (h : AgreeOff σ τ) (L : List (RsbR ⊕ RsbX t₀))
    (hL : ∀ x ∈ L, x ≠ .inl .src ∧ x ≠ .inr .ax ∧ x ≠ .inr .ax') :
    (L.map fun r => 2 * (σ r).length + 2) = L.map fun r => 2 * (τ r).length + 2 :=
  List.map_congr_left fun x hx => by
    obtain ⟨a, b, c⟩ := hL x hx
    rw [h x a b c]

/-- The step bound of the loader ignores the box and axis registers. -/
theorem bandPreCost_agree (h : AgreeOff σ τ) (T : ℕ) (hd : Fin 5 → Fin t₀) (w : ℕ) (D : PreAxB)
    [NeZero D.s] (rest : List (Fin (prime + K + 4))) :
    bandPreCost T σ hd w D rest = bandPreCost T τ hd w D rest := by
  have hB1 := agree_bandFB1 h hd w D rest
  have hB2a := agree_bandFB2a hB1 D w
  have hB2b := agree_bandFB2b hB2a D w
  have hP := agree_bandFP hB2b D w (σ (.inl .src)) (τ (.inl .src))
  unfold bandPreCost bandCostB1 bandCostA bandCostB2b bandCostE
  rw [costs_agree h (bandClrB hd) (by simp [bandClrB, preHB]),
    costs_agree hB2a bandScrL (by simp [bandScrL]),
    costs_agree hP bandClrE (by simp [bandClrE])]
  simp only [bvx]
  rw [hP (.inr (.vx 0)) (by simp) (by simp) (by simp), hP (.inr (.vx 1)) (by simp) (by simp) (by simp),
    hP (.inr (.vx 2)) (by simp) (by simp) (by simp), hP (.inr (.vx 3)) (by simp) (by simp) (by simp),
    hP (.inr (.vx 4)) (by simp) (by simp) (by simp), hP (.inr (.vx 5)) (by simp) (by simp) (by simp)]

end Commute

section Frames

variable (σ : RsbR ⊕ RsbX t₀ → List (Fin (prime + K + 4))) (hd : Fin 5 → Fin t₀) (w : ℕ)
  (D : PreAxB) [NeZero D.s] (rest : List (Fin (prime + K + 4)))

open Classical in
lemma bandLoad_prm : bandLoad σ hd w D rest (.inl .prm) = rest := by
  simp [bandLoad, bandFE, bandMvF, bandFE0, bandClrE, bandFP, bandFB2b, bandScrL, bandFB2a, bandFB1,
    bandFF2, bandFF2a, bandFF2b, bandFF2c, bandFF2d, bandFF1, bandFA, preBankB, bandF0, bandClrB,
    preHB, Function.update_apply]

open Classical in
lemma bandLoad_xt (x : RsbX t₀) (hx : x = .xt ∨ x = .e1 ∨ x = .e2) :
    bandLoad σ hd w D rest (.inr x) = σ (.inr x) := by
  rcases hx with rfl | rfl | rfl <;>
  simp [bandLoad, bandFE, bandMvF, bandFE0, bandClrE, bandFP, bandFB2b, bandScrL, bandFB2a, bandFB1,
    bandFF2, bandFF2a, bandFF2b, bandFF2c, bandFF2d, bandFF1, bandFA, preBankB, bandF0, bandClrB,
    preHB, Function.update_apply]

open Classical in
lemma bandLoad_sw (j : Fin (swapT t₀)) :
    bandLoad σ hd w D rest (.inr (.sw j)) =
      if ∃ k, reg (hd k) = j then rsbBank hd (D.hs w) j else σ (.inr (.sw j)) := by
  by_cases hj : ∃ k, reg (hd k) = j
  · simp [bandLoad, bandFE, bandMvF, bandFE0, bandClrE, bandFP, bandFB2b, bandScrL, bandFB2a, bandFB1,
      bandFF2, bandFF2a, bandFF2b, bandFF2c, bandFF2d, bandFF1, bandFA, preBankB, Function.update_apply,
      hj]
  · have hj' : ∀ k, ¬ reg (hd k) = j := fun k e => hj ⟨k, e⟩
    simp [bandLoad, bandFE, bandMvF, bandFE0, bandClrE, bandFP, bandFB2b, bandScrL, bandFB2a, bandFB1,
      bandFF2, bandFF2a, bandFF2b, bandFF2c, bandFF2d, bandFF1, bandFA, preBankB, bandF0, bandClrB, preHB,
      Function.update_apply, hj, hj']
    intro h
    exfalso
    rcases h with h | h | h | h | h <;> exact hj' _ h.symm

open Classical in
lemma bandLoad_vx (hvx : ∀ j, σ (.inr (.vx j)) = []) (j : Fin 12) :
    bandLoad σ hd w D rest (.inr (.vx j)) = [] := by
  simp only [bandLoad, bandFE, bandMvF, bandFE0, bandClrE, bandFP, bandFB2b, bandScrL, bandFB2a,
    bandFB1, bandFF2, bandFF2a, bandFF2b, bandFF2c, bandFF2d, bandFF1, bandFA, bandF0, bandClrB,
    preHB, preBankB, Function.update_apply, bvx]
  fin_cases j <;> simp [hvx]

/-- The loaded register file is again a loader input. -/
lemma bandLoad_free {σ : RsbR ⊕ RsbX t₀ → List (Fin (prime + K + 4))} (hF : BandPreFree σ)
    (hd : Fin 5 → Fin t₀) (w : ℕ) (D : PreAxB) [NeZero D.s] (rest : List (Fin (prime + K + 4)))
    (hwn : (σ (.inl (.cm .wn))).length = w)
    (hnn : (σ (.inl (.cm .nn))).length = IntegerMultBounds.Schoenhage.Schedule.topN w)
    (hA3 : 3 ≤ prime + K) : BandPreFree (bandLoad σ hd w D rest) := by
  have c := bandLoad_cfg σ hd D rest w hF hwn hnn hA3
  exact ⟨c.ya, c.b1, c.tb, c.xa, c.xs, c.pr, c.hc, c.ac, c.hv, c.tL, c.ac2, c.nv, c.tA, c.tJ, c.dst,
    c.tC, c.tK, c.sr, c.sel, c.ef, c.dout, c.vk, bandLoad_vx σ hd w D rest hF.vx, c.ready.empty⟩

lemma BandPreFree.withRsb {σ : RsbR ⊕ RsbX t₀ → List (Fin (prime + K + 4))} (hF : BandPreFree σ)
    (l a a' : List (Fin (prime + K + 4))) : BandPreFree (rsbWith σ l a a') := by
  have h := rsbWith_agree σ l a a'
  have e : ∀ r : RsbR, r ≠ .src → rsbWith σ l a a' (.inl r) = σ (.inl r) := fun r hr =>
    h _ (fun e => hr (Sum.inl_injective e)) (by simp) (by simp)
  exact ⟨by rw [e _ (by decide)]; exact hF.ya, by rw [e _ (by decide)]; exact hF.b1,
    by rw [e _ (by decide)]; exact hF.tb, by rw [e _ (by decide)]; exact hF.xa,
    by rw [e _ (by decide)]; exact hF.xs, by rw [e _ (by decide)]; exact hF.pr,
    by rw [e _ (by decide)]; exact hF.hc, by rw [e _ (by decide)]; exact hF.ac,
    by rw [e _ (by decide)]; exact hF.hv, by rw [e _ (by decide)]; exact hF.tL,
    by rw [e _ (by decide)]; exact hF.ac2, by rw [e _ (by decide)]; exact hF.nv,
    by rw [e _ (by decide)]; exact hF.tA, by rw [e _ (by decide)]; exact hF.tJ,
    by rw [e _ (by decide)]; exact hF.dst, by rw [e _ (by decide)]; exact hF.tC,
    by rw [e _ (by decide)]; exact hF.tK, by rw [e _ (by decide)]; exact hF.sr,
    by rw [e _ (by decide)]; exact hF.sel, by rw [e _ (by decide)]; exact hF.ef,
    by rw [e _ (by decide)]; exact hF.dout, by rw [e _ (by decide)]; exact hF.vk,
    fun j => by rw [h _ (by simp) (by simp) (by simp)]; exact hF.vx j,
    fun c h1 h2 h3 h4 h5 h6 => by rw [e _ (by simp)]; exact hF.cm c h1 h2 h3 h4 h5 h6⟩

end Frames

section Contract

variable {T Q : ℕ} {U F : Type}
variable {body : F → Pr F T Q (prime + K) U} {rg : RsbR → Fin T} {rgx : RsbX t₀ → Fin T}
  {ι : Fin 64 → Fin T}

/-- **The contract `hprep` of `rsb_allG_runs` for the band loader.** -/
theorem bandPreB_rsbWith (hrg₂ : Function.Injective (Sum.elim rg rgx)) (hι : Function.Injective ι)
    (hdisj₂ : ∀ r j, Sum.elim rg rgx r ≠ ι j) (hT : 64 ≤ T) (hQ : SS.states ≤ Q)
    (hA : 96 ≤ prime + K) {hd : Fin 5 → Fin t₀} (hdi : Function.Injective hd)
    (σ : RsbR ⊕ RsbX t₀ → List (Fin (prime + K + 4))) (D : PreAxB) [NeZero D.s]
    (rest : List (Fin (prime + K + 4))) (w : ℕ) (hw : 1 ≤ w) (hok : BandPreOk D w)
    (hF : BandPreFree σ) (hprm : σ (.inl .prm) = preRec D.fields ++ rest)
    (hwn : (σ (.inl (.cm .wn))).length = w)
    (hnn : (σ (.inl (.cm .nn))).length = IntegerMultBounds.Schoenhage.Schedule.topN w)
    (hfit : ∀ m < D.s, FacFits w D.bP D.bK (facState D.bP D.bK
      (bandRows D.bWd D.s (Mult.BandFactor.coefZ D.s D.t D.α D.bP))
      (bandInputs D.bWd D.s (Mult.BandFactor.coefZ D.s D.t D.α D.bP)) m))
    (l a a' : List (Fin (prime + K + 4))) :
    RsbRuns body (Sum.elim rg rgx) ι (bandPreB rg rgx ι hd hι hT hQ) (rsbWith σ l a a')
      (rsbWith (bandLoad σ hd w D rest) l a a') (bandPreCost T σ hd w D rest) := by
  have hag := rsbWith_agree σ l a a'
  have e : ∀ r : RsbR, r ≠ .src → rsbWith σ l a a' (.inl r) = σ (.inl r) := fun r hr =>
    hag _ (fun e => hr (Sum.inl_injective e)) (by simp) (by simp)
  have h := band_preB_runs (body := body) hrg₂ hι hdisj₂ hT hQ hA hdi (rsbWith σ l a a') D rest w hw
    hok (hF.withRsb l a a') (by rw [e _ (by decide)]; exact hprm)
    (by rw [e _ (by simp)]; exact hwn) (by rw [e _ (by simp)]; exact hnn) hfit
  rwa [bandLoad_rsbWith, bandPreCost_agree hag] at h

/-- **One axis after loading.** The loaded register file runs the band lines of the axis on any
box stream of admissible lines. -/
theorem band_axis_loaded (hι : Function.Injective ι) (hT : 64 ≤ T) (hQ : SS.states ≤ Q)
    (hrg : Function.Injective rg) (hdisj : ∀ r j, rg r ≠ ι j) (hA : 96 ≤ prime + K)
    {σ : RsbR ⊕ RsbX t₀ → List (Fin (prime + K + 4))} (hF : BandPreFree σ)
    (hd : Fin 5 → Fin t₀) (w : ℕ) (D : PreAxB) [NeZero D.s] [NeZero D.t]
    (rest : List (Fin (prime + K + 4)))
    (hwn : (σ (.inl (.cm .wn))).length = w)
    (hnn : (σ (.inl (.cm .nn))).length = IntegerMultBounds.Schoenhage.Schedule.topN w)
    (hst : D.s < D.t) (hw1 : 1 ≤ w) (hPw : D.bP ≤ w)
    (htab : BandTabOk w D.s D.bB
      (bandLc D.bP D.bK D.bWd D.s (Mult.BandFactor.coefZ D.s D.t D.α D.bP))
      (bandUc D.bP D.bK D.bWd D.s (Mult.BandFactor.coefZ D.s D.t D.α D.bP))
      (bandRcs D.bP D.bK D.bWd D.s (Mult.BandFactor.coefZ D.s D.t D.α D.bP)) (bandDl D)
      (2 ^ (9 * D.p - 1)) (2 ^ (D.p - D.α * D.α)))
    (lines : List (List GaussianInt))
    (hok : ∀ L ∈ lines, BandLineOk w D.bP D.s D.t D.bB
      (bandLc D.bP D.bK D.bWd D.s (Mult.BandFactor.coefZ D.s D.t D.α D.bP))
      (bandUc D.bP D.bK D.bWd D.s (Mult.BandFactor.coefZ D.s D.t D.α D.bP))
      (bandRcs D.bP D.bK D.bWd D.s (Mult.BandFactor.coefZ D.s D.t D.α D.bP))
      (2 ^ (9 * D.p - 1)) (2 ^ (D.p - D.α * D.α)) L) :
    RsbRuns body rg ι (bandAxisP rg hι hT hQ)
      (Function.update (fun r => bandLoad σ hd w D rest (.inl r)) .src
        (cstream (prime + K) w lines.flatten))
      (Function.update (fun r => bandLoad σ hd w D rest (.inl r)) .src
        (cstream (prime + K) w (lines.flatMap (bandLineT D.bP D.s D.t D.bB
          (bandLc D.bP D.bK D.bWd D.s (Mult.BandFactor.coefZ D.s D.t D.α D.bP))
          (bandUc D.bP D.bK D.bWd D.s (Mult.BandFactor.coefZ D.s D.t D.α D.bP))
          (bandRcs D.bP D.bK D.bWd D.s (Mult.BandFactor.coefZ D.s D.t D.α D.bP)) (bandDl D)
          (2 ^ (9 * D.p - 1)) (2 ^ (D.p - D.α * D.α))))))
      (bandAxisCost T w D.s D.t D.bB lines.length) := by
  have c := (bandLoad_cfg σ hd D rest w hF hwn hnn (by omega)).with_src
    (cstream (prime + K) w lines.flatten)
  have h := band_axis_runs (body := body) (rg := rg) hι hT hQ hrg hdisj hA hst hw1 hPw _ _ _ _ _ _ htab lines
    hok _ c (by simp)
  rwa [Function.update_idem] at h

end Contract

end

end IntegerMultBounds.MathlibTM2.Fast
