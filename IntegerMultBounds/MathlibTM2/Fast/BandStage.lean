module

public import IntegerMultBounds.MathlibTM2.Fast.BandPrep
public import IntegerMultBounds.MathlibTM2.Fast.BandFits
public import IntegerMultBounds.MathlibTM2.Fast.ResampBPipe
public import IntegerMultBounds.MathlibTM2.Mult.Pipeline

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
open IntegerMultBounds.MathlibTM2.Mult.BandSpec

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

/-! ### The configured register files of the stage -/

section StageDefs

open IntegerMultBounds.MathlibTM2.Mult.Pipeline IntegerMultBounds.MathlibTM2.Mult.Sizes

instance preDB_neZero_s (n W : ℕ) (hd0 : 0 < d n) (k : ℕ) : NeZero (preDB n W hd0 k).s :=
  neZero_s n _

instance preDB_neZero_t (n W : ℕ) (hd0 : 0 < d n) (k : ℕ) : NeZero (preDB n W hd0 k).t :=
  neZero_t n _

/-- The register file configured for step `k` of the band stage. -/
def bandCfgB (σ₀ : RsbR ⊕ RsbX t₀ → List (Fin (prime + K + 4))) (hd : Fin 5 → Fin t₀)
    (n w W : ℕ) (hd0 : 0 < d n) (rest : List (Fin (prime + K + 4))) :
    ℕ → RsbR ⊕ RsbX t₀ → List (Fin (prime + K + 4))
  | 0 => bandLoad σ₀ hd w (preDB n W hd0 0) (preRecsB n W hd0 1 ++ rest)
  | k + 1 => bandLoad (bandCfgB σ₀ hd n w W hd0 rest k) hd w (preDB n W hd0 (k + 1))
      (preRecsB n W hd0 (k + 2) ++ rest)

/-- The step bound of the band loader at step `k`. -/
def bandCpB (T : ℕ) (σ₀ : RsbR ⊕ RsbX t₀ → List (Fin (prime + K + 4))) (hd : Fin 5 → Fin t₀)
    (n w W : ℕ) (hd0 : 0 < d n) (rest : List (Fin (prime + K + 4))) : ℕ → ℕ
  | 0 => bandPreCost T σ₀ hd w (preDB n W hd0 0) (preRecsB n W hd0 1 ++ rest)
  | k + 1 => bandPreCost T (bandCfgB σ₀ hd n w W hd0 rest k) hd w (preDB n W hd0 (k + 1))
      (preRecsB n W hd0 (k + 2) ++ rest)

/-- A base register file for the band stage. -/
structure BandBase (σ : RsbR ⊕ RsbX t₀ → List (Fin (prime + K + 4))) (w : ℕ) (hd : Fin 5 → Fin t₀) :
    Prop where
  free : BandPreFree σ
  wn : (σ (.inl (.cm .wn))).length = w
  nn : (σ (.inl (.cm .nn))).length = IntegerMultBounds.Schoenhage.Schedule.topN w
  bank : ∀ j, (∀ k, reg (hd k) ≠ j) → σ (.inr (.sw j)) = []
  xt : σ (.inr .xt) = []
  e1 : σ (.inr .e1) = []
  e2 : σ (.inr .e2) = []

lemma BandBase.load {σ : RsbR ⊕ RsbX t₀ → List (Fin (prime + K + 4))} {w : ℕ}
    {hd : Fin 5 → Fin t₀} (h : BandBase σ w hd) (hA3 : 3 ≤ prime + K) (D : PreAxB) [NeZero D.s]
    (rest : List (Fin (prime + K + 4))) : BandBase (bandLoad σ hd w D rest) w hd := by
  have c := bandLoad_cfg σ hd D rest w h.free h.wn h.nn hA3
  refine ⟨bandLoad_free h.free hd w D rest h.wn h.nn hA3, c.ready.wn, c.ready.nn, fun j hj => ?_,
    by rw [bandLoad_xt _ _ _ _ _ _ (Or.inl rfl)]; exact h.xt,
    by rw [bandLoad_xt _ _ _ _ _ _ (Or.inr (Or.inl rfl))]; exact h.e1,
    by rw [bandLoad_xt _ _ _ _ _ _ (Or.inr (Or.inr rfl))]; exact h.e2⟩
  rw [bandLoad_sw]
  split_ifs with hk
  · exact absurd hk (fun ⟨k, e⟩ => hj k e)
  · exact h.bank j hj

variable {σ₀ : RsbR ⊕ RsbX t₀ → List (Fin (prime + K + 4))} {hd : Fin 5 → Fin t₀} {n w W : ℕ}
  {hd0 : 0 < d n} {rest : List (Fin (prime + K + 4))}

lemma bandCfgB_base (h : BandBase σ₀ w hd) (hA3 : 3 ≤ prime + K) :
    ∀ k, BandBase (bandCfgB σ₀ hd n w W hd0 rest k) w hd
  | 0 => h.load hA3 _ _
  | k + 1 => (bandCfgB_base h hA3 k).load hA3 _ _

lemma bandCfgB_prm (k : ℕ) :
    bandCfgB σ₀ hd n w W hd0 rest k (.inl .prm) = preRecsB n W hd0 (k + 1) ++ rest := by
  cases k <;> exact bandLoad_prm _ _ _ _ _

lemma bandCfgB_sw (h : BandBase σ₀ w hd) (hA3 : 3 ≤ prime + K) (k : ℕ) (j : Fin (swapT t₀)) :
    bandCfgB σ₀ hd n w W hd0 rest k (.inr (.sw j)) = rsbBank hd (preHsB n w hd0 (rsbAx hd0 k)) j := by
  have e : ∀ σ : RsbR ⊕ RsbX t₀ → List (Fin (prime + K + 4)), (∀ j, (∀ k, reg (hd k) ≠ j) →
      σ (.inr (.sw j)) = []) → ∀ (D : PreAxB) [NeZero D.s] (r : List (Fin (prime + K + 4))),
      D.hs w = preHsB n w hd0 (rsbAx hd0 k) →
      bandLoad σ hd w D r (.inr (.sw j)) = rsbBank hd (preHsB n w hd0 (rsbAx hd0 k)) j := by
    intro σ hσ D _ r hD
    rw [bandLoad_sw]
    split_ifs with hj
    · rw [hD]
    · have hj' : ∀ k, reg (hd k) ≠ j := fun k e => hj ⟨k, e⟩
      rw [hσ j hj', rsbBank_other _ hj']
  cases k with
  | zero => exact e σ₀ h.bank _ _ rfl
  | succ k => exact e _ (bandCfgB_base (n := n) (W := W) (hd0 := hd0) (rest := rest) h
      hA3 k).bank _ _ rfl

end StageDefs

/-! ### The line maps of the stage -/

section Lines

open IntegerMultBounds.MathlibTM2.Mult.Pipeline IntegerMultBounds.MathlibTM2.Mult.Sizes

/-- A line map related to a map of the unit ball into itself keeps lines in the unit disk. -/
theorem lineRel_ball {M N q : ℕ} [NeZero M] [NeZero N] {A : (ZMod M → ℂ) → ZMod N → ℂ}
    {g : List GaussianInt → List GaussianInt} (hrel : RsbLineRel M N A g q)
    (hA : ∀ v, ‖v‖ ≤ 1 → ‖A v‖ ≤ 1) (L : List GaussianInt) (hL : ∀ y ∈ L, ‖rsbGrid q y‖ ≤ 1) :
    ∀ x ∈ g L, ‖rsbGrid q x‖ ≤ 1 := by
  set v : ZMod M → ℂ := fun j => rsbGrid q (L.getD j.val 0)
  have hv : ‖v‖ ≤ 1 := by
    refine (pi_norm_le_iff_of_nonneg (by norm_num)).mpr fun j => ?_
    simp only [v]
    by_cases hj : j.val < L.length
    · rw [List.getD_eq_getElem _ _ hj]; exact hL _ (List.getElem_mem hj)
    · rw [List.getD_eq_default _ _ (by omega)]; simp [rsbGrid]
  intro x hx
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hx
  by_cases hkN : k < N
  · have e := hrel.num L v (fun j => rfl) k hkN
    rw [List.getD_eq_getElem _ _ hk] at e
    rw [rsbGrid, ← e]
    exact (norm_le_pi_norm (A v) _).trans (hA v hv)
  · have e := hrel.pad L k (by omega)
    rw [List.getD_eq_getElem _ _ hk] at e
    rw [e]; simp [rsbGrid]

variable (n : ℕ)

/-- The diagonal table of axis `i` at precision `5p`. -/
noncomputable def bandDlN (i : Fin (d n)) : List ℤ :=
  rsbArr fun ℓ : ZMod (s n i) => tableD (s n i) (t n i) (alpha n) (p n) ℓ * 2 ^ (4 * p n)

/-- The band line map of axis `i`. -/
noncomputable def bandG (i : Fin (d n)) : List GaussianInt → List GaussianInt :=
  bandLineT (5 * p n) (s n i) (t n i) (2 * (8 * Mult.FastB0.fastWindow (p n) (alpha n)) + 1)
    (bandLc (5 * p n) (4 * (alpha n * alpha n)) (8 * Mult.FastB0.fastWindow (p n) (alpha n)) (s n i)
      (bandAZ n i))
    (bandUc (5 * p n) (4 * (alpha n * alpha n)) (8 * Mult.FastB0.fastWindow (p n) (alpha n)) (s n i)
      (bandAZ n i))
    (bandRcs (5 * p n) (4 * (alpha n * alpha n)) (8 * Mult.FastB0.fastWindow (p n) (alpha n)) (s n i)
      (bandAZ n i))
    (bandDlN n i) (2 ^ (9 * p n - 1)) (2 ^ (p n - alpha n * alpha n))

variable {n}

theorem bandG_eq (h : Big n) (i : Fin (d n)) :
    bandLineG (5 * p n) (4 * (alpha n * alpha n)) (8 * Mult.FastB0.fastWindow (p n) (alpha n))
      (p n) (alpha n * alpha n) (s n i) (t n i) (bandAZ n i) (bandDlN n i) = bandG n i := by
  have hp13 := h.thirteen_le_p
  funext L
  simp only [bandLineG, bandG, bandLineT]
  rw [show 2 * (5 * p n) - p n - 1 = 9 * p n - 1 by omega]

theorem length_bandG (h : Big n) (i : Fin (d n)) (L : List GaussianInt) :
    (bandG n i L).length = t n i := by
  have hp13 := h.thirteen_le_p
  have hst := (h.good.lt i).le
  rw [← bandG_eq h i, bandLineG, List.length_append, length_bandOutVec _ _ _ _ _ _ _ (by omega) _ _
    (by simp [bandDlN, rsbArr])]
  simp; omega

/-- **The band line of axis `i` computes `bandA` on numerators.** -/
theorem band_axis_rel (h : Big n) (i : Fin (d n)) :
    RsbLineRel (t n i) (s n i) (bandA n i) (bandG n i) (p n) := by
  have hp13 := h.thirteen_le_p
  have hαp := h.alpha_sq_le_p
  have hjp : alpha n * alpha n ≤ p n := by nlinarith
  have hrel := band_lineG_rel (5 * p n) (4 * (alpha n * alpha n))
    (8 * Mult.FastB0.fastWindow (p n) (alpha n)) (p n) (alpha n * alpha n) (s n i) (t n i)
    (by omega) (by omega) hjp (bandAZ n i) (bandDlN n i)
    (fun ℓ => tableD (s n i) (t n i) (alpha n) (p n) ℓ) (by simp [bandDlN, rsbArr])
    (fun ℓ => by
      rw [bandDlN, rsbArr, List.getD_eq_getElem _ _ (by simpa using ZMod.val_lt ℓ), List.getElem_map,
        List.getElem_range, ZMod.natCast_zmod_val, show 5 * p n - p n = 4 * p n by omega])
    (fun ℓ => (tableD (s n i) (t n i) (alpha n) (p n) ℓ : ℝ) / 2 ^ p n)
    (fun ℓ => by
      rw [Resampling.WindowSum.rhoC_real, mul_div_cancel₀ _ (by positivity : (2 : ℝ) ^ p n ≠ 0),
        Resampling.NeumannWords.rho0_int]
      apply Complex.ext <;> simp [rsbGrid, rsbReal, GaussianInt.toComplex_def])
  rw [bandG_eq h i] at hrel
  exact hrel

end Lines

/-! ### The stage -/

section Stage

open IntegerMultBounds.MathlibTM2.Mult.Pipeline IntegerMultBounds.MathlibTM2.Mult.Sizes
open IntegerMultBounds.NLogN IntegerMultBounds.NLogN.SchurDominance

variable {T Q : ℕ} {U F : Type}
variable {body : F → Pr F T Q (prime + K) U} {rg : RsbR → Fin T} {rgx : RsbX t₀ → Fin T}
  {ι : Fin 64 → Fin T}

variable {n : ℕ}

/-- The admissible lines of axis `i`: length `t_i`, entries in the unit disk. -/
def BandOk (n : ℕ) (i : Fin (d n)) (L : List GaussianInt) : Prop :=
  L.length = t n i ∧ ∀ y ∈ L, ‖rsbGrid (p n) y‖ ≤ 1

theorem band_lineOk_of (h : Big n) {β : ℝ} {w : ℕ} (hpre : BandPrec n β w) (i : Fin (d n))
    (hax : BandAxisMath n β i) (L : List GaussianInt) (hL : BandOk n i L) :
    BandLineOk w (5 * p n) (s n i) (t n i) (2 * (8 * Mult.FastB0.fastWindow (p n) (alpha n)) + 1)
      (bandLc (5 * p n) (4 * (alpha n * alpha n)) (8 * Mult.FastB0.fastWindow (p n) (alpha n)) (s n i)
        (bandAZ n i))
      (bandUc (5 * p n) (4 * (alpha n * alpha n)) (8 * Mult.FastB0.fastWindow (p n) (alpha n)) (s n i)
        (bandAZ n i))
      (bandRcs (5 * p n) (4 * (alpha n * alpha n)) (8 * Mult.FastB0.fastWindow (p n) (alpha n)) (s n i)
        (bandAZ n i))
      (2 ^ (9 * p n - 1)) (2 ^ (p n - alpha n * alpha n)) L := by
  have hp13 := h.thirteen_le_p
  have hαp := h.alpha_sq_le_p
  have hjp : alpha n * alpha n ≤ p n := by nlinarith
  have hLb : ∀ x ∈ L, |x.re| ≤ 2 ^ p n ∧ |x.im| ≤ 2 ^ p n := by
    intro x hx
    have hn := hL.2 x hx
    have hP : (0 : ℝ) < 2 ^ p n := by positivity
    have h1 := (Complex.abs_re_le_norm (rsbGrid (p n) x)).trans hn
    have h2 := (Complex.abs_im_le_norm (rsbGrid (p n) x)).trans hn
    rw [rsbGrid, two_pow_complex, toComplex_div_re, abs_div, abs_of_pos hP, div_le_one hP] at h1
    rw [rsbGrid, two_pow_complex, toComplex_div_im, abs_div, abs_of_pos hP, div_le_one hP] at h2
    exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩
  have H := band_lineOk (K := 4 * (alpha n * alpha n)) (wd := 8 * Mult.FastB0.fastWindow (p n) (alpha n))
    (aZ := bandAZ n i) (p n) (alpha n * alpha n) (t n i) (by omega) (by omega) hjp hax.inv β hpre.pos
    hpre.le hpre.eta hpre.newton hax.small hax.err w hpre.width L hL.1 hLb
  rwa [show 2 * (5 * p n) - p n - 1 = 9 * p n - 1 by omega] at H

lemma bandCfgB_eq {σ₀ : RsbR ⊕ RsbX t₀ → List (Fin (prime + K + 4))} {w : ℕ} {hd : Fin 5 → Fin t₀}
    (hσ₀ : BandBase σ₀ w hd) (hA3 : 3 ≤ prime + K) (W : ℕ) (hd0 : 0 < d n)
    (rest : List (Fin (prime + K + 4))) (k : ℕ) :
    ∃ σ, BandBase σ w hd ∧ bandCfgB σ₀ hd n w W hd0 rest k =
      bandLoad σ hd w (preDB n W hd0 k) (preRecsB n W hd0 (k + 1) ++ rest) := by
  cases k with
  | zero => exact ⟨σ₀, hσ₀, rfl⟩
  | succ k => exact ⟨_, bandCfgB_base hσ₀ hA3 k, rfl⟩

lemma fits_pow_le {w a b : ℕ} (hab : a ≤ b) (h : Fits w (⟨2 ^ b, 0⟩ : GaussianInt)) :
    Fits w (⟨2 ^ a, 0⟩ : GaussianInt) := by
  refine ⟨lt_of_le_of_lt ?_ h.1, h.2⟩
  simp only [abs_pow, abs_two]
  exact pow_le_pow_right₀ (by norm_num) hab

/-- **The axis contract of the band stage.** -/
theorem band_stage_hcfg (h : Big n) (hd0 : 0 < d n) (hι : Function.Injective ι) (hT : 64 ≤ T)
    (hQ : SS.states ≤ Q) (hrg₂ : Function.Injective (Sum.elim rg rgx))
    (hdisj₂ : ∀ r j, Sum.elim rg rgx r ≠ ι j) (hA : 96 ≤ prime + K) {β : ℝ} {w W : ℕ}
    (hpre : BandPrec n β w) (hax : ∀ i, BandAxisMath n β i)
    (hok : ∀ k < d n, BandPreOk (preDB n W hd0 k) w) (hw1 : 1 ≤ w)
    (hDfit : ∀ i, ∀ x ∈ bandDlN n i, Fits w (⟨x, 0⟩ : GaussianInt))
    {hd : Fin 5 → Fin t₀} {σ₀ : RsbR ⊕ RsbX t₀ → List (Fin (prime + K + 4))}
    (hσ₀ : BandBase σ₀ w hd) (rest : List (Fin (prime + K + 4))) (k : ℕ) (hk : k < d n) :
    (∀ lines : List (List GaussianInt), (∀ c ∈ lines, BandOk n (rsbAx hd0 k) c) →
      RsbRuns body rg ι (bandAxisP rg hι hT hQ)
        (Function.update (fun r => bandCfgB σ₀ hd n w W hd0 rest k (.inl r)) .src
          (cstream (prime + K) w lines.flatten))
        (Function.update (fun r => bandCfgB σ₀ hd n w W hd0 rest k (.inl r)) .src
          (cstream (prime + K) w (lines.flatMap (bandG n (rsbAx hd0 k)))))
        (bandAxisCost T w (s n (rsbAx hd0 k)) (t n (rsbAx hd0 k))
          (2 * (8 * Mult.FastB0.fastWindow (p n) (alpha n)) + 1) lines.length)) ∧
    (0 < k → (∀ j, bandCfgB σ₀ hd n w W hd0 rest k (.inr (.sw j)) =
        rsbBank hd (preHsB n w hd0 (rsbAx hd0 k)) j) ∧
      bandCfgB σ₀ hd n w W hd0 rest k (.inr .xt) = [] ∧
      bandCfgB σ₀ hd n w W hd0 rest k (.inr .e1) = [] ∧
      bandCfgB σ₀ hd n w W hd0 rest k (.inr .e2) = []) := by
  have hA3 : 3 ≤ prime + K := by omega
  have hp13 := h.thirteen_le_p
  refine ⟨fun lines hlines => ?_, fun _ => ⟨bandCfgB_sw hσ₀ hA3 k, (bandCfgB_base hσ₀ hA3 k).xt,
    (bandCfgB_base hσ₀ hA3 k).e1, (bandCfgB_base hσ₀ hA3 k).e2⟩⟩
  obtain ⟨σ, hσ, e⟩ := bandCfgB_eq hσ₀ hA3 W hd0 rest k
  rw [e]
  set i := rsbAx hd0 k
  have hrg : Function.Injective rg := fun a b hab => Sum.inl_injective (hrg₂ (a₁ := .inl a) hab)
  have hdisj : ∀ r j, rg r ≠ ι j := fun r j => hdisj₂ (.inl r) j
  have hO : Fits w (⟨2 ^ (p n - alpha n * alpha n), 0⟩ : GaussianInt) := by
    refine ⟨?_, by simp⟩
    have h1 : (2 : ℝ) ^ (p n - alpha n * alpha n) ≤ 2 ^ (5 * p n) :=
      pow_le_pow_right₀ (by norm_num) (by omega)
    have h2 : (2 : ℝ) ^ (5 * p n) ≤ (6 / β + 1) * 2 ^ (5 * p n) := by
      have : 0 ≤ 6 / β := div_nonneg (by norm_num) hpre.pos.le
      exact le_mul_of_one_le_left (by positivity) (by linarith)
    have h3 := lt_of_le_of_lt (h1.trans h2) hpre.width
    simp only [abs_pow, abs_two]
    exact_mod_cast h3
  have htab := band_tabOk (K := 4 * (alpha n * alpha n))
    (wd := 8 * Mult.FastB0.fastWindow (p n) (alpha n)) (aZ := bandAZ n i) (p n) (by omega)
    (by omega) (hax i).inv β hpre.pos hpre.le hpre.eta hpre.newton (hax i).small w hpre.width
    (bandDlN n i) (by simp [bandDlN, rsbArr]) (hDfit i) _ _
    (fits_pow_le (show 9 * p n - 1 ≤ 9 * p n by omega) (hok k hk).fc) hO
  exact band_axis_loaded (body := body) hι hT hQ hrg hdisj hA hσ.free hd w (preDB n W hd0 k) _ hσ.wn
    hσ.nn (h.good.lt i) hw1 (hok k hk).Pw htab lines
    (fun L hL => band_lineOk_of h hpre i (hax i) L (hlines L hL))

/-- **The loader contract of the band stage.** -/
theorem band_stage_hprep (h : Big n) (hd0 : 0 < d n) (hι : Function.Injective ι) (hT : 64 ≤ T)
    (hQ : SS.states ≤ Q) (hrg₂ : Function.Injective (Sum.elim rg rgx))
    (hdisj₂ : ∀ r j, Sum.elim rg rgx r ≠ ι j) (hA : 96 ≤ prime + K) {β : ℝ} {w W : ℕ}
    (hpre : BandPrec n β w) (hax : ∀ i, BandAxisMath n β i)
    (hok : ∀ k < d n, BandPreOk (preDB n W hd0 k) w) (hw1 : 1 ≤ w)
    {hd : Fin 5 → Fin t₀} (hdi : Function.Injective hd)
    {σ : RsbR ⊕ RsbX t₀ → List (Fin (prime + K + 4))} (hσ : BandBase σ w hd)
    (rest : List (Fin (prime + K + 4))) (k : ℕ) (hk : k < d n)
    (hprm : σ (.inl .prm) = preRecsB n W hd0 k ++ rest) (l a a' : List (Fin (prime + K + 4))) :
    RsbRuns body (Sum.elim rg rgx) ι (bandPreB rg rgx ι hd hι hT hQ) (rsbWith σ l a a')
      (rsbWith (bandLoad σ hd w (preDB n W hd0 k) (preRecsB n W hd0 (k + 1) ++ rest)) l a a')
      (bandPreCost T σ hd w (preDB n W hd0 k) (preRecsB n W hd0 (k + 1) ++ rest)) := by
  have hp13 := h.thirteen_le_p
  set i := rsbAx hd0 k
  exact bandPreB_rsbWith (body := body) hrg₂ hι hdisj₂ hT hQ hA hdi σ _ _ w hw1 (hok k hk) hσ.free
    (by rw [hprm, preRecsB_succ n W hd0 hk, List.append_assoc]) hσ.wn hσ.nn
    (fun m hm => band_facFits (K := 4 * (alpha n * alpha n))
      (wd := 8 * Mult.FastB0.fastWindow (p n) (alpha n)) (aZ := bandAZ n i) (p n) (by omega)
      (by omega) (hax i).inv β hpre.pos hpre.le hpre.eta hpre.newton (hax i).small w hpre.width m hm)
    l a a'

/-- **The banded `B̃₀` stage with its loader.** At operand length `n` in the regime `Big n`, with
the numeric facts of every axis (`BandAxisMath`), the Newton precision and record width
(`BandPrec`), the loader conditions of every axis and fitting diagonal tables: from a base
register file `σ₀` whose parameter register `prm` holds the records of the pipeline followed by
`rest`, with the box register holding the padded stream of the numerators of `u` at scale `p n`
(`‖u‖ ≤ 1`), the stage ends with the box register holding the numerators of
`tensorZR (d n) (t n) (s n) (bandA n) u` at scale `p n` (zero off the source box). -/
theorem bandStage_exec (n : ℕ) (h : Big n) (hd0 : 0 < d n)
    (hrg₂ : Function.Injective (Sum.elim rg rgx)) (hdisj₂ : ∀ r j, Sum.elim rg rgx r ≠ ι j)
    (hι : Function.Injective ι) (hT : 64 ≤ T) (hQ : SS.states ≤ Q) (hA : 96 ≤ prime + K)
    (hd : Fin 5 → Fin t₀) (pay : Fin t₀) (hi : Function.Injective hd)
    (hQs : swapStates hd pay hi ≤ Q) (hsw : Function.Injective fun j => rgx (.sw j))
    (hTs : swapT t₀ ≤ T) (hdpay : ∀ k, hd k ≠ pay) {β : ℝ} {w W : ℕ} (hw1 : 1 ≤ w)
    (hpre : BandPrec n β w) (hax : ∀ i, BandAxisMath n β i)
    (hok : ∀ k < d n, BandPreOk (preDB n W hd0 k) w)
    (hDfit : ∀ i, ∀ x ∈ bandDlN n i, Fits w (⟨x, 0⟩ : GaussianInt))
    (σ₀ : RsbR ⊕ RsbX t₀ → List (Fin (prime + K + 4))) (hσ₀ : BandBase σ₀ w hd)
    (rest : List (Fin (prime + K + 4))) (hprm : σ₀ (.inl .prm) = preRecsB n W hd0 0 ++ rest)
    (u : ((i : Fin (d n)) → ZMod (t n i)) → ℂ)
    (Fn : ((i : Fin (d n)) → Fin (t n i)) → GaussianInt)
    (hF : ∀ x : (i : Fin (d n)) → Fin (t n i),
      u (fun i => ((x i : ℕ) : ZMod (t n i))) = GaussianInt.toComplex (Fn x) / 2 ^ p n)
    (hu : ∀ x : (i : Fin (d n)) → Fin (t n i), ‖u (fun i => ((x i : ℕ) : ZMod (t n i)))‖ ≤ 1)
    (axs : List (Fin (prime + K + 4))) (haxs : axs.length = d n - 1) :
    ∃ G : ((i : Fin (d n)) → Fin (t n i)) → GaussianInt,
      (∀ x : (i : Fin (d n)) → Fin (t n i), (∀ i, (x i : ℕ) < s n i) →
        tensorZR (d n) (t n) (s n) (bandA n) u (fun i => ((x i : ℕ) : ZMod (s n i))) =
          GaussianInt.toComplex (G x) / 2 ^ p n) ∧
      (∀ x : (i : Fin (d n)) → Fin (t n i), (∃ i, s n i ≤ x i) → G x = 0) ∧
      RsbRuns body (Sum.elim rg rgx) ι (rsbAllG (bandPreB rg rgx ι hd hι hT hQ)
          (bandAxisP rg hι hT hQ) rg rgx hd pay hi hQs hsw hTs)
        (rsbWith σ₀ (cstream (prime + K) w (rsbBox (d n) (t n) Fn)) axs [])
        (rsbWith (bandCfgB σ₀ hd n w W hd0 rest (d n - 1))
          (cstream (prime + K) w (rsbBox (d n) (t n) G)) axs [])
        (rsbAllCostG T t₀ w (d n) (t n) hd0 (fun i => Nat.log 2 (t n i)) (preHsB n w hd0)
          (fun i nl => bandAxisCost T w (s n i) (t n i)
            (2 * (8 * Mult.FastB0.fastWindow (p n) (alpha n)) + 1) nl)
          (prime + K) hd (bandCpB T σ₀ hd n w W hd0 rest) (∏ i, t n i)) := by
  have hp13 := h.thirteen_le_p
  have hA3 : 3 ≤ prime + K := by omega
  have hbox : ∀ y ∈ rsbBox (d n) (t n) Fn, ‖rsbGrid (p n) y‖ ≤ 1 := by
    intro y hy
    obtain ⟨a, rfl⟩ := rsb_mem_rsbBox _ _ _ hy
    rw [rsbGrid, ← hF a]
    exact hu a
  have hflat := rsb_flat_mem (t n) (bandG n) (fun y => ‖rsbGrid (p n) y‖ ≤ 1) (by simp [rsbGrid])
    (fun i L _ hL => lineRel_ball (band_axis_rel h i) (hax i).ball L hL) _ hbox
  have hlast : rsbAx hd0 0 = ResampA.rsaStepAx hd0 0 := rfl
  refine rsb_allG_tensor (body := body) (bandPreB rg rgx ι hd hι hT hQ) (bandAxisP rg hι hT hQ)
    hrg₂ hdisj₂ hA hd pay hi hQs hsw hTs hdpay hd0 (t n) hw1 (fun i => Nat.log 2 (t n i))
    (preHsB n w hd0) (bandG n) (fun i x => length_bandG h i x) (BandOk n) _ (t_pow_log n)
    (fun i hi1 => ?_) σ₀ (bandCfgB σ₀ hd n w W hd0 rest)
    (fun k hk => band_stage_hcfg (body := body) h hd0 hι hT hQ hrg₂ hdisj₂ hA hpre hax hok hw1 hDfit
      hσ₀ rest k hk) (bandCpB T σ₀ hd n w W hd0 rest)
    (fun l a a' => band_stage_hprep (body := body) h hd0 hι hT hQ hrg₂ hdisj₂ hA hpre hax hok hw1 hi
      hσ₀ rest 0 hd0 hprm l a a')
    (fun k hk l a a' => band_stage_hprep (body := body) h hd0 hι hT hQ hrg₂ hdisj₂ hA hpre hax hok hw1
      hi (bandCfgB_base hσ₀ hA3 k) rest (k + 1) hk (bandCfgB_prm k) l a a')
    (s n) (fun i => (h.good.lt i).le) (bandA n) (p n) (fun i => band_axis_rel h i) u Fn hF
    (fun i p' _ q _ => ⟨length_rsbLineAt _ _ _ _ _, fun y hy =>
      (rsb_mem_rsbLineAt hy).elim (fun e => by rw [e]; simp [rsbGrid]) (fun hy' => hflat _ y hy')⟩)
    axs haxs
  have hl := pre_log_last h hd0
  rw [← hlast] at hl
  refine ⟨?_, ?_, fun k => ?_, fun k => canonical_sxBits _⟩
  · rw [hl]; rcases pre_log_t (n := n) i with e | e <;> omega
  · rw [hl]
    rcases pre_log_t (n := n) i with e | e <;> rw [e] <;> have := h.two_le_ℓ <;> omega
  · simp only [preHsB, value_sxBits]

end Stage

/-! ### The stage's conditions from widths -/

section Sizes

open IntegerMultBounds.MathlibTM2.Mult.Pipeline IntegerMultBounds.MathlibTM2.Mult.Sizes
open IntegerMultBounds.Resampling.WeightTable (tableD_spec)

variable {n : ℕ}

theorem fits_real_of_le {w : ℕ} {x : ℤ} (h0 : 0 ≤ x) (h : x < 2 ^ (w - 1)) :
    Fits w (⟨x, 0⟩ : GaussianInt) :=
  ⟨by rw [abs_of_nonneg h0]; exact h, by simp⟩

/-- The numeric facts behind the loader conditions of axis `i`. -/
theorem band_preOk_facts (h : Big n) {w W : ℕ} (hw9 : 9 * p n + 2 ≤ w) (i : Fin (d n))
    (hW : alpha n ^ 2 * ((s n i + t n i) *
      (8 * Mult.FastB0.fastWindow (p n) (alpha n) + 1)) ^ 2 * 2 ^ (65 * p n + 8) < 2 ^ W) :
    2 * (8 * Mult.FastB0.fastWindow (p n) (alpha n)) + 1 < s n i ∧ 65 * p n + 8 < W ∧
      2 * s n i * (t n i + 1) < 2 ^ W ∧ s n i * s n i < 2 ^ W ∧ alpha n * alpha n < 2 ^ W ∧
      (2 * (8 * Mult.FastB0.fastWindow (p n) (alpha n)) + 1 + 1 + s n i) +
        2 * (2 * (8 * Mult.FastB0.fastWindow (p n) (alpha n)) + 1) + 1 < 2 ^ W ∧
      t n i < 2 ^ W ∧ 8 * Mult.FastB0.fastWindow (p n) (alpha n) < 2 ^ W ∧
      alpha n ^ 2 * ((s n i + t n i) * (Mult.FastB0.fastWindow (p n) (alpha n) + 1)) ^ 2 *
        2 ^ (13 * p n + 8) < 2 ^ W := by
  have hp64 := h.sixty_four_le_p
  have hα2 := two_le_alpha h.1
  have hps := pre_p_le_s h i
  have hst := h.good.lt i
  set m := Mult.FastB0.fastWindow (p n) (alpha n)
  have hm : 16 * m + 1 < p n := by
    have h1 : Nat.sqrt (p n) / (2 * alpha n) ≤ Nat.sqrt (p n) / 4 :=
      Nat.div_le_div_left (by omega) (by norm_num)
    have h2 : Nat.sqrt (p n) * Nat.sqrt (p n) ≤ p n := Nat.sqrt_le (p n)
    have h3 : 8 ≤ Nat.sqrt (p n) := Nat.le_sqrt'.mpr (by omega)
    have h4 : 4 * (Nat.sqrt (p n) / 4) ≤ Nat.sqrt (p n) := Nat.mul_div_le _ _
    have : 8 * Nat.sqrt (p n) ≤ p n := le_trans (Nat.mul_le_mul_right _ h3) h2
    simp only [m, Mult.FastB0.fastWindow]; omega
  have hm1 : 1 ≤ m := by simp [m, Mult.FastB0.fastWindow]
  have hW' : alpha n ^ 2 * ((s n i + t n i) * (8 * m + 1)) ^ 2 * 2 ^ (13 * (5 * p n) + 8) < 2 ^ W := by
    rw [show 13 * (5 * p n) + 8 = 65 * p n + 8 by ring]; exact hW
  have hN1 : 1 ≤ (s n i + t n i) * (8 * m + 1) := Nat.mul_pos (by omega) (by omega)
  obtain ⟨hW1, -, hNN, hααNN⟩ := TableVM.tbl_W_facts hα2 hN1 hW'
  set N := (s n i + t n i) * (8 * m + 1)
  have hsN : 9 * (s n i + t n i) ≤ N := by
    calc 9 * (s n i + t n i) ≤ (8 * m + 1) * (s n i + t n i) := Nat.mul_le_mul_right _ (by omega)
      _ = N := by ring
  have hNN' : N ≤ N * N := Nat.le_mul_self N
  have hDW : alpha n ^ 2 * ((s n i + t n i) * (m + 1)) ^ 2 * 2 ^ (13 * p n + 8) < 2 ^ W := by
    refine lt_of_le_of_lt ?_ hW
    have hmN : (s n i + t n i) * (m + 1) ≤ N := Nat.mul_le_mul_left _ (by omega)
    have := Nat.pow_le_pow_left hmN 2
    have h13 : 2 ^ (13 * p n + 8) ≤ 2 ^ (65 * p n + 8) := Nat.pow_le_pow_right (by norm_num) (by omega)
    exact Nat.mul_le_mul (Nat.mul_le_mul_left _ this) h13
  refine ⟨by omega, by omega, ?_, ?_, ?_, ?_, ?_, ?_, hDW⟩
  · refine lt_of_le_of_lt ?_ hNN; nlinarith
  · refine lt_of_le_of_lt ?_ hNN; nlinarith
  · refine lt_of_le_of_lt ?_ hααNN; nlinarith
  · refine lt_of_le_of_lt ?_ hNN; nlinarith
  · refine lt_of_le_of_lt ?_ hNN; nlinarith
  · refine lt_of_le_of_lt ?_ hNN; nlinarith

/-- **The loader conditions of every axis** at a width `w ≥ 9p + 2` and a table word with
`α² ((s+t)(8m+1))² 2^(65p+8) < 2^W`. -/
theorem band_preOk (h : Big n) (hd0 : 0 < d n) {w W : ℕ} (hw9 : 9 * p n + 2 ≤ w) (hwW : w ≤ W)
    (hW65 : ∀ i : Fin (d n), alpha n ^ 2 * ((s n i + t n i) *
      (8 * Mult.FastB0.fastWindow (p n) (alpha n) + 1)) ^ 2 * 2 ^ (65 * p n + 8) < 2 ^ W)
    (k : ℕ) (_hk : k < d n) : BandPreOk (preDB n W hd0 k) w := by
  obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8, f9⟩ := band_preOk_facts h hw9 (rsbAx hd0 k) (hW65 _)
  have hp13 := h.thirteen_le_p
  have hW' := hW65 (rsbAx hd0 k)
  rw [show 65 * p n + 8 = 13 * (5 * p n) + 8 by ring] at hW'
  have hst := h.good.lt (rsbAx hd0 k)
  have hw1 : 2 ^ (9 * p n) < 2 ^ (w - 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hP : 2 ^ (5 * p n) < 2 ^ W := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hfold : BandFoldW (preDB n W hd0 k) :=
    ⟨f1, by show 13 ≤ 5 * p n; omega,
      TableVM.tblOffW_of (two_le_alpha h.1) (by show 0 < s n _ + t n _; omega) hW',
      by show 5 * (5 * p n) + 16 ≤ W; omega, f3, f4, f5, hP, f6, f7, f8⟩
  refine ⟨hfold, hwW, hp13, two_le_alpha h.1, h.alpha_sq_le_p, by show 0 < s n _; omega, hst, f9,
    by show 9 * p n + 1 < W; omega, by show 5 * p n ≤ w; omega, fun ℓ => ?_, ?_⟩
  · obtain ⟨-, h0, h1⟩ := tableD_spec (s n (rsbAx hd0 k)) (t n (rsbAx hd0 k)) (alpha n) (p n)
      hp13 (by have := two_le_alpha h.1; omega) h.alpha_sq_le_p ℓ
    refine fits_real_of_le h0 (lt_of_le_of_lt h1 ?_)
    have : (2 : ℤ) ^ p n < 2 ^ (9 * p n) := pow_lt_pow_right₀ (by norm_num) (by omega)
    exact this.trans (by exact_mod_cast hw1)
  · exact fits_real_of_le (by positivity) (by exact_mod_cast hw1)

/-- The diagonal tables fit a width `w ≥ 9p + 2`. -/
theorem band_dfit (h : Big n) {w : ℕ} (hw9 : 9 * p n + 2 ≤ w) (i : Fin (d n)) :
    ∀ x ∈ bandDlN n i, Fits w (⟨x, 0⟩ : GaussianInt) := by
  intro x hx
  simp only [bandDlN, rsbArr, List.mem_map, List.mem_range] at hx
  obtain ⟨ℓ, -, rfl⟩ := hx
  have hp13 := h.thirteen_le_p
  obtain ⟨-, h0, h1⟩ := tableD_spec (s n i) (t n i) (alpha n) (p n) hp13 (by have := two_le_alpha h.1; omega)
    h.alpha_sq_le_p (ℓ : ZMod (s n i))
  have h1' : tableD (s n i) (t n i) (alpha n) (p n) (ℓ : ZMod (s n i)) ≤ 2 ^ p n := h1
  refine fits_real_of_le (by positivity) ?_
  calc tableD (s n i) (t n i) (alpha n) (p n) (ℓ : ZMod (s n i)) * 2 ^ (4 * p n)
      ≤ 2 ^ p n * 2 ^ (4 * p n) := mul_le_mul_of_nonneg_right h1' (by positivity)
    _ = 2 ^ (5 * p n) := by rw [← pow_add]; ring_nf
    _ < 2 ^ (w - 1) := pow_lt_pow_right₀ (by norm_num) (by omega)

/-- The record width of the band at `w ≥ 9p + 2`. -/
theorem band_prec_w (h : Big n) {w : ℕ} (hw9 : 9 * p n + 2 ≤ w) :
    BandPrec n (1 / (32 * (p n : ℝ))) w := by
  refine band_prec h h.band_width ?_
  have hp13 := h.thirteen_le_p
  have hpR : (0 : ℝ) < p n := by positivity
  have e : 6 / (1 / (32 * (p n : ℝ))) + 1 = 192 * p n + 1 := by field_simp; ring
  rw [e]
  have h1 : (192 * p n + 1 : ℕ) < 2 ^ (4 * p n + 1) := by
    calc 192 * p n + 1 < 2 ^ 8 * (p n + 1) := by omega
      _ ≤ 2 ^ 8 * 2 ^ p n := Nat.mul_le_mul_left _ (Nat.lt_two_pow_self)
      _ = 2 ^ (p n + 8) := by rw [← pow_add]; ring_nf
      _ ≤ 2 ^ (4 * p n + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h2 : ((192 * p n + 1 : ℕ) : ℝ) * 2 ^ (5 * p n) < 2 ^ (4 * p n + 1) * 2 ^ (5 * p n) :=
    mul_lt_mul_of_pos_right (by exact_mod_cast h1) (by positivity)
  have h3 : (2 : ℝ) ^ (4 * p n + 1) * 2 ^ (5 * p n) ≤ 2 ^ (w - 1) := by
    rw [← pow_add]; exact pow_le_pow_right₀ (by norm_num) (by omega)
  push_cast at h2
  linarith

end Sizes

end

end IntegerMultBounds.MathlibTM2.Fast
