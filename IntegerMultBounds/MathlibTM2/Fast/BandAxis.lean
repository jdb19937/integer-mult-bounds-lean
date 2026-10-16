module

public import IntegerMultBounds.MathlibTM2.Fast.BandLineSpec

/-!
# The banded `B̃₀` along the innermost axis of a padded box

`bandAxisP` runs the banded line `bandLineP` while `src` is nonempty, collecting the outputs
(reversed) on `dst`, and moves them back onto `src`, as `rsbAxisP` does for the Neumann line.

* `BandAxisCfg`: the line registers configured for one axis: the tables `bo`, `hf`, `df`,
  `dtab`, the constants on `smwn` and `bx`, the counters and the empty scratch registers.
* `BandLineOk`: the record-width conditions of one line.
* `band_axis_runs`: `src = cstream (lines.flatten)` becomes `cstream (lines.flatMap bandLineG)`.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Fast

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.NLogN (rowIndex)

set_option linter.unusedSimpArgs false

noncomputable section

/-- The line registers configured for the banded line of one axis. -/
structure BandAxisCfg {A : ℕ} (ρ : RsbR → List (Fin (A + 4))) (w P s t B : ℕ)
    (Lc Uc : List (List ℤ)) (rcs Dl : List ℤ) (cin cout : ℤ) : Prop where
  ready : RsbReady ρ w P
  dst : ρ .dst = []
  msk : ρ .msk = (rsbMask s t).map bitSymbol
  smwn : ρ .smwn = csyms A w ⟨cin, 0⟩
  bx : ρ .bx = csyms A w ⟨cout, 0⟩
  bo : ρ .bo = cstream A w (Lc.map colC).flatten
  hf : ρ .hf = cstream A w (Uc.map colC).flatten
  df : ρ .df = cstream A w (rcs.map fun x => (⟨x, 0⟩ : GaussianInt))
  dtab : ρ .dtab = cstream A w (Dl.map fun d => (⟨d, 0⟩ : GaussianInt))
  padc : (ρ .padc).length = (t - s) * w
  tswn : (ρ .tswn).length = (s + 1) / 2 * w
  m2wn : (ρ .m2wn).length = s / 2
  kn : (ρ .kn).length = (s + 1) / 2 - s / 2
  sn : (ρ .sn).length = s
  mwn : (ρ .mwn).length = B * w
  m2n : (ρ .m2n).length = B
  ms : ρ .ms = []
  sr : ρ .sr = []
  sel : ρ .sel = []
  vk : ρ .vk = []
  ya : ρ .ya = []
  xs : ρ .xs = []
  nv : ρ .nv = []
  tK : ρ .tK = []
  tC : ρ .tC = []
  ac2 : ρ .ac2 = []
  ef : ρ .ef = []
  tb : ρ .tb = []
  dout : ρ .dout = []
  hv : ρ .hv = []
  pr : ρ .pr = []
  ac : ρ .ac = []
  tA : ρ .tA = []
  tJ : ρ .tJ = []
  b1 : ρ .b1 = []
  tL : ρ .tL = []
  xa : ρ .xa = []
  hc : ρ .hc = []

/-- A configuration survives changing the box register. -/
lemma BandAxisCfg.with_src {A : ℕ} {ρ : RsbR → List (Fin (A + 4))} {w P s t B : ℕ}
    {Lc Uc : List (List ℤ)} {rcs Dl : List ℤ} {cin cout : ℤ}
    (h : BandAxisCfg ρ w P s t B Lc Uc rcs Dl cin cout) (l : List (Fin (A + 4))) :
    BandAxisCfg (Function.update ρ .src l) w P s t B Lc Uc rcs Dl cin cout := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18,
    h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36,
    h37⟩ := h
  exact ⟨h0.update .src (fun c => by simp) l, by simp [h1], by simp [h2], by simp [h3],
    by simp [h4], by simp [h5], by simp [h6], by simp [h7], by simp [h8], by simp [h9],
    by simp [h10], by simp [h11], by simp [h12], by simp [h13], by simp [h14], by simp [h15],
    by simp [h16], by simp [h17], by simp [h18], by simp [h19], by simp [h20], by simp [h21],
    by simp [h22], by simp [h23], by simp [h24], by simp [h25], by simp [h26], by simp [h27],
    by simp [h28], by simp [h29], by simp [h30], by simp [h31], by simp [h32], by simp [h33],
    by simp [h34], by simp [h35], by simp [h36], by simp [h37]⟩

/-- The tables of one axis: shapes and record widths. -/
structure BandTabOk (w s B : ℕ) (Lc Uc : List (List ℤ)) (rcs Dl : List ℤ) (cin cout : ℤ) : Prop where
  lenL : Lc.length = s
  lenU : Uc.length = s
  colL : ∀ c ∈ Lc, c.length = B
  colU : ∀ c ∈ Uc, c.length = B
  lenR : rcs.length = s
  lenD : Dl.length = s
  fitL : ∀ c ∈ Lc, ∀ x ∈ c, Fits w (⟨x, 0⟩ : GaussianInt)
  fitU : ∀ c ∈ Uc, ∀ x ∈ c, Fits w (⟨x, 0⟩ : GaussianInt)
  fitR : ∀ x ∈ rcs, Fits w (⟨x, 0⟩ : GaussianInt)
  fitD : ∀ d ∈ Dl, Fits w (⟨d, 0⟩ : GaussianInt)
  fitI : Fits w (⟨cin, 0⟩ : GaussianInt)
  fitO : Fits w (⟨cout, 0⟩ : GaussianInt)

/-- The record-width conditions of one line `L`. -/
def BandLineOk (w P s t B : ℕ) [NeZero s] (Lc Uc : List (List ℤ)) (rcs : List ℤ) (cin cout : ℤ)
    (L : List GaussianInt) : Prop :=
  L.length = t ∧ (∀ x ∈ L, Fits w x) ∧
    (∀ j < s, Fits w ((Mult.BandList.bandPend P Lc
      (bandInVec P s t cin (rsbVec (t := t) L) ++ List.replicate B 0) j).headD 0)) ∧
    (∀ j < s, Fits w ((Mult.BandList.bandPendB P Uc rcs
      ((Mult.BandList.fwdZC P Lc (bandInVec P s t cin (rsbVec (t := t) L) ++
        List.replicate B 0)).reverse ++ List.replicate B 0) j).headD 0)) ∧
    (∀ j < s, Fits w (tdivN P ((Mult.BandList.bandPendB P Uc rcs
      ((Mult.BandList.fwdZC P Lc (bandInVec P s t cin (rsbVec (t := t) L) ++
        List.replicate B 0)).reverse ++ List.replicate B 0) j).headD 0 * ⟨rcs.getD j 0, 0⟩))) ∧
    (∀ a ∈ Mult.BandFactor.unfoldList
      (bandSolveVec P B Lc Uc rcs (bandInVec P s t cin (rsbVec (t := t) L))), Fits w a) ∧
    (∀ a ∈ Mult.BandFactor.unfoldList
      (bandSolveVec P B Lc Uc rcs (bandInVec P s t cin (rsbVec (t := t) L))),
        Fits w (tdivN P (a * ⟨cout, 0⟩)))

/-- The line map of the tape line, for any tables. -/
def bandLineT (P s t B : ℕ) [NeZero s] (Lc Uc : List (List ℤ)) (rcs Dl : List ℤ) (cin cout : ℤ)
    (L : List GaussianInt) : List GaussianInt :=
  bandOutVec P cout Dl (bandSolveVec P B Lc Uc rcs (bandInVec P s t cin (rsbVec (t := t) L))) ++
    List.replicate (t - s) 0

theorem length_bandLineT (P s t B : ℕ) [NeZero s] (Lc Uc : List (List ℤ)) (rcs Dl : List ℤ)
    (cin cout : ℤ) (hLc : Lc.length = s) (hUc : Uc.length = s) (hrcs : rcs.length = s) (hDl : Dl.length = s)
    (hst : s ≤ t) (L : List GaussianInt) :
    (bandLineT P s t B Lc Uc rcs Dl cin cout L).length = t := by
  have hb : (bandInVec P s t cin (rsbVec (t := t) L)).length = s := by
    simp [bandInVec, length_foldList, length_rsbArr]
  have hx : (bandSolveVec P B Lc Uc rcs (bandInVec P s t cin (rsbVec (t := t) L))).length = s := by
    have hf : (Mult.BandList.fwdZC P Lc (bandInVec P s t cin (rsbVec (t := t) L) ++
        List.replicate B 0)).length = s := by
      rw [length_fwdZC P Lc _ (by simp [hb]; omega), hLc]
    rw [bandSolveVec, List.length_reverse, length_bwdZC P Uc rcs _ (by omega) (by simp [hf]; omega), hUc]
  simp [bandLineT, bandOutVec, length_unfoldList, hx, hDl]; omega

variable {T Q A : ℕ} {U : Type} {P : Type}

variable (rg : RsbR → Fin T) {ι : Fin 64 → Fin T} (hι : Function.Injective ι) (hT : 64 ≤ T)
  (hQ : SS.states ≤ Q)

/-- The banded `B̃₀` along the innermost axis. -/
def bandAxisP : Pr P T Q A U :=
  .seq (rsbWhile (rg .src) (bandLineP rg hι hT hQ)) (moveR (rg .dst) (rg .src) id)

/-- The step bound of `bandAxisP` on `n` lines. -/
def bandAxisCost (T w s t B n : ℕ) : ℕ := n * (bandLineCost T w s t B + 2) + 2 * (n * t * w) + 4

variable {body : P → Pr P T Q A U} {rg}

/-- **The banded `B̃₀` along the innermost axis.** -/
theorem band_axis_runs (hrg : Function.Injective rg) (hdisj : ∀ r j, rg r ≠ ι j) (hA : 96 ≤ A)
    {w P s t B : ℕ} [NeZero s] [NeZero t] (hst : s < t) (hw : 1 ≤ w) (hp : P ≤ w)
    (Lc Uc : List (List ℤ)) (rcs Dl : List ℤ) (cin cout : ℤ)
    (htab : BandTabOk w s B Lc Uc rcs Dl cin cout)
    (lines : List (List GaussianInt))
    (hok : ∀ L ∈ lines, BandLineOk w P s t B Lc Uc rcs cin cout L)
    (σ : RsbR → List (Fin (A + 4))) (hcfg : BandAxisCfg σ w P s t B Lc Uc rcs Dl cin cout)
    (hsrc : σ .src = cstream A w lines.flatten) :
    RsbRuns body rg ι (bandAxisP rg hι hT hQ) σ
      (Function.update σ .src (cstream A w (lines.flatMap (bandLineT P s t B Lc Uc rcs Dl cin cout))))
      (bandAxisCost T w s t B lines.length) := by
  have ht : 1 ≤ t := by omega
  set g := bandLineT P s t B Lc Uc rcs Dl cin cout with hg
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : ℕ → RsbR → List (Fin (A + 4)), Ψ = fun j =>
      Function.update (Function.update σ .src (cstream A w (lines.drop j).flatten)) .dst
        (cstream A w ((lines.take j).flatMap g)).reverse := ⟨_, rfl⟩
  have hbody : ∀ j < lines.length, RsbRuns body rg ι (bandLineP rg hι hT hQ) (Ψ j) (Ψ (j + 1))
      (bandLineCost T w s t B) := by
    intro j hj
    obtain ⟨hlen, hfx, hf1, hf2, hf3, hf4, hf5⟩ := hok lines[j] (List.getElem_mem hj)
    have hsrcj : Ψ j .src = cstream A w (rsbArr (rsbVec (t := t) lines[j])) ++
        cstream A w (lines.drop (j + 1)).flatten := by
      rw [rsbArr_rsbVec _ hlen, ← cstream_append, ← List.flatten_cons,
        ← List.drop_eq_getElem_cons hj]
      simp [hΨ]
    have hc := hcfg.with_src (cstream A w (lines.drop j).flatten)
    have hΨj : Ψ j = Function.update (Function.update σ .src (cstream A w (lines.drop j).flatten))
        .dst (cstream A w ((lines.take j).flatMap g)).reverse := by rw [hΨ]
    refine (band_line_runs rg hrg hdisj hι hT hQ hA hst (Ψ j)
      (by rw [hΨj]; exact hc.ready.update .dst (fun c => by simp) _) hw hp (rsbVec lines[j])
      (fun i => by
        simp only [rsbVec]
        by_cases hi : i.val < lines[j].length
        · rw [List.getD_eq_getElem _ _ hi]; exact hfx _ (List.getElem_mem hi)
        · rw [List.getD_eq_default _ _ (by omega)]; exact ⟨by simp, by simp⟩)
      cin cout htab.fitI htab.fitO Lc Uc rcs Dl htab.lenL htab.lenU htab.colL htab.colU htab.lenR htab.lenD
      htab.fitL htab.fitU htab.fitR htab.fitD hf1 hf2 hf3 hf4 hf5 _ hsrcj
      (by simp [hΨj, hcfg.msk]) (by simp [hΨj, hcfg.smwn]) (by simp [hΨj, hcfg.bx])
      (by simp [hΨj, hcfg.bo]) (by simp [hΨj, hcfg.hf]) (by simp [hΨj, hcfg.df])
      (by simp [hΨj, hcfg.dtab]) (by simp [hΨj, hcfg.padc]) (by simp [hΨj, hcfg.tswn])
      (by simp [hΨj, hcfg.m2wn]) (by simp [hΨj, hcfg.kn]) (by simp [hΨj, hcfg.sn])
      (by simp [hΨj, hcfg.mwn]) (by simp [hΨj, hcfg.m2n]) (by simp [hΨj, hcfg.ms])
      (by simp [hΨj, hcfg.sr]) (by simp [hΨj, hcfg.sel]) (by simp [hΨj, hcfg.vk])
      (by simp [hΨj, hcfg.ya]) (by simp [hΨj, hcfg.xs]) (by simp [hΨj, hcfg.nv])
      (by simp [hΨj, hcfg.tK]) (by simp [hΨj, hcfg.tC]) (by simp [hΨj, hcfg.ac2])
      (by simp [hΨj, hcfg.ef]) (by simp [hΨj, hcfg.tb]) (by simp [hΨj, hcfg.dout])
      (by simp [hΨj, hcfg.hv]) (by simp [hΨj, hcfg.pr]) (by simp [hΨj, hcfg.ac])
      (by simp [hΨj, hcfg.tA]) (by simp [hΨj, hcfg.tJ]) (by simp [hΨj, hcfg.b1])
      (by simp [hΨj, hcfg.tL]) (by simp [hΨj, hcfg.xa]) (by simp [hΨj, hcfg.hc])).congr ?_
    have htk : (lines.take (j + 1)).flatMap g = (lines.take j).flatMap g ++ g lines[j] := by
      rw [List.take_add_one, List.getElem?_eq_getElem hj, Option.toList_some, List.flatMap_append]
      simp
    funext r
    by_cases hr : r = .dst
    · subst hr
      simp only [hΨ, Function.update_self, Function.update_of_ne (show RsbR.dst ≠ .src by decide)]
      rw [htk]; simp only [reverse_cstream_append, hg, bandLineT, List.append_assoc]
    · cases r <;> first | exact absurd rfl hr | simp [hΨ]
  have H := rsb_while_runs (body := body) hdisj (ra := .src) (bandLineP rg hι hT hQ) Ψ
    lines.length (bandLineCost T w s t B)
    (fun j hj => by
      obtain ⟨hlen, -⟩ := hok lines[j] (List.getElem_mem hj)
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
    funext r; cases r <;> simp [hΨ, hsrc, hcfg.dst]
  rw [e₀] at H
  have H₂ := rsb_moveR_runs (body := body) (ι := ι) hrg (a := .dst) (b := .src) (by decide)
    (Ψ lines.length)
  refine ((RsbRuns.seq hdisj H H₂).congr ?_).mono ?_
  · funext r; cases r <;> simp [hΨ, hcfg.dst]
  · have hlg : ((lines.take lines.length).flatMap g).length = lines.length * t := by
      rw [List.take_length, rsb_length_flatMap_const _ _ t
        (fun L => length_bandLineT P s t B Lc Uc rcs Dl cin cout htab.lenL htab.lenU htab.lenR htab.lenD hst.le L)]
    simp only [hΨ, Function.update_self, List.length_reverse, length_cstream, hlg]
    unfold bandAxisCost
    nlinarith

end

end IntegerMultBounds.MathlibTM2.Fast
