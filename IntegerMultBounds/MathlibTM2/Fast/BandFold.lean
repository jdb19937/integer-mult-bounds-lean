module

public import IntegerMultBounds.MathlibTM2.Fast.BandFactor
public import IntegerMultBounds.MathlibTM2.Mult.BandFoldList

/-!
# Folding a line on tapes

Record moves between registers for the fold and unfold of a line: one record moves
through `ac2` keeping its symbol order; the interleave loop alternates records of two
registers; the deinterleave loop splits a register into its even and odd records.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Fast

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.Node


variable {T Q A : ℕ} {U : Type} {P : Type}

section Programs

variable (rg : RsbR → Fin T)

/-- Move the top record of `x` onto `y`, keeping its symbol order. -/
def bandRec1P (x y : RsbR) : Pr P T Q A U :=
  .seq (rsbMv (rg (.cm .wn)) (rg .tC) (rg x) (rg .ac2)) (moveR (rg .ac2) (rg y) id)

/-- Alternate records of `a` and `b` onto `z`, one pair per symbol of `n`. -/
def bandILeaveP (a b z n tn : RsbR) : Pr P T Q A U :=
  rsbRep (rg n) (rg tn) (.seq (bandRec1P rg a z) (bandRec1P rg b z))

/-- Split records of `x` alternately onto `e` and `o`, one pair per symbol of `n`. -/
def bandDeILeaveP (x e o n tn : RsbR) : Pr P T Q A U :=
  rsbRep (rg n) (rg tn) (.seq (bandRec1P rg x e) (bandRec1P rg x o))

/-- Fold the line on `sel` onto `vk`: first half to `ya` in order, the rest reversed onto
`xs`, pairs interleaved onto `nv`, the odd last record, then `nv` reversed onto `vk`. -/
def bandFoldLineP : Pr P T Q A U :=
  .seq (rsbMv (rg .tswn) (rg .tC) (rg .sel) (rg .ac2)) (.seq (moveR (rg .ac2) (rg .ya) id)
  (.seq (bandRevP rg .sel .xs (.cm .wn) .m2wn .tK)
  (.seq (bandILeaveP rg .ya .xs .nv .m2wn .tK)
  (.seq (rsbRep (rg .kn) (rg .tK) (bandRec1P rg .ya .nv))
  (bandRevP rg .nv .vk (.cm .wn) .sn .tK)))))

/-- Unfold the line on `dout` onto `sel`: even and odd records split, the odd ones kept in
reverse, the even ones reversed back on top. -/
def bandUnfoldLineP : Pr P T Q A U :=
  .seq (bandDeILeaveP rg .dout .ya .xs .m2wn .tK)
  (.seq (rsbRep (rg .kn) (rg .tK) (bandRec1P rg .dout .ya))
  (.seq (moveR (rg .xs) (rg .ac2) id) (.seq (moveR (rg .ac2) (rg .sel) id)
  (.seq (bandRevP rg .ya .sel (.cm .wn) .m2wn .tK) (bandRevP rg .ya .sel (.cm .wn) .kn .tK)))))

end Programs

section Contracts

variable {body : P → Pr P T Q A U} {rg : RsbR → Fin T} {ι : Fin 64 → Fin T}

theorem band_rec1_runs (hrg : Function.Injective rg) (hdisj : ∀ r j, rg r ≠ ι j) {x y : RsbR}
    (hd : [x, y, .cm .wn, .tC, .ac2].Nodup) {w : ℕ} (σ : RsbR → List (Fin (A + 4)))
    (r : GaussianInt) (X : List (Fin (A + 4))) (hx : σ x = csyms A w r ++ X)
    (hwn : (σ (.cm .wn)).length = w) (htC : σ .tC = []) (hac2 : σ .ac2 = []) :
    RsbRuns body rg ι (bandRec1P rg x y) σ
      (Function.update (Function.update σ x X) y (csyms A w r ++ σ y)) (6 * w + 6) := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hd
  obtain ⟨⟨hxy, hxw, hxC, hxa⟩, ⟨hyw, hyC, hya⟩, ⟨hwC, hwa⟩, hCa, -⟩ := hd
  have hd4 : [RsbR.cm .wn, RsbR.tC, x, RsbR.ac2].Nodup := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil,
      and_true]
    exact ⟨⟨hwC, Ne.symm hxw, hwa⟩, ⟨Ne.symm hxC, hCa⟩, hxa, not_false⟩
  have h₁ := rsb_mv_runs (body := body) (ι := ι) hrg (c := .cm .wn) (t := .tC) (x := x) (y := .ac2)
    hd4 σ htC (by rw [hwn, hx]; simp [csyms])
  rw [hwn, hx, take_csyms_append, drop_csyms_append, hac2, List.append_nil] at h₁
  have h₂ := rsb_moveR_runs (body := body) (ι := ι) hrg (a := .ac2) (b := y) (Ne.symm hya)
    (Function.update (Function.update σ x X) .ac2 (csyms A w r).reverse)
  refine ((RsbRuns.seq hdisj h₁ h₂).congr ?_).mono ?_
  · funext z
    simp only [Function.update_apply]
    split_ifs <;> simp_all
  · simp; omega

theorem interleave_snoc {α : Type*} (x y : α) : ∀ (l₁ l₂ : List α), l₁.length = l₂.length →
    Mult.BandFactor.interleave (l₁ ++ [x]) (l₂ ++ [y]) =
      Mult.BandFactor.interleave l₁ l₂ ++ [x, y]
  | [], [], _ => rfl
  | a :: l₁, b :: l₂, h => by
    simp only [List.cons_append, Mult.BandFactor.interleave]
    rw [interleave_snoc x y l₁ l₂ (by simpa using h)]
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h

/-- One pair of the interleave loop. -/
theorem band_ileave_step (hrg : Function.Injective rg) (hdisj : ∀ r j, rg r ≠ ι j)
    {a b z : RsbR} (hd : [a, b, z, .cm .wn, .tC, .ac2].Nodup) {w : ℕ}
    (ρ : RsbR → List (Fin (A + 4))) (x y : GaussianInt) (RA RB : List (Fin (A + 4)))
    (ha : ρ a = csyms A w x ++ RA) (hb : ρ b = csyms A w y ++ RB)
    (hwn : (ρ (.cm .wn)).length = w) (htC : ρ .tC = []) (hac2 : ρ .ac2 = []) :
    RsbRuns body rg ι (.seq (bandRec1P rg a z) (bandRec1P rg b z)) ρ
      (Function.update (Function.update (Function.update ρ a RA) b RB) z
        (csyms A w y ++ csyms A w x ++ ρ z)) (2 * (6 * w + 6)) := by
  have hd' := hd
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hd'
  obtain ⟨⟨hab, haz, haw, haC, haa⟩, ⟨hbz, hbw, hbC, hba⟩, ⟨hzw, hzC, hza⟩, ⟨hwC, hwa⟩, hCa, -⟩ := hd'
  have h₁ := band_rec1_runs (body := body) (ι := ι) hrg hdisj (x := a) (y := z) (w := w)
    (by simp [haz, haw, haC, haa, hzw, hzC, hza, hwC, hwa, hCa]) ρ x RA ha hwn htC hac2
  have h₂ := band_rec1_runs (body := body) (ι := ι) hrg hdisj (x := b) (y := z) (w := w)
    (by simp [hbz, hbw, hbC, hba, hzw, hzC, hza, hwC, hwa, hCa])
    (Function.update (Function.update ρ a RA) z (csyms A w x ++ ρ z)) y RB
    (by rw [Function.update_of_ne hbz, Function.update_of_ne (Ne.symm hab), hb])
    (by rw [Function.update_of_ne (Ne.symm hzw), Function.update_of_ne (Ne.symm haw), hwn])
    (by rw [Function.update_of_ne (Ne.symm hzC), Function.update_of_ne (Ne.symm haC), htC])
    (by rw [Function.update_of_ne (Ne.symm hza), Function.update_of_ne (Ne.symm haa), hac2])
  refine ((RsbRuns.seq hdisj h₁ h₂).congr ?_).mono (by omega)
  funext r
  by_cases hrz : r = z
  · subst hrz; simp
  by_cases hrb : r = b
  · subst hrb; simp [Function.update_of_ne hrz]
  by_cases hra : r = a
  · subst hra; simp [Function.update_of_ne hrz, Function.update_of_ne hrb]
  simp [Function.update_of_ne hrz, Function.update_of_ne hrb, Function.update_of_ne hra]

/-- **Interleave loop.** -/
theorem band_ileave_runs (hrg : Function.Injective rg) (hdisj : ∀ r j, rg r ≠ ι j)
    {a b z n tn : RsbR} (hd : [a, b, z, n, tn, .cm .wn, .tC, .ac2].Nodup) {w : ℕ}
    (σ : RsbR → List (Fin (A + 4))) (as bs : List GaussianInt) (RA RB : List (Fin (A + 4)))
    (hlen : as.length = bs.length) (hn : (σ n).length = as.length)
    (ha : σ a = cstream A w as ++ RA) (hb : σ b = cstream A w bs ++ RB)
    (hwn : (σ (.cm .wn)).length = w) (htC : σ .tC = []) (hac2 : σ .ac2 = []) (htn : σ tn = []) :
    RsbRuns body rg ι (bandILeaveP rg a b z n tn) σ
      (Function.update (Function.update (Function.update σ a RA) b RB) z
        (cstream A w (Mult.BandFactor.interleave as bs).reverse ++ σ z))
      (as.length * (2 * (6 * w + 6) + 6) + 4) := by
  have hd6 : [a, b, z, RsbR.cm .wn, RsbR.tC, RsbR.ac2].Nodup := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hd ⊢
    tauto
  have hd' := hd
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hd'
  obtain ⟨⟨hab, haz, han, hat, haw, haC, haa⟩, ⟨hbz, hbn, hbt, hbw, hbC, hba⟩,
    ⟨hzn, hzt, hzw, hzC, hza⟩, ⟨hnt, hnw, hnC, hna⟩, ⟨htw, htC', hta⟩, -, -, -⟩ := hd'
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : ℕ → RsbR → List (Fin (A + 4)), Ψ = fun j =>
      Function.update (Function.update (Function.update σ a (cstream A w (as.drop j) ++ RA)) b
        (cstream A w (bs.drop j) ++ RB)) z
        (cstream A w (Mult.BandFactor.interleave (as.take j) (bs.take j)).reverse ++ σ z) := ⟨_, rfl⟩
  have hbody : ∀ j < (σ n).length, ∀ X Y, RsbRuns body rg ι
      (.seq (bandRec1P rg a z) (bandRec1P rg b z))
      (rsbUpd2 (Ψ j) n X tn Y) (rsbUpd2 (Ψ (j + 1)) n X tn Y) (2 * (6 * w + 6)) := by
    intro j hj X Y
    rw [hn] at hj
    have hjb : j < bs.length := by omega
    have hda : as.drop j = as[j] :: as.drop (j + 1) := List.drop_eq_getElem_cons hj
    have hdb : bs.drop j = bs[j] :: bs.drop (j + 1) := List.drop_eq_getElem_cons hjb
    have h := band_ileave_step (body := body) (ι := ι) hrg hdisj hd6 (w := w)
      (rsbUpd2 (Ψ j) n X tn Y) as[j] bs[j] (cstream A w (as.drop (j + 1)) ++ RA)
      (cstream A w (bs.drop (j + 1)) ++ RB)
      (by
        rw [show rsbUpd2 (Ψ j) n X tn Y a = cstream A w (as.drop j) ++ RA by
          simp [rsbUpd2, hΨ, Function.update_of_ne han, Function.update_of_ne hat,
            Function.update_of_ne haz, Function.update_of_ne hab], hda, cstream_cons, List.append_assoc])
      (by
        rw [show rsbUpd2 (Ψ j) n X tn Y b = cstream A w (bs.drop j) ++ RB by
          simp [rsbUpd2, hΨ, Function.update_of_ne hbn, Function.update_of_ne hbt,
            Function.update_of_ne hbz], hdb, cstream_cons, List.append_assoc])
      (by simp [rsbUpd2, hΨ, Function.update_of_ne (Ne.symm hnw), Function.update_of_ne (Ne.symm htw),
        Function.update_of_ne (Ne.symm hzw), Function.update_of_ne (Ne.symm hbw),
        Function.update_of_ne (Ne.symm haw), hwn])
      (by simp [rsbUpd2, hΨ, Function.update_of_ne (Ne.symm hnC), Function.update_of_ne (Ne.symm htC'),
        Function.update_of_ne (Ne.symm hzC), Function.update_of_ne (Ne.symm hbC),
        Function.update_of_ne (Ne.symm haC), htC])
      (by simp [rsbUpd2, hΨ, Function.update_of_ne (Ne.symm hna), Function.update_of_ne (Ne.symm hta),
        Function.update_of_ne (Ne.symm hza), Function.update_of_ne (Ne.symm hba),
        Function.update_of_ne (Ne.symm haa), hac2])
    refine h.congr ?_
    have hti : Mult.BandFactor.interleave (as.take (j + 1)) (bs.take (j + 1)) =
        Mult.BandFactor.interleave (as.take j) (bs.take j) ++ [as[j], bs[j]] := by
      rw [List.take_succ_eq_append_getElem hj, List.take_succ_eq_append_getElem hjb,
        interleave_snoc _ _ _ _ (by simp; omega)]
    funext r
    by_cases hrz : r = z
    · subst hrz
      simp [rsbUpd2, hΨ, Function.update_of_ne hzn, Function.update_of_ne hzt, hti,
        ]
    by_cases hrb : r = b
    · subst hrb; simp [rsbUpd2, hΨ, Function.update_of_ne hrz, Function.update_of_ne hbn,
        Function.update_of_ne hbt]
    by_cases hra : r = a
    · subst hra; simp [rsbUpd2, hΨ, Function.update_of_ne hrz, Function.update_of_ne hrb,
        Function.update_of_ne han, Function.update_of_ne hat]
    simp only [rsbUpd2, hΨ, Function.update_apply, hrz, hrb, hra, ite_false]
  have h := rsb_rep_runs hrg hdisj (ra := n) (rt := tn) hnt _ (σ n) Ψ _ hbody
  refine (h.congr_pre ?_ |>.congr ?_).mono ?_
  · funext r
    by_cases hrz : r = z
    · subst hrz; simp [rsbUpd2, hΨ, Function.update_of_ne hzn, Function.update_of_ne hzt,
        Mult.BandFactor.interleave]
    by_cases hrb : r = b
    · subst hrb; simp [rsbUpd2, hΨ, Function.update_of_ne hrz, Function.update_of_ne hbn,
        Function.update_of_ne hbt, hb]
    by_cases hra : r = a
    · subst hra; simp [rsbUpd2, hΨ, Function.update_of_ne hrz, Function.update_of_ne hrb,
        Function.update_of_ne han, Function.update_of_ne hat, ha]
    by_cases hrt : r = tn
    · subst hrt; simp [rsbUpd2, htn, 
        ]
    by_cases hrn : r = n
    · subst hrn; simp [rsbUpd2, Function.update_of_ne hrt, 
        ]
    simp [rsbUpd2, hΨ, hrz, hrb, hra, hrt, hrn]
  · funext r
    by_cases hrz : r = z
    · subst hrz; simp [rsbUpd2, hΨ, Function.update_of_ne hzn, Function.update_of_ne hzt, hn,
        List.take_of_length_le]
      rw [List.take_of_length_le (by omega)]
    by_cases hrb : r = b
    · subst hrb; simp [rsbUpd2, hΨ, Function.update_of_ne hrz, Function.update_of_ne hbn,
        Function.update_of_ne hbt, hn, List.drop_of_length_le (by omega : bs.length ≤ as.length)]
    by_cases hra : r = a
    · subst hra; simp [rsbUpd2, hΨ, Function.update_of_ne hrz, Function.update_of_ne hrb,
        Function.update_of_ne han, Function.update_of_ne hat, hn]
    by_cases hrt : r = tn
    · subst hrt; simp [rsbUpd2, htn, Function.update_of_ne (Ne.symm hat), Function.update_of_ne (Ne.symm hbt),
        Function.update_of_ne (Ne.symm hzt)]
    by_cases hrn : r = n
    · subst hrn; simp [rsbUpd2, Function.update_of_ne hrt, Function.update_of_ne (Ne.symm han),
        Function.update_of_ne (Ne.symm hbn), Function.update_of_ne (Ne.symm hzn)]
    simp [rsbUpd2, hΨ, hrz, hrb, hra, hrt, hrn]
  · rw [hn]

/-- One pair of the deinterleave loop. -/
theorem band_deileave_step (hrg : Function.Injective rg) (hdisj : ∀ r j, rg r ≠ ι j)
    {x e o : RsbR} (hd : [x, e, o, .cm .wn, .tC, .ac2].Nodup) {w : ℕ}
    (ρ : RsbR → List (Fin (A + 4))) (a b : GaussianInt) (R : List (Fin (A + 4)))
    (hx : ρ x = csyms A w a ++ csyms A w b ++ R)
    (hwn : (ρ (.cm .wn)).length = w) (htC : ρ .tC = []) (hac2 : ρ .ac2 = []) :
    RsbRuns body rg ι (.seq (bandRec1P rg x e) (bandRec1P rg x o)) ρ
      (Function.update (Function.update (Function.update ρ x R) e (csyms A w a ++ ρ e)) o
        (csyms A w b ++ ρ o)) (2 * (6 * w + 6)) := by
  have hd' := hd
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hd'
  obtain ⟨⟨hxe, hxo, hxw, hxC, hxa⟩, ⟨heo, hew, heC, hea⟩, ⟨how, hoC, hoa⟩, ⟨hwC, hwa⟩, hCa, -⟩ := hd'
  have h₁ := band_rec1_runs (body := body) (ι := ι) hrg hdisj (x := x) (y := e) (w := w)
    (by simp [hxe, hxw, hxC, hxa, hew, heC, hea, hwC, hwa, hCa]) ρ a (csyms A w b ++ R)
    (by rw [hx, List.append_assoc]) hwn htC hac2
  have h₂ := band_rec1_runs (body := body) (ι := ι) hrg hdisj (x := x) (y := o) (w := w)
    (by simp [hxo, hxw, hxC, hxa, how, hoC, hoa, hwC, hwa, hCa])
    (Function.update (Function.update ρ x (csyms A w b ++ R)) e (csyms A w a ++ ρ e)) b R
    (by rw [Function.update_of_ne hxe, Function.update_self])
    (by rw [Function.update_of_ne (Ne.symm hew), Function.update_of_ne (Ne.symm hxw), hwn])
    (by rw [Function.update_of_ne (Ne.symm heC), Function.update_of_ne (Ne.symm hxC), htC])
    (by rw [Function.update_of_ne (Ne.symm hea), Function.update_of_ne (Ne.symm hxa), hac2])
  refine ((RsbRuns.seq hdisj h₁ h₂).congr ?_).mono (by omega)
  funext r
  by_cases hro : r = o
  · subst hro; simp [Function.update_of_ne (Ne.symm heo), Function.update_of_ne (Ne.symm hxo)]
  by_cases hre : r = e
  · subst hre; simp [Function.update_of_ne hro, Function.update_of_ne (Ne.symm hxe)]
  by_cases hrx : r = x
  · subst hrx; simp [Function.update_of_ne hro, Function.update_of_ne hre]
  simp [Function.update_of_ne hro, Function.update_of_ne hre, Function.update_of_ne hrx]

/-- **Deinterleave loop.** -/
theorem band_deileave_runs (hrg : Function.Injective rg) (hdisj : ∀ r j, rg r ≠ ι j)
    {x e o n tn : RsbR} (hd : [x, e, o, n, tn, .cm .wn, .tC, .ac2].Nodup) {w : ℕ}
    (σ : RsbR → List (Fin (A + 4))) (as bs : List GaussianInt) (R : List (Fin (A + 4)))
    (hlen : as.length = bs.length) (hn : (σ n).length = as.length)
    (hx : σ x = cstream A w (Mult.BandFactor.interleave as bs) ++ R)
    (hwn : (σ (.cm .wn)).length = w) (htC : σ .tC = []) (hac2 : σ .ac2 = []) (htn : σ tn = []) :
    RsbRuns body rg ι (bandDeILeaveP rg x e o n tn) σ
      (Function.update (Function.update (Function.update σ x R) e
        (cstream A w as.reverse ++ σ e)) o (cstream A w bs.reverse ++ σ o))
      (as.length * (2 * (6 * w + 6) + 6) + 4) := by
  have hd6 : [x, e, o, RsbR.cm .wn, RsbR.tC, RsbR.ac2].Nodup := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hd ⊢
    tauto
  have hd' := hd
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hd'
  obtain ⟨⟨hxe, hxo, hxn, hxt, -⟩, ⟨heo, hen, het, -⟩, ⟨hon, hot, -⟩, ⟨hnt, -⟩, -⟩ := hd'
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : ℕ → RsbR → List (Fin (A + 4)), Ψ = fun j =>
      Function.update (Function.update (Function.update σ x
        (cstream A w (Mult.BandFactor.interleave (as.drop j) (bs.drop j)) ++ R)) e
        (cstream A w (as.take j).reverse ++ σ e)) o (cstream A w (bs.take j).reverse ++ σ o) := ⟨_, rfl⟩
  have hbody : ∀ j < (σ n).length, ∀ X Y, RsbRuns body rg ι
      (.seq (bandRec1P rg x e) (bandRec1P rg x o))
      (rsbUpd2 (Ψ j) n X tn Y) (rsbUpd2 (Ψ (j + 1)) n X tn Y) (2 * (6 * w + 6)) := by
    intro j hj X Y
    rw [hn] at hj
    have hjb : j < bs.length := by omega
    have hda : as.drop j = as[j] :: as.drop (j + 1) := List.drop_eq_getElem_cons hj
    have hdb : bs.drop j = bs[j] :: bs.drop (j + 1) := List.drop_eq_getElem_cons hjb
    have h := band_deileave_step (body := body) (ι := ι) hrg hdisj hd6 (w := w)
      (rsbUpd2 (Ψ j) n X tn Y) as[j] bs[j]
      (cstream A w (Mult.BandFactor.interleave (as.drop (j + 1)) (bs.drop (j + 1))) ++ R)
      (by
        rw [show rsbUpd2 (Ψ j) n X tn Y x = cstream A w (Mult.BandFactor.interleave (as.drop j)
            (bs.drop j)) ++ R by
          simp [rsbUpd2, hΨ, Function.update_of_ne hxn, Function.update_of_ne hxt,
            Function.update_of_ne hxe, Function.update_of_ne hxo], hda, hdb]
        simp [Mult.BandFactor.interleave])
      (by simp only [rsbUpd2, hΨ, Function.update_apply]; split_ifs <;> simp_all)
      (by simp only [rsbUpd2, hΨ, Function.update_apply]; split_ifs <;> simp_all)
      (by simp only [rsbUpd2, hΨ, Function.update_apply]; split_ifs <;> simp_all)
    refine h.congr ?_
    have hta : (as.take (j + 1)).reverse = as[j] :: (as.take j).reverse := by
      rw [List.take_succ_eq_append_getElem hj]; simp
    have htb : (bs.take (j + 1)).reverse = bs[j] :: (bs.take j).reverse := by
      rw [List.take_succ_eq_append_getElem hjb]; simp
    funext r
    by_cases hro : r = o
    · subst hro; simp [rsbUpd2, hΨ, Function.update_of_ne hon, Function.update_of_ne hot, htb,
        ]
    by_cases hre : r = e
    · subst hre; simp [rsbUpd2, hΨ, Function.update_of_ne hro, Function.update_of_ne hen,
        Function.update_of_ne het, hta]
    by_cases hrx : r = x
    · subst hrx; simp [rsbUpd2, hΨ, Function.update_of_ne hro, Function.update_of_ne hre,
        Function.update_of_ne hxn, Function.update_of_ne hxt]
    simp only [rsbUpd2, hΨ, Function.update_apply, hro, hre, hrx, ite_false]
  have h := rsb_rep_runs hrg hdisj (ra := n) (rt := tn) hnt _ (σ n) Ψ _ hbody
  refine (h.congr_pre ?_ |>.congr ?_).mono ?_
  · funext r
    by_cases hro : r = o
    · subst hro; simp [rsbUpd2, hΨ, Function.update_of_ne hon, Function.update_of_ne hot]
    by_cases hre : r = e
    · subst hre; simp [rsbUpd2, hΨ, Function.update_of_ne hro, Function.update_of_ne hen,
        Function.update_of_ne het]
    by_cases hrx : r = x
    · subst hrx; simp [rsbUpd2, hΨ, Function.update_of_ne hro, Function.update_of_ne hre,
        Function.update_of_ne hxn, Function.update_of_ne hxt, hx]
    by_cases hrt : r = tn
    · subst hrt; simp [rsbUpd2, htn, 
        ]
    by_cases hrn : r = n
    · subst hrn; simp [rsbUpd2, Function.update_of_ne hrt, 
        ]
    simp [rsbUpd2, hΨ, hro, hre, hrx, hrt, hrn]
  · funext r
    have hda : as.drop as.length = [] := List.drop_length
    have hdb : bs.drop as.length = [] := List.drop_of_length_le (by omega)
    by_cases hro : r = o
    · subst hro; simp [rsbUpd2, hΨ, Function.update_of_ne hon, Function.update_of_ne hot, hn,
        List.take_of_length_le (by omega : bs.length ≤ as.length)]
    by_cases hre : r = e
    · subst hre; simp [rsbUpd2, hΨ, Function.update_of_ne hro, Function.update_of_ne hen,
        Function.update_of_ne het, hn]
    by_cases hrx : r = x
    · subst hrx; simp [rsbUpd2, hΨ, Function.update_of_ne hro, Function.update_of_ne hre,
        Function.update_of_ne hxn, Function.update_of_ne hxt, hn, hdb, Mult.BandFactor.interleave]
    by_cases hrt : r = tn
    · subst hrt; simp [rsbUpd2, htn, Function.update_of_ne (Ne.symm hxt), Function.update_of_ne (Ne.symm het),
        Function.update_of_ne (Ne.symm hot)]
    by_cases hrn : r = n
    · subst hrn; simp [rsbUpd2, Function.update_of_ne hrt, Function.update_of_ne (Ne.symm hxn),
        Function.update_of_ne (Ne.symm hen), Function.update_of_ne (Ne.symm hon)]
    simp [rsbUpd2, hΨ, hro, hre, hrx, hrt, hrn]
  · rw [hn]

theorem interleave_append_left {α : Type*} (as₂ : List α) : ∀ (as₁ bs : List α),
    as₁.length = bs.length →
    Mult.BandFactor.interleave (as₁ ++ as₂) bs = Mult.BandFactor.interleave as₁ bs ++ as₂
  | [], [], _ => by cases as₂ <;> rfl
  | a :: as₁, b :: bs, h => by
    simp only [List.cons_append, Mult.BandFactor.interleave]
    rw [interleave_append_left as₂ as₁ bs (by simpa using h)]
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h

/-- Move `|n|` records of `x` one by one onto `y`. -/
theorem band_rec1Rep_runs (hrg : Function.Injective rg) (hdisj : ∀ r j, rg r ≠ ι j)
    {x y n tn : RsbR} (hd : [x, y, n, tn, .cm .wn, .tC, .ac2].Nodup) {w : ℕ}
    (σ : RsbR → List (Fin (A + 4))) (l : List GaussianInt) (R : List (Fin (A + 4)))
    (hn : (σ n).length = l.length) (hx : σ x = cstream A w l ++ R)
    (hwn : (σ (.cm .wn)).length = w) (htC : σ .tC = []) (hac2 : σ .ac2 = []) (htn : σ tn = []) :
    RsbRuns body rg ι (rsbRep (rg n) (rg tn) (bandRec1P rg x y)) σ
      (Function.update (Function.update σ x R) y (cstream A w l.reverse ++ σ y))
      (l.length * (6 * w + 6 + 6) + 4) := by
  have hd5 : [x, y, RsbR.cm .wn, RsbR.tC, RsbR.ac2].Nodup := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hd ⊢
    tauto
  have hd' := hd
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hd'
  obtain ⟨⟨hxy, hxn, hxt, -⟩, ⟨hyn, hyt, -⟩, ⟨hnt, -⟩, -⟩ := hd'
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : ℕ → RsbR → List (Fin (A + 4)), Ψ = fun j =>
      Function.update (Function.update σ x (cstream A w (l.drop j) ++ R)) y
        (cstream A w (l.take j).reverse ++ σ y) := ⟨_, rfl⟩
  have hbody : ∀ j < (σ n).length, ∀ X Y, RsbRuns body rg ι (bandRec1P rg x y)
      (rsbUpd2 (Ψ j) n X tn Y) (rsbUpd2 (Ψ (j + 1)) n X tn Y) (6 * w + 6) := by
    intro j hj X Y
    rw [hn] at hj
    have hda : l.drop j = l[j] :: l.drop (j + 1) := List.drop_eq_getElem_cons hj
    have h := band_rec1_runs (body := body) (ι := ι) hrg hdisj (x := x) (y := y) (w := w) hd5
      (rsbUpd2 (Ψ j) n X tn Y) l[j] (cstream A w (l.drop (j + 1)) ++ R)
      (by
        rw [show rsbUpd2 (Ψ j) n X tn Y x = cstream A w (l.drop j) ++ R by
          simp [rsbUpd2, hΨ, Function.update_of_ne hxn, Function.update_of_ne hxt,
            Function.update_of_ne hxy], hda, cstream_cons, List.append_assoc])
      (by simp only [rsbUpd2, hΨ, Function.update_apply]; split_ifs <;> simp_all)
      (by simp only [rsbUpd2, hΨ, Function.update_apply]; split_ifs <;> simp_all)
      (by simp only [rsbUpd2, hΨ, Function.update_apply]; split_ifs <;> simp_all)
    refine h.congr ?_
    have htk : (l.take (j + 1)).reverse = l[j] :: (l.take j).reverse := by
      rw [List.take_succ_eq_append_getElem hj]; simp
    funext r
    by_cases hry : r = y
    · subst hry; simp [rsbUpd2, hΨ, Function.update_of_ne hyn, Function.update_of_ne hyt, htk,
        ]
    by_cases hrx : r = x
    · subst hrx; simp [rsbUpd2, hΨ, Function.update_of_ne hry, Function.update_of_ne hxn,
        Function.update_of_ne hxt]
    simp only [rsbUpd2, hΨ, Function.update_apply, hry, hrx, ite_false]
  have h := rsb_rep_runs hrg hdisj (ra := n) (rt := tn) hnt _ (σ n) Ψ _ hbody
  refine (h.congr_pre ?_ |>.congr ?_).mono ?_
  · funext r
    by_cases hry : r = y
    · subst hry; simp [rsbUpd2, hΨ, Function.update_of_ne hyn, Function.update_of_ne hyt]
    by_cases hrx : r = x
    · subst hrx; simp [rsbUpd2, hΨ, Function.update_of_ne hry, Function.update_of_ne hxn,
        Function.update_of_ne hxt, hx]
    by_cases hrt : r = tn
    · subst hrt; simp [rsbUpd2, htn]
    by_cases hrn : r = n
    · subst hrn; simp [rsbUpd2, Function.update_of_ne hrt, 
        ]
    simp [rsbUpd2, hΨ, hry, hrx, hrt, hrn]
  · funext r
    by_cases hry : r = y
    · subst hry; simp [rsbUpd2, hΨ, Function.update_of_ne hyn, Function.update_of_ne hyt, hn]
    by_cases hrx : r = x
    · subst hrx; simp [rsbUpd2, hΨ, Function.update_of_ne hry, Function.update_of_ne hxn,
        Function.update_of_ne hxt, hn]
    by_cases hrt : r = tn
    · subst hrt; simp [rsbUpd2, htn, Function.update_of_ne (Ne.symm hxt), Function.update_of_ne (Ne.symm hyt)]
    by_cases hrn : r = n
    · subst hrn; simp [rsbUpd2, Function.update_of_ne hrt, Function.update_of_ne (Ne.symm hxn),
        Function.update_of_ne (Ne.symm hyn)]
    simp [rsbUpd2, hΨ, hry, hrx, hrt, hrn]
  · rw [hn]

/-- **Fold a line.** `sel` holding the line `v` (`s` records) becomes empty and `vk`
receives the folded line. -/
theorem band_foldLine_runs (hrg : Function.Injective rg) (hdisj : ∀ r j, rg r ≠ ι j) {w : ℕ}
    (σ : RsbR → List (Fin (A + 4))) (v : List GaussianInt) (hsel : σ .sel = cstream A w v)
    (htswn : (σ .tswn).length = (v.length + 1) / 2 * w) (hm2wn : (σ .m2wn).length = v.length / 2)
    (hkn : (σ .kn).length = (v.length + 1) / 2 - v.length / 2) (hsn : (σ .sn).length = v.length)
    (hwn : (σ (.cm .wn)).length = w) (hvk : σ .vk = []) (hya : σ .ya = []) (hxs : σ .xs = [])
    (hnv : σ .nv = []) (htK : σ .tK = []) (htC : σ .tC = []) (hac2 : σ .ac2 = []) :
    RsbRuns body rg ι (bandFoldLineP rg) σ
      (Function.update (Function.update σ .sel []) .vk (cstream A w (Mult.BandFactor.foldList v)))
      (60 * (v.length + 1) * w + 60 * v.length + 60) := by
  have hsing : ∀ l : List GaussianInt, (l.map fun a => [a]).flatten = l := by
    intro l; induction l <;> simp_all
  set h := (v.length + 1) / 2 with hh
  set r := v.length / 2 with hr
  have hrh : r ≤ h := by omega
  -- the first half
  have h₁ := rsb_mv_runs (body := body) (ι := ι) hrg (c := .tswn) (t := .tC) (x := .sel) (y := .ac2)
    (by decide) σ htC (by rw [htswn, hsel, length_cstream]; exact Nat.mul_le_mul_right _ (by omega))
  have hl1 : (σ .tswn).length = (v.take h).length * w := by rw [htswn]; simp; omega
  have hsplit : σ .sel = cstream A w (v.take h) ++ cstream A w (v.drop h) := by
    rw [hsel, ← cstream_append, List.take_append_drop]
  rw [hl1, hsplit, take_cstream _ _ le_rfl, drop_cstream, List.take_length, List.drop_length,
    Nat.sub_self, zero_mul, List.drop_zero, cstream_nil, List.nil_append, hac2, List.append_nil] at h₁
  set σ₁ := Function.update (Function.update σ .sel (cstream A w (v.drop h))) .ac2
    (cstream A w (v.take h)).reverse
  have h₂ := rsb_moveR_runs (body := body) (ι := ι) hrg (a := .ac2) (b := .ya) (by decide) σ₁
  set σ₂ := Function.update (Function.update σ₁ .ac2 []) .ya ((σ₁ .ac2).reverse ++ σ₁ .ya)
  -- the rest, reversed
  have h₃ := band_rev_runs (body := body) (ι := ι) hrg hdisj (x := .sel) (y := .xs) (c := .cm .wn)
    (n := .m2wn) (tn := .tK) (by decide) (w := w) (L := 1) σ₂ ((v.drop h).map fun a => [a])
    (by intro b hb; obtain ⟨a, -, rfl⟩ := List.mem_map.mp hb; rfl) [] []
    (by rw [hsing]; simp [σ₂, σ₁]) (by simp [σ₂, σ₁, hxs])
    (by simp [σ₂, σ₁, hwn]) (by simp [σ₂, σ₁, hm2wn]; omega) (by simp [σ₂, σ₁, htK])
    (by simp [σ₂, σ₁, htC]) (by simp [σ₂, σ₁])
  set as := (v.take h).take r
  set bs := (v.drop h).reverse
  set l := (v.take h).drop r
  have hasl : as.length = r := by simp [as]; omega
  have hbsl : bs.length = r := by simp [bs]; omega
  set σ₃ := Function.update (Function.update σ₂ .sel []) .xs
    (cstream A w ((v.drop h).map fun a => [a]).reverse.flatten ++ [])
  have h₄ := band_ileave_runs (body := body) (ι := ι) hrg hdisj (a := .ya) (b := .xs) (z := .nv)
    (n := .m2wn) (tn := .tK) (by decide) (w := w) σ₃ as bs (cstream A w l) []
    (by omega) (by simp [σ₃, σ₂, σ₁, hm2wn, hasl])
    (by simp [σ₃, σ₂, σ₁, hya, as, l, ← cstream_append])
    (by
      have : ((v.drop h).map fun a => [a]).reverse.flatten = bs := by
        rw [← List.map_reverse, hsing]
      simp only [σ₃, Function.update_self]
      rw [this])
    (by simp [σ₃, σ₂, σ₁, hwn]) (by simp [σ₃, σ₂, σ₁, htC]) (by simp [σ₃, σ₂, σ₁])
    (by simp [σ₃, σ₂, σ₁, htK])
  set σ₄ := Function.update (Function.update (Function.update σ₃ .ya (cstream A w l)) .xs []) .nv
    (cstream A w (Mult.BandFactor.interleave as bs).reverse ++ σ₃ .nv)
  have h₅ := band_rec1Rep_runs (body := body) (ι := ι) hrg hdisj (x := .ya) (y := .nv) (n := .kn)
    (tn := .tK) (by decide) (w := w) σ₄ l [] (by simp [σ₄, σ₃, σ₂, σ₁, hkn, l]; omega)
    (by simp [σ₄]) (by simp [σ₄, σ₃, σ₂, σ₁, hwn]) (by simp [σ₄, σ₃, σ₂, σ₁, htC])
    (by simp [σ₄, σ₃, σ₂, σ₁]) (by simp [σ₄, σ₃, σ₂, σ₁, htK])
  set L := Mult.BandFactor.interleave as bs ++ l
  have hL : L = Mult.BandFactor.foldList v := by
    simp only [L, Mult.BandFactor.foldList, ← hh]
    rw [← interleave_append_left l as bs (by omega)]
    simp only [as, l, List.take_append_drop]
    rfl
  have hLl : L.length = v.length := by
    simp only [L, List.length_append, Mult.BandFactor.length_interleave as bs (by omega) (by omega), hasl, hbsl, l,
      List.length_drop, List.length_take]
    omega
  set σ₅ := Function.update (Function.update σ₄ .ya []) .nv (cstream A w l.reverse ++ σ₄ .nv)
  have h₆ := band_rev_runs (body := body) (ι := ι) hrg hdisj (x := .nv) (y := .vk) (c := .cm .wn)
    (n := .sn) (tn := .tK) (by decide) (w := w) (L := 1) σ₅ (L.reverse.map fun a => [a])
    (by intro b hb; obtain ⟨a, -, rfl⟩ := List.mem_map.mp hb; rfl) [] []
    (by rw [hsing]; simp [σ₅, σ₄, σ₃, σ₂, σ₁, hnv, L, ← cstream_append])
    (by simp [σ₅, σ₄, σ₃, σ₂, σ₁, hvk]) (by simp [σ₅, σ₄, σ₃, σ₂, σ₁, hwn])
    (by simp [σ₅, σ₄, σ₃, σ₂, σ₁, hsn, hLl]) (by simp [σ₅, σ₄, σ₃, σ₂, σ₁, htK])
    (by simp [σ₅, σ₄, σ₃, σ₂, σ₁, htC]) (by simp [σ₅, σ₄, σ₃, σ₂, σ₁])
  have hrev : (L.reverse.map fun a => [a]).reverse.flatten = L := by
    rw [← List.map_reverse, List.reverse_reverse, hsing]
  refine ((RsbRuns.seq hdisj h₁ (RsbRuns.seq hdisj h₂ (RsbRuns.seq hdisj h₃ (RsbRuns.seq hdisj h₄
    (RsbRuns.seq hdisj h₅ h₆))))).congr ?_).mono ?_
  · funext x; cases x <;> simp [σ₅, σ₄, σ₃, σ₂, σ₁, hL, hya, hxs, hnv, hac2, hsing]
  · simp only [σ₁, Function.update_self, length_cstream, List.length_reverse, List.length_drop,
      List.length_map, List.length_take, hasl, hLl, l]
    simp only [List.length_take] at *
    set n := v.length
    have a1 : min h n * w ≤ n * w := Nat.mul_le_mul_right _ (min_le_right _ _)
    have a2 : (n - h) * (6 * (1 * w) + 6 + 6) ≤ n * (6 * (1 * w) + 6 + 6) :=
      Nat.mul_le_mul_right _ (Nat.sub_le _ _)
    have a3 : r * (2 * (6 * w + 6) + 6) ≤ n * (2 * (6 * w + 6) + 6) := Nat.mul_le_mul_right _ (by omega)
    have a4 : (min h n - r) * (6 * w + 6 + 6) ≤ n * (6 * w + 6 + 6) :=
      Nat.mul_le_mul_right _ (by omega)
    ring_nf at a1 a2 a3 a4 ⊢
    omega

/-- **Unfold a line.** `dout` holding the folded line `x` becomes empty and `sel` receives
the line in natural order. -/
theorem band_unfoldLine_runs (hrg : Function.Injective rg) (hdisj : ∀ r j, rg r ≠ ι j) {w : ℕ}
    (σ : RsbR → List (Fin (A + 4))) (x : List GaussianInt) (hdout : σ .dout = cstream A w x)
    (hm2wn : (σ .m2wn).length = x.length / 2) (hkn : (σ .kn).length = (x.length + 1) / 2 - x.length / 2)
    (hwn : (σ (.cm .wn)).length = w) (hsel : σ .sel = []) (hya : σ .ya = []) (hxs : σ .xs = [])
    (htK : σ .tK = []) (htC : σ .tC = []) (hac2 : σ .ac2 = []) :
    RsbRuns body rg ι (bandUnfoldLineP rg) σ
      (Function.update (Function.update σ .dout []) .sel
        (cstream A w (Mult.BandFactor.unfoldList x))) (60 * (x.length + 1) * w + 60 * x.length + 60) := by
  have hsing : ∀ l : List GaussianInt, (l.map fun a => [a]).flatten = l := by
    intro l; induction l <;> simp_all
  set n := x.length
  set r := n / 2 with hrdef
  set E := Mult.BandFactor.evens x
  set O := Mult.BandFactor.odds x
  have hE : E.length = (n + 1) / 2 := Mult.BandFactor.length_evens x
  have hO : O.length = n / 2 := Mult.BandFactor.length_odds x
  have hsplit := Mult.BandFactor.split_evens_odds x
  set E1 := E.take r
  set l := E.drop r
  have h₁ := band_deileave_runs (body := body) (ι := ι) hrg hdisj (x := .dout) (e := .ya) (o := .xs)
    (n := .m2wn) (tn := .tK) (by decide) (w := w) σ E1 O (cstream A w l)
    (by simp [E1, hE, hO]; omega) (by simp [hm2wn, E1, hE]; omega)
    (by rw [hdout]; conv_lhs => rw [hsplit]
        rw [cstream_append])
    hwn htC hac2 htK
  set σ₁ := Function.update (Function.update (Function.update σ .dout (cstream A w l)) .ya
    (cstream A w E1.reverse ++ σ .ya)) .xs (cstream A w O.reverse ++ σ .xs)
  have hll : l.length = (n + 1) / 2 - r := by simp [l, hE]
  have h₂ := band_rec1Rep_runs (body := body) (ι := ι) hrg hdisj (x := .dout) (y := .ya) (n := .kn)
    (tn := .tK) (by decide) (w := w) σ₁ l []
    (by simp only [σ₁, Function.update_of_ne (by decide : RsbR.kn ≠ RsbR.xs),
      Function.update_of_ne (by decide : RsbR.kn ≠ RsbR.ya),
      Function.update_of_ne (by decide : RsbR.kn ≠ RsbR.dout), hkn, hll])
    (by simp [σ₁]) (by simp [σ₁, hwn]) (by simp [σ₁, htC]) (by simp [σ₁, hac2]) (by simp [σ₁, htK])
  set σ₂ := Function.update (Function.update σ₁ .dout []) .ya (cstream A w l.reverse ++ σ₁ .ya)
  have hya2 : σ₂ .ya = cstream A w E.reverse := by
    have : E = E1 ++ l := (List.take_append_drop r E).symm
    simp [σ₂, σ₁, hya, ← cstream_append, this]
  have h₃ := rsb_moveR_runs (body := body) (ι := ι) hrg (a := .xs) (b := .ac2) (by decide) σ₂
  set σ₃ := Function.update (Function.update σ₂ .xs []) .ac2 ((σ₂ .xs).reverse ++ σ₂ .ac2)
  have h₄ := rsb_moveR_runs (body := body) (ι := ι) hrg (a := .ac2) (b := .sel) (by decide) σ₃
  set σ₄ := Function.update (Function.update σ₃ .ac2 []) .sel ((σ₃ .ac2).reverse ++ σ₃ .sel)
  have hsel4 : σ₄ .sel = cstream A w O.reverse := by simp [σ₄, σ₃, σ₂, σ₁, hxs, hac2, hsel]
  have hya4 : σ₄ .ya = cstream A w (E.reverse.take r) ++ cstream A w (E.reverse.drop r) := by
    rw [← cstream_append, List.take_append_drop]
    simp only [σ₄, σ₃, Function.update_of_ne (by decide : RsbR.ya ≠ RsbR.sel),
      Function.update_of_ne (by decide : RsbR.ya ≠ RsbR.ac2),
      Function.update_of_ne (by decide : RsbR.ya ≠ RsbR.xs)]
    exact hya2
  have h₅ := band_rev_runs (body := body) (ι := ι) hrg hdisj (x := .ya) (y := .sel) (c := .cm .wn)
    (n := .m2wn) (tn := .tK) (by decide) (w := w) (L := 1) σ₄ ((E.reverse.take r).map fun a => [a])
    (by intro b hb; obtain ⟨a, -, rfl⟩ := List.mem_map.mp hb; rfl)
    (cstream A w (E.reverse.drop r)) (cstream A w O.reverse)
    (by rw [hsing, hya4]) hsel4 (by simp [σ₄, σ₃, σ₂, σ₁, hwn])
    (by simp [σ₄, σ₃, σ₂, σ₁, hm2wn, hE, hrdef]; omega) (by simp [σ₄, σ₃, σ₂, σ₁, htK])
    (by simp [σ₄, σ₃, σ₂, σ₁, htC]) (by simp [σ₄, σ₃, σ₂, σ₁])
  set σ₅ := Function.update (Function.update σ₄ .ya (cstream A w (E.reverse.drop r))) .sel
    (cstream A w ((E.reverse.take r).map fun a => [a]).reverse.flatten ++ cstream A w O.reverse)
  have h₆ := band_rev_runs (body := body) (ι := ι) hrg hdisj (x := .ya) (y := .sel) (c := .cm .wn)
    (n := .kn) (tn := .tK) (by decide) (w := w) (L := 1) σ₅ ((E.reverse.drop r).map fun a => [a])
    (by intro b hb; obtain ⟨a, -, rfl⟩ := List.mem_map.mp hb; rfl) [] _
    (by rw [hsing]; simp [σ₅]) rfl (by simp [σ₅, σ₄, σ₃, σ₂, σ₁, hwn])
    (by simp [σ₅, σ₄, σ₃, σ₂, σ₁, hkn, hE, hrdef]) (by simp [σ₅, σ₄, σ₃, σ₂, σ₁, htK])
    (by simp [σ₅, σ₄, σ₃, σ₂, σ₁, htC]) (by simp [σ₅, σ₄, σ₃, σ₂, σ₁])
  refine ((RsbRuns.seq hdisj h₁ (RsbRuns.seq hdisj h₂ (RsbRuns.seq hdisj h₃ (RsbRuns.seq hdisj h₄
    (RsbRuns.seq hdisj h₅ h₆))))).congr ?_).mono ?_
  swap
  · simp only [σ₃, σ₂, σ₁, Function.update_self, 
      Function.update_of_ne (by decide : RsbR.xs ≠ RsbR.ya), Function.update_of_ne (by decide : RsbR.xs ≠ RsbR.dout),
      Function.update_of_ne (by decide : RsbR.ac2 ≠ RsbR.xs), Function.update_of_ne (by decide : RsbR.ac2 ≠ RsbR.ya),
      Function.update_of_ne (by decide : RsbR.ac2 ≠ RsbR.dout), hxs, hac2, length_cstream, List.length_append,
      List.length_reverse, List.length_nil, List.length_map, List.length_take, List.length_drop, hE, hO, hll,
      List.length_reverse]
    have hE1 : E1.length = r := by simp [E1, hE]; omega
    rw [hE1, show min r ((n + 1) / 2) = r by omega]
    have a1 : r * (2 * (6 * w + 6) + 6) ≤ n * (12 * w + 18) := Nat.mul_le_mul (by omega) (by omega)
    have a2 : ((n + 1) / 2 - r) * (6 * w + 6 + 6) ≤ n * (6 * w + 12) + (6 * w + 12) := by
      have : (n + 1) / 2 - r ≤ n + 1 := by omega
      nlinarith
    have a3 : n / 2 * w ≤ n * w := Nat.mul_le_mul_right _ (by omega)
    have a4 : r * (6 * (1 * w) + 6 + 6) ≤ n * (6 * w + 12) := Nat.mul_le_mul (by omega) (by omega)
    have a5 : ((n + 1) / 2 - r) * (6 * (1 * w) + 6 + 6) ≤ n * (6 * w + 12) + (6 * w + 12) := by
      have : (n + 1) / 2 - r ≤ n + 1 := by omega
      nlinarith
    nlinarith
  have hfin : ((E.reverse.drop r).map fun a => [a]).reverse.flatten ++
      ((E.reverse.take r).map fun a => [a]).reverse.flatten = E := by
    rw [← List.map_reverse, ← List.map_reverse, hsing, hsing, ← List.reverse_append,
      List.take_append_drop, List.reverse_reverse]
  have hsel : cstream A w ((E.reverse.drop r).map fun a => [a]).reverse.flatten ++
      (cstream A w ((E.reverse.take r).map fun a => [a]).reverse.flatten ++ cstream A w O.reverse) =
      cstream A w (Mult.BandFactor.unfoldList x) := by
    rw [← List.append_assoc, ← cstream_append, hfin, Mult.BandFactor.unfoldList, cstream_append]
  funext z
  by_cases hz : z = .sel
  · subst hz
    simp only [Function.update_self]
    exact hsel
  cases z <;> first | exact absurd rfl hz | simp [σ₅, σ₄, σ₃, σ₂, σ₁, hya, hxs, hac2]

end Contracts

end IntegerMultBounds.MathlibTM2.Fast
