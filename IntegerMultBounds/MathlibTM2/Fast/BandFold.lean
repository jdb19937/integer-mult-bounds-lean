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

set_option linter.unusedSimpArgs false

variable {T Q A : ℕ} {U : Type} {P : Type}

section Programs

variable (rg : RsbR → Fin T)

/-- Move the top record of `x` onto `y`, keeping its symbol order. -/
def bandRec1P (x y : RsbR) : Pr P T Q A U :=
  .seq (rsbMv (rg (.cm .wn)) (rg .tC) (rg x) (rg .ac2)) (moveR (rg .ac2) (rg y) id)

/-- Alternate records of `a` and `b` onto `z`, one pair per symbol of `n`. -/
def bandILeaveP (a b z n tn : RsbR) : Pr P T Q A U :=
  rsbRep (rg n) (rg tn) (.seq (bandRec1P rg a z) (bandRec1P rg b z))

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
  · simp [hwn]; omega

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
  · subst hrz; simp [Function.update_of_ne (Ne.symm hbz), Function.update_of_ne (Ne.symm haz)]
  by_cases hrb : r = b
  · subst hrb; simp [Function.update_of_ne hrz, Function.update_of_ne (Ne.symm hab)]
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
        Function.update_of_ne (Ne.symm hbz), Function.update_of_ne (Ne.symm haz)]
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
    · subst hrt; simp [rsbUpd2, htn, Function.update_of_ne (Ne.symm hat), Function.update_of_ne (Ne.symm hbt),
        Function.update_of_ne (Ne.symm hzt)]
    by_cases hrn : r = n
    · subst hrn; simp [rsbUpd2, Function.update_of_ne hrt, Function.update_of_ne (Ne.symm han),
        Function.update_of_ne (Ne.symm hbn), Function.update_of_ne (Ne.symm hzn)]
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

end Contracts

end IntegerMultBounds.MathlibTM2.Fast
