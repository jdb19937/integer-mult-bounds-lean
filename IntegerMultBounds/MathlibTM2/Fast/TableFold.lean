module

public import IntegerMultBounds.MathlibTM2.Fast.TableWeight
public import IntegerMultBounds.MathlibTM2.Mult.BandFoldRows

/-!
# The folded matrix rows as a table stream

A table program with `60` variables emits the folded rows `foldRowZ` of the banded
factorization: rows `i = 0, …, B+s`, in row `i` the `2B+1` columns from
`i - min(i,B)`, each entry `foldEntryZ` as a real coefficient. The off-diagonal
entries reuse the Gaussian entry bodies of the off-diagonal weight stream
(`tblOffPosBody`, `tblOffNegBody`) on the first `48` variables; the diagonal is the
constant `2^P`.

Variables: the weight layout `0 … 47` (`19` holds the precision `P`, `34` `s`, `35`
`t`, `36` `α`, `37` the row vertex `ℓ`, `39` the band `w`), and `48` row `i`, `49` the
row count, `50` the column counter, `51` the row length `2B+1`, `52` `B`, `53` the
column, `54` the residue `d`, `55` `2^P`, `56` the first column, `57` the column vertex,
`58` a spare, `59` the constant `2`.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Fast

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Fast.TableVM
open IntegerMultBounds.Resampling.WeightTable IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.Resampling.WeightNat

set_option linter.unusedSimpArgs false

/-- The weight layout inside the fold layout. -/
def tblFoldMap : Fin 48 → Fin 60 := Fin.castLE (by norm_num)

theorem tblFoldMap_inj : Function.Injective tblFoldMap := Fin.castLE_injective _

/-- `dst := foldAt src` (as a residue below `s`), with `59 = 2`, `22 = 1`, `34 = s`. -/
def tblFoldAt (src dst : Fin 60) : TblCode 60 :=
  tblBlock 60 [.div src 59 58] (.mod src 59 dst) ;;
    .ite dst 22 (.ins (.copy 58 dst)) (tblBlock 60 [.sub 34 22 dst] (.sub dst 58 dst))

theorem foldAt_val (s : ℕ) [NeZero s] (m : ℕ) (hm : m < s) :
    (NLogN.PhaseCellMatrix.foldAt s m).val = if m % 2 = 0 then m / 2 else s - 1 - m / 2 := by
  unfold NLogN.PhaseCellMatrix.foldAt
  split
  · rw [ZMod.val_cast_of_lt (by omega)]
  · rw [ZMod.val_cast_of_lt (by omega)]

theorem tblFoldAt_do {A W w : ℕ} (st : TblSt 60 A) (src dst : Fin 60) {s m : ℕ} [NeZero s]
    (hsrc : st.val src = m) (hm : m < s) (h59 : st.val 59 = 2) (h22 : st.val 22 = 1)
    (hS : st.val 34 = s) (hd : dst ≠ 59 ∧ dst ≠ 22 ∧ dst ≠ 34 ∧ dst ≠ 58) (hs58 : src ≠ 58)
    (hWs : s < 2 ^ W) :
    TblDo A W w (tblFoldAt src dst) st (fun s' => s'.val dst = (NLogN.PhaseCellMatrix.foldAt s m).val ∧
      s'.acc = st.acc ∧ ∀ x, x ≠ dst → x ≠ 58 → s'.val x = st.val x) 5 := by
  obtain ⟨h1, h2, h3, h4⟩ := hd
  rw [foldAt_val s m hm]
  refine (TblDo.block _ _ (by simp [tblFitsList, TblIns.fits]) rfl).seq (K₂ := 3)
    (fun s₁ hs₁ => ?_) |>.mono (fun _ h => h) (by norm_num)
  subst hs₁
  set s₁ := tblExactList A w ([.div src 59 58] ++ [.mod src 59 dst]) st
  have v58 : s₁.val 58 = m / 2 := by
    simp [s₁, tblExactList, TblIns.exact, hsrc, h59, Function.update_of_ne h4.symm]
  have vd : s₁.val dst = m % 2 := by
    simp [s₁, tblExactList, TblIns.exact, hsrc, h59, Function.update_of_ne h4, hs58]
  have v22 : s₁.val 22 = 1 := by
    simp [s₁, tblExactList, TblIns.exact, h22, Function.update_of_ne h2.symm,
      Function.update_of_ne (show (22 : Fin 60) ≠ 58 by decide)]
  have v34 : s₁.val 34 = s := by
    simp [s₁, tblExactList, TblIns.exact, hS, Function.update_of_ne h3.symm,
      Function.update_of_ne (show (34 : Fin 60) ≠ 58 by decide)]
  have vacc : s₁.acc = st.acc := by simp [s₁, tblExactList, TblIns.exact]
  have vkeep : ∀ x, x ≠ dst → x ≠ 58 → s₁.val x = st.val x := by
    intro x hx1 hx2
    simp [s₁, tblExactList, TblIns.exact, Function.update_of_ne hx1, Function.update_of_ne hx2]
  by_cases hev : m % 2 = 0
  · refine TblDo.iteT (by rw [vd, v22, hev]; norm_num) (TblDo.insX (.copy 58 dst) trivial ?_) |>.mono
      (fun _ h => h) (by norm_num)
    refine ⟨by simp [TblIns.exact, v58, hev], by simp [TblIns.exact, vacc], fun x hx1 hx2 => ?_⟩
    simp [TblIns.exact, Function.update_of_ne hx1, vkeep x hx1 hx2]
  · refine TblDo.iteF (by rw [vd, v22]; omega) (TblDo.block _ _ ?_ ?_)
    · simp [tblFitsList, TblIns.fits, TblIns.exact, v22, v34, v58, Function.update_of_ne h4.symm]
      omega
    · refine ⟨?_, by simp [tblExactList, TblIns.exact, vacc], fun x hx1 hx2 => ?_⟩
      · simp [tblExactList, TblIns.exact, v22, v34, v58, Function.update_of_ne h4.symm, hev]
      · simp [tblExactList, TblIns.exact, Function.update_of_ne hx1, vkeep x hx1 hx2]

/-- A zero entry. -/
def tblFoldZero : TblCode 60 := .ins (.emit 38 38)

/-- An entry with `h = d ∈ [1, w]`. -/
def tblFoldPos : TblCode 60 := tblBlock 60 [] (.sub 54 22 40) ;; tblOffPosBody.rename tblFoldMap

/-- An entry with `d > w`: `h = d - s` when `d ≥ s - w`, else zero. -/
def tblFoldNeg : TblCode 60 :=
  tblBlock 60 [] (.sub 34 39 58) ;;
    .ite 54 58 tblFoldZero (tblBlock 60 [.sub 34 54 58] (.sub 39 58 40) ;; tblOffNegBody.rename tblFoldMap)

/-- The entry of row `48` at column `53`, the row prelude in place. -/
def tblFoldMain : TblCode 60 :=
  tblFoldAt 53 57 ;; tblBlock 60 [.add 57 34 58] (.sub 58 37 54) ;; .ins (.mod 54 34 54) ;;
    .ite 54 22 (.ins (.emit 55 38)) (.ite 39 54 tblFoldNeg tblFoldPos)

/-- One folded entry; zero outside `s × s`. -/
def tblFoldEntry : TblCode 60 := .ite 48 34 (.ite 53 34 tblFoldMain tblFoldZero) tblFoldZero

/-- The coefficient symbols of a folded entry. -/
def tblFoldSyms (A w s t α P wd i c : ℕ) [NeZero s] : List (Fin (A + 4)) :=
  coeffSyms A w (red w ⟨Mult.BandFactor.foldEntryZ s t α P wd i c, 0⟩)

theorem tblFoldZero_do {A W w : ℕ} (st : TblSt 60 A) (h38 : st.val 38 = 0) :
    TblDo A W w tblFoldZero st (fun s' => s'.acc =
      (coeffSyms A w (red w ⟨(0 : ℤ), 0⟩)).reverse ++ st.acc) 1 :=
  TblDo.insX (.emit 38 38) trivial (by
    simp only [TblIns.exact, h38, tbl_pairs_red, Nat.cast_zero])

/-- The entry body emits the folded entry of row `i` at column `c`. -/
theorem tblFoldEntry_do {A W w : ℕ} (st : TblSt 60 A) {s t α P wd i c N : ℕ} [NeZero s]
    (h18 : st.val 18 = piN P) (h19 : st.val 19 = P) (h21 : st.val 21 = s * s)
    (h22 : st.val 22 = 1) (h34 : st.val 34 = s) (h35 : st.val 35 = t) (h43 : st.val 43 = α * α)
    (h38 : st.val 38 = 0) (h39 : st.val 39 = wd)
    (hrow : i < s → st.val 37 = (NLogN.PhaseCellMatrix.foldAt s i).val ∧
      st.val 41 = t * (NLogN.PhaseCellMatrix.foldAt s i).val % s ∧
      st.val 42 = if t * (NLogN.PhaseCellMatrix.foldAt s i).val % s +
        t * (NLogN.PhaseCellMatrix.foldAt s i).val % s < s then 0 else s)
    (h48 : st.val 48 = i) (h53 : st.val 53 = c) (h55 : st.val 55 = 2 ^ P) (h59 : st.val 59 = 2)
    (hws : 2 * wd + 1 < s) (hP : 13 ≤ P) (hW : TblOffW W P α s t wd N) (hsW : 2 * s < 2 ^ W) :
    TblDo A W w tblFoldEntry st (fun s' => s'.acc =
      (tblFoldSyms A w s t α P wd i c).reverse ++ st.acc) (310 * P + 200) := by
  have hz := tblFoldZero_do (W := W) (w := w) st h38
  by_cases hi : i < s
  · by_cases hc : c < s
    · refine TblDo.iteT (by rw [h48, h34]; exact hi) (TblDo.iteT (by rw [h53, h34]; exact hc) ?_)
        |>.mono (fun _ h => h) (show 310 * P + 198 + 1 + 1 ≤ 310 * P + 200 by omega)
      obtain ⟨h37, h41, h42⟩ := hrow hi
      set ℓ := (NLogN.PhaseCellMatrix.foldAt s i).val with hℓdef
      have hℓ : ℓ < s := ZMod.val_lt _
      have hs0 : 0 < s := Nat.pos_of_ne_zero (NeZero.ne s)
      obtain ⟨hN, hW1, hW2, hW4, h4N⟩ := hW
      have hW' : TblOffW W P α s t wd N := ⟨hN, hW1, hW2, hW4, h4N⟩
      refine (tblFoldAt_do (W := W) (w := w) st 53 57 h53 hc h59 h22 h34 (by decide) (by decide)
        (by omega)).seq (K₂ := 310 * P + 193) (fun s₁ ⟨f57, facc, fkeep⟩ => ?_) |>.mono
        (fun _ h => h) (by omega)
      set x := (NLogN.PhaseCellMatrix.foldAt s c).val with hxdef
      have hx : x < s := ZMod.val_lt _
      have k₁ : ∀ y : Fin 60, y ≠ 57 → y ≠ 58 → s₁.val y = st.val y := fkeep
      refine (TblDo.block [.add 57 34 58] (.sub 58 37 54) ?_ rfl).seq (K₂ := 310 * P + 191)
        (fun s₂ hs₂ => ?_) |>.mono (fun _ h => h) (by simp; omega)
      · simp [tblFitsList, TblIns.fits, TblIns.exact, f57, k₁ 34 (by decide) (by decide), h34,
          k₁ 37 (by decide) (by decide), h37]
        omega
      subst hs₂
      set s₂ := tblExactList A w ([.add 57 34 58] ++ [.sub 58 37 54]) s₁
      have v54 : s₂.val 54 = x + s - ℓ := by
        simp [s₂, tblExactList, TblIns.exact, f57, k₁ 34 (by decide) (by decide), h34,
          k₁ 37 (by decide) (by decide), h37]
      have k₂ : ∀ y : Fin 60, y ≠ 54 → y ≠ 57 → y ≠ 58 → s₂.val y = st.val y := by
        intro y h1 h2 h3
        simp [s₂, tblExactList, TblIns.exact, Function.update_of_ne h1, Function.update_of_ne h3, k₁ y h2 h3]
      have acc₂ : s₂.acc = st.acc := by simp [s₂, tblExactList, TblIns.exact, facc]
      refine (TblDo.insX (.mod 54 34 54) trivial rfl).seq (K₂ := 310 * P + 190)
        (fun s₃ hs₃ => ?_) |>.mono (fun _ h => h) (by omega)
      subst hs₃
      set d := Mult.BandFactor.fdist s (NLogN.PhaseCellMatrix.foldAt s i)
        (NLogN.PhaseCellMatrix.foldAt s c) with hddef
      have v54' : ((TblIns.mod 54 34 54).exact A w s₂).val 54 = d := by
        simp [TblIns.exact, v54, k₂ 34 (by decide) (by decide) (by decide), h34, hddef,
          Mult.BandFactor.fdist, hxdef, hℓdef]
      set s₃ := (TblIns.mod 54 34 54).exact A w s₂
      have k₃ : ∀ y : Fin 60, y ≠ 54 → y ≠ 57 → y ≠ 58 → s₃.val y = st.val y := by
        intro y h1 h2 h3
        simp [s₃, TblIns.exact, Function.update_of_ne h1, k₂ y h1 h2 h3]
      have acc₃ : s₃.acc = st.acc := by simp [s₃, TblIns.exact, acc₂]
      have hds : d < s := Nat.mod_lt _ hs0
      have hcast : ((ℓ : ℕ) : ZMod s) = NLogN.PhaseCellMatrix.foldAt s i := ZMod.natCast_zmod_val _
      by_cases hd0 : d < 1
      · refine TblDo.iteT (by rw [v54', k₃ 22 (by decide) (by decide) (by decide), h22]; exact hd0)
          (TblDo.insX (.emit 55 38) trivial rfl) |>.mono (fun s' hs' => ?_) (by omega)
        subst hs'
        have hd : d = 0 := by omega
        simp only [TblIns.exact, k₃ 55 (by decide) (by decide) (by decide), h55,
          k₃ 38 (by decide) (by decide) (by decide), h38, acc₃, tblFoldSyms,
          Mult.BandFactor.foldEntryZ, if_pos (And.intro hi hc), ← hddef, hd, ite_true]
        rw [tbl_pairs_red]; push_cast; rfl
      · refine TblDo.iteF (by rw [v54', k₃ 22 (by decide) (by decide) (by decide), h22]; exact hd0)
          ?_ |>.mono (fun _ h => h) (show 310 * P + 189 + 1 ≤ 310 * P + 190 by omega)
        by_cases hwd : wd < d
        · refine TblDo.iteT (by rw [v54', k₃ 39 (by decide) (by decide) (by decide), h39]; exact hwd)
            ?_ |>.mono (fun _ h => h) (show 310 * P + 188 + 1 ≤ 310 * P + 189 by omega)
          -- the negative side
          refine (TblDo.block [] (.sub 34 39 58) ?_ rfl).seq (K₂ := 310 * P + 187)
            (fun s₄ hs₄ => ?_) |>.mono (fun _ h => h) (by simp; omega)
          · simp [tblFitsList, TblIns.fits, k₃ 34 (by decide) (by decide) (by decide), h34,
              k₃ 39 (by decide) (by decide) (by decide), h39]
            omega
          subst hs₄
          set s₄ := tblExactList A w ([] ++ [.sub 34 39 58]) s₃
          have v58 : s₄.val 58 = s - wd := by
            simp [s₄, tblExactList, TblIns.exact, k₃ 34 (by decide) (by decide) (by decide), h34,
              k₃ 39 (by decide) (by decide) (by decide), h39]
          have v54'' : s₄.val 54 = d := by simp [s₄, tblExactList, TblIns.exact, v54']
          have k₄ : ∀ y : Fin 60, y ≠ 54 → y ≠ 57 → y ≠ 58 → s₄.val y = st.val y := by
            intro y h1 h2 h3
            simp [s₄, tblExactList, TblIns.exact, Function.update_of_ne h3, k₃ y h1 h2 h3]
          have acc₄ : s₄.acc = st.acc := by simp [s₄, tblExactList, TblIns.exact, acc₃]
          by_cases hfar : d < s - wd
          · refine TblDo.iteT (by rw [v54'', v58]; exact hfar)
              (tblFoldZero_do s₄ (by rw [k₄ 38 (by decide) (by decide) (by decide), h38]))
              |>.mono (fun s' hs' => ?_) (by omega)
            rw [hs', acc₄, tblFoldSyms, Mult.BandFactor.foldEntryZ, if_pos (And.intro hi hc), ← hddef,
              if_neg (by omega), if_neg (by omega), if_neg (by omega)]
          · refine TblDo.iteF (by rw [v54'', v58]; exact hfar) ?_ |>.mono (fun _ h => h)
              (show 310 * P + 124 + 2 + 1 ≤ 310 * P + 187 by omega)
            refine (TblDo.block [.sub 34 54 58] (.sub 39 58 40) ?_ rfl).seq (K₂ := 310 * P + 124)
              (fun s₅ hs₅ => ?_) |>.mono (fun _ h => h) (by simp; omega)
            · simp [tblFitsList, TblIns.fits, TblIns.exact, k₄ 34 (by decide) (by decide) (by decide),
                h34, v54'', k₄ 39 (by decide) (by decide) (by decide), h39]
              omega
            subst hs₅
            set s₅ := tblExactList A w ([.sub 34 54 58] ++ [.sub 39 58 40]) s₄
            have v40 : s₅.val 40 = wd - (s - d) := by
              simp [s₅, tblExactList, TblIns.exact, k₄ 34 (by decide) (by decide) (by decide), h34,
                v54'', k₄ 39 (by decide) (by decide) (by decide), h39]
            have k₅ : ∀ y : Fin 60, y ≠ 40 → y ≠ 54 → y ≠ 57 → y ≠ 58 → s₅.val y = st.val y := by
              intro y h0 h1 h2 h3
              simp [s₅, tblExactList, TblIns.exact, Function.update_of_ne h0, Function.update_of_ne h3,
                k₄ y h1 h2 h3]
            have acc₅ : s₅.acc = st.acc := by simp [s₅, tblExactList, TblIns.exact, acc₄]
            have hb := (tblOffNegBody_do (A := A) (W := W) (w := w) (s₅.restrict tblFoldMap)
              (s := s) (t := t) (α := α) (p := P) (m := wd) (ℓ := ℓ) (i := wd - (s - d)) (N := N)
              (by show s₅.val 18 = _; rw [k₅ 18 (by decide) (by decide) (by decide) (by decide), h18])
              (by show s₅.val 19 = _; rw [k₅ 19 (by decide) (by decide) (by decide) (by decide), h19])
              (by show s₅.val 21 = _; rw [k₅ 21 (by decide) (by decide) (by decide) (by decide), h21])
              (by show s₅.val 22 = _; rw [k₅ 22 (by decide) (by decide) (by decide) (by decide), h22])
              (by show s₅.val 34 = _; rw [k₅ 34 (by decide) (by decide) (by decide) (by decide), h34])
              (by show s₅.val 35 = _; rw [k₅ 35 (by decide) (by decide) (by decide) (by decide), h35])
              (by show s₅.val 43 = _; rw [k₅ 43 (by decide) (by decide) (by decide) (by decide), h43])
              (by show s₅.val 38 = _; rw [k₅ 38 (by decide) (by decide) (by decide) (by decide), h38])
              (by show s₅.val 39 = _; rw [k₅ 39 (by decide) (by decide) (by decide) (by decide), h39])
              (by show s₅.val 40 = _; exact v40)
              (by show s₅.val 37 = _; rw [k₅ 37 (by decide) (by decide) (by decide) (by decide), h37])
              (by show s₅.val 41 = _; rw [k₅ 41 (by decide) (by decide) (by decide) (by decide), h41])
              (by show s₅.val 42 = _; rw [k₅ 42 (by decide) (by decide) (by decide) (by decide), h42])
              (by omega) hℓ hP hW').rename tblFoldMap_inj
            refine hb.mono (fun s' ⟨hs', _⟩ => ?_) le_rfl
            rw [show s'.acc = (s'.restrict tblFoldMap).acc from rfl, hs',
              show (s₅.restrict tblFoldMap).acc = s₅.acc from rfl, acc₅]
            congr 2
            rw [tblFoldSyms, tblEntE, Mult.BandFactor.foldEntryZ, if_pos (And.intro hi hc), ← hddef,
              if_neg (by omega), if_neg (by omega), if_pos (by omega), hcast]
            congr 2
            push_cast [show wd - (wd - (s - d)) = s - d by omega, Nat.cast_sub hds.le]
            ring_nf
        · refine TblDo.iteF (by rw [v54', k₃ 39 (by decide) (by decide) (by decide), h39]; exact hwd)
            ?_ |>.mono (fun _ h => h) (show 310 * P + 188 + 1 ≤ 310 * P + 189 by omega)
          -- the positive side
          have hdw : d ≤ wd := by omega
          refine (TblDo.block [] (.sub 54 22 40) ?_ rfl).seq (K₂ := 310 * P + 122)
            (fun s₄ hs₄ => ?_) |>.mono (fun _ h => h) (by simp; omega)
          · simp [tblFitsList, TblIns.fits, v54', k₃ 22 (by decide) (by decide) (by decide), h22]
            omega
          subst hs₄
          set s₄ := tblExactList A w ([] ++ [.sub 54 22 40]) s₃
          have k₄ : ∀ y : Fin 60, y ≠ 40 → y ≠ 54 → y ≠ 57 → y ≠ 58 → s₄.val y = st.val y := by
            intro y h0 h1 h2 h3
            simp [s₄, tblExactList, TblIns.exact, Function.update_of_ne h0, k₃ y h1 h2 h3]
          have v40 : s₄.val 40 = d - 1 := by
            simp [s₄, tblExactList, TblIns.exact, v54', k₃ 22 (by decide) (by decide) (by decide), h22]
          have acc₄ : s₄.acc = st.acc := by simp [s₄, tblExactList, TblIns.exact, acc₃]
          have hb := (tblOffPosBody_do (A := A) (W := W) (w := w) (s₄.restrict tblFoldMap)
            (s := s) (t := t) (α := α) (p := P) (m := wd) (ℓ := ℓ) (i := d - 1) (N := N)
            (by show s₄.val 18 = _; rw [k₄ 18 (by decide) (by decide) (by decide) (by decide), h18])
            (by show s₄.val 19 = _; rw [k₄ 19 (by decide) (by decide) (by decide) (by decide), h19])
            (by show s₄.val 21 = _; rw [k₄ 21 (by decide) (by decide) (by decide) (by decide), h21])
            (by show s₄.val 22 = _; rw [k₄ 22 (by decide) (by decide) (by decide) (by decide), h22])
            (by show s₄.val 34 = _; rw [k₄ 34 (by decide) (by decide) (by decide) (by decide), h34])
            (by show s₄.val 35 = _; rw [k₄ 35 (by decide) (by decide) (by decide) (by decide), h35])
            (by show s₄.val 43 = _; rw [k₄ 43 (by decide) (by decide) (by decide) (by decide), h43])
            (by show s₄.val 38 = _; rw [k₄ 38 (by decide) (by decide) (by decide) (by decide), h38])
            (by show s₄.val 40 = _; exact v40)
            (by show s₄.val 37 = _; rw [k₄ 37 (by decide) (by decide) (by decide) (by decide), h37])
            (by show s₄.val 41 = _; rw [k₄ 41 (by decide) (by decide) (by decide) (by decide), h41])
            (by show s₄.val 42 = _; rw [k₄ 42 (by decide) (by decide) (by decide) (by decide), h42])
            (by omega) hℓ hP hW').rename tblFoldMap_inj
          refine hb.mono (fun s' ⟨hs', _⟩ => ?_) le_rfl
          rw [show s'.acc = (s'.restrict tblFoldMap).acc from rfl, hs',
            show (s₄.restrict tblFoldMap).acc = s₄.acc from rfl, acc₄]
          congr 2
          rw [tblFoldSyms, tblEntE, Mult.BandFactor.foldEntryZ, if_pos (And.intro hi hc), ← hddef,
            if_neg (by omega), if_pos hdw, hcast, show ((d - 1 + 1 : ℕ) : ℤ) = (d : ℤ) by
              rw [Nat.sub_add_cancel (by omega)]]
    · refine TblDo.iteT (by rw [h48, h34]; exact hi) (TblDo.iteF (by rw [h53, h34]; exact hc) hz)
        |>.mono (fun _ h => ?_) (by omega)
      rw [h, tblFoldSyms, Mult.BandFactor.foldEntryZ, if_neg (fun h' => hc h'.2)]
  · refine TblDo.iteF (by rw [h48, h34]; exact hi) hz |>.mono (fun _ h => ?_) (by omega)
    rw [h, tblFoldSyms, Mult.BandFactor.foldEntryZ, if_neg (fun h' => hi h'.1)]

end IntegerMultBounds.MathlibTM2.Fast
