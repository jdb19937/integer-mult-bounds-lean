module

public import IntegerMultBounds.MathlibTM2.Fast.TableWeight
public import IntegerMultBounds.MathlibTM2.Mult.BandFoldRows
public import IntegerMultBounds.MathlibTM2.Fast.CMulStream

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
    simp [s₁, tblExactList, TblIns.exact, hsrc, h59, hs58]
  have v22 : s₁.val 22 = 1 := by
    simp [s₁, tblExactList, TblIns.exact, h22, Function.update_of_ne h2.symm]
  have v34 : s₁.val 34 = s := by
    simp [s₁, tblExactList, TblIns.exact, hS, Function.update_of_ne h3.symm]
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
          Mult.BandFactor.foldEntryZ, ite_eq_left (And.intro hi hc), ← hddef, hd, ite_true]
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
            rw [hs', acc₄, tblFoldSyms, Mult.BandFactor.foldEntryZ, ite_eq_left (And.intro hi hc), ← hddef,
              ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]
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
            rw [tblFoldSyms, tblEntE, Mult.BandFactor.foldEntryZ, ite_eq_left (And.intro hi hc), ← hddef,
              ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left (by omega), hcast]
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
          rw [tblFoldSyms, tblEntE, Mult.BandFactor.foldEntryZ, ite_eq_left (And.intro hi hc), ← hddef,
            ite_eq_right (by omega), ite_eq_left hdw, hcast, show ((d - 1 + 1 : ℕ) : ℤ) = (d : ℤ) by
              rw [Nat.sub_add_cancel (by omega)]]
    · refine TblDo.iteT (by rw [h48, h34]; exact hi) (TblDo.iteF (by rw [h53, h34]; exact hc) hz)
        |>.mono (fun _ h => ?_) (by omega)
      rw [h, tblFoldSyms, Mult.BandFactor.foldEntryZ, ite_eq_right (fun h' => hc h'.2)]
  · refine TblDo.iteF (by rw [h48, h34]; exact hi) hz |>.mono (fun _ h => ?_) (by omega)
    rw [h, tblFoldSyms, Mult.BandFactor.foldEntryZ, ite_eq_right (fun h' => hi h'.1)]

/-- The row prelude: `ℓ = foldAt i` into `37`, `t ℓ mod s` into `41`, the centring `42`. -/
def tblFoldRowPre : TblCode 60 :=
  tblFoldAt 48 37 ;; tblBlock 60 [.mul 35 37 41, .mod 41 34 41] (.add 41 41 0) ;;
    .ite 0 34 (.ins (.zero 42)) (.ins (.copy 34 42))

/-- One folded row: the prelude when `i < s`, the first column into `56`, the entries. -/
def tblFoldRow : TblCode 60 :=
  .ite 48 34 tblFoldRowPre (.ins (.zero 58)) ;;
    .ite 48 52 (.ins (.zero 56)) (.ins (.sub 48 52 56)) ;;
    tblFor 50 51 (tblBlock 60 [] (.add 56 50 53) ;; tblFoldEntry)

theorem tblFoldRowPre_do {A W w : ℕ} (st : TblSt 60 A) {s t i : ℕ} [NeZero s]
    (h48 : st.val 48 = i) (hi : i < s) (h59 : st.val 59 = 2) (h22 : st.val 22 = 1)
    (h34 : st.val 34 = s) (h35 : st.val 35 = t) (hW : 2 * s * (t + 1) < 2 ^ W) :
    TblDo A W w tblFoldRowPre st (fun s' =>
      s'.val 37 = (NLogN.PhaseCellMatrix.foldAt s i).val ∧
      s'.val 41 = t * (NLogN.PhaseCellMatrix.foldAt s i).val % s ∧
      s'.val 42 = (if t * (NLogN.PhaseCellMatrix.foldAt s i).val % s +
        t * (NLogN.PhaseCellMatrix.foldAt s i).val % s < s then 0 else s) ∧
      s'.acc = st.acc ∧ ∀ x : Fin 60, x ≠ 0 → x ≠ 37 → x ≠ 41 → x ≠ 42 → x ≠ 58 →
        s'.val x = st.val x) 10 := by
  have hs0 : 0 < s := Nat.pos_of_ne_zero (NeZero.ne s)
  have hsW : s < 2 ^ W := lt_of_le_of_lt (by nlinarith) hW
  have htsW : t * s < 2 ^ W := lt_of_le_of_lt (by nlinarith) hW
  refine (tblFoldAt_do (W := W) (w := w) st 48 37 h48 hi h59 h22 h34 (by decide) (by decide) hsW).seq
    (K₂ := 5) (fun s₁ ⟨f37, facc, fkeep⟩ => ?_) |>.mono (fun _ h => h) (by norm_num)
  set ℓ := (NLogN.PhaseCellMatrix.foldAt s i).val with hℓdef
  have hℓ : ℓ < s := ZMod.val_lt _
  have k₁ : ∀ y : Fin 60, y ≠ 37 → y ≠ 58 → s₁.val y = st.val y := fkeep
  have v34 := k₁ 34 (by decide) (by decide)
  have v35 := k₁ 35 (by decide) (by decide)
  have htl : t * ℓ ≤ t * s := Nat.mul_le_mul_left _ hℓ.le
  have hmod := Nat.mod_lt (t * ℓ) hs0
  refine (TblDo.block [.mul 35 37 41, .mod 41 34 41] (.add 41 41 0) ?_ rfl).seq (K₂ := 2)
    (fun s₂ hs₂ => ?_) |>.mono (fun _ h => h) (by simp)
  · simp [tblFitsList, TblIns.fits, TblIns.exact, f37, v34, v35, h34, h35]
    constructor <;> nlinarith
  subst hs₂
  set s₂ := tblExactList A w ([.mul 35 37 41, .mod 41 34 41] ++ [.add 41 41 0]) s₁
  have v0 : s₂.val 0 = t * ℓ % s + t * ℓ % s := by
    simp [s₂, tblExactList, TblIns.exact, f37, v34, v35, h34, h35]
  have v41 : s₂.val 41 = t * ℓ % s := by
    simp [s₂, tblExactList, TblIns.exact, f37, v34, v35, h34, h35]
  have v37 : s₂.val 37 = ℓ := by simp [s₂, tblExactList, TblIns.exact, f37]
  have v34' : s₂.val 34 = s := by simp [s₂, tblExactList, TblIns.exact, v34, h34]
  have k₂ : ∀ y : Fin 60, y ≠ 0 → y ≠ 37 → y ≠ 41 → y ≠ 58 → s₂.val y = st.val y := by
    intro y h0 h1 h2 h3
    simp [s₂, tblExactList, TblIns.exact, Function.update_of_ne h0, Function.update_of_ne h2,
      k₁ y h1 h3]
  have acc₂ : s₂.acc = st.acc := by simp [s₂, tblExactList, TblIns.exact, facc]
  by_cases hc : t * ℓ % s + t * ℓ % s < s
  · refine TblDo.iteT (by rw [v0, v34']; exact hc) (TblDo.insX (.zero 42) trivial ?_)
    refine ⟨?_, ?_, ?_, ?_, fun x h0 h1 h2 h3 h4 => ?_⟩
    · simp [TblIns.exact, v37]
    · simp [TblIns.exact, v41]
    · simp [TblIns.exact, hc]
    · simp [TblIns.exact, acc₂]
    · simp [TblIns.exact, Function.update_of_ne h3, k₂ x h0 h1 h2 h4]
  · refine TblDo.iteF (by rw [v0, v34']; exact hc) (TblDo.insX (.copy 34 42) trivial ?_)
    refine ⟨?_, ?_, ?_, ?_, fun x h0 h1 h2 h3 h4 => ?_⟩
    · simp [TblIns.exact, v37]
    · simp [TblIns.exact, v41]
    · simp [TblIns.exact, hc, v34']
    · simp [TblIns.exact, acc₂]
    · simp [TblIns.exact, Function.update_of_ne h3, k₂ x h0 h1 h2 h4]

/-- Variables an entry keeps. -/
def tblFoldKeepE : List (Fin 60) := [18, 19, 21, 22, 34, 35, 37, 38, 39, 41, 42, 43, 48, 49, 50, 51,
  52, 55, 56, 59]

theorem tblFoldEntry_keep : ∀ x ∈ tblFoldKeepE, x ∉ tblFoldEntry.tblDsts := by decide

/-- One column of a row: its index `56 + 50` into `53`, then the entry. -/
theorem tblFoldCol_do {A W w : ℕ} (s' : TblSt 60 A) {s t α P wd i N st0 j : ℕ} [NeZero s]
    (h18 : s'.val 18 = piN P) (h19 : s'.val 19 = P) (h21 : s'.val 21 = s * s)
    (h22 : s'.val 22 = 1) (h34 : s'.val 34 = s) (h35 : s'.val 35 = t) (h43 : s'.val 43 = α * α)
    (h38 : s'.val 38 = 0) (h39 : s'.val 39 = wd)
    (hrow : i < s → s'.val 37 = (NLogN.PhaseCellMatrix.foldAt s i).val ∧
      s'.val 41 = t * (NLogN.PhaseCellMatrix.foldAt s i).val % s ∧
      s'.val 42 = if t * (NLogN.PhaseCellMatrix.foldAt s i).val % s +
        t * (NLogN.PhaseCellMatrix.foldAt s i).val % s < s then 0 else s)
    (h48 : s'.val 48 = i) (h50 : s'.val 50 = j) (h56 : s'.val 56 = st0) (h55 : s'.val 55 = 2 ^ P)
    (h59 : s'.val 59 = 2) (hws : 2 * wd + 1 < s) (hP : 13 ≤ P) (hW : TblOffW W P α s t wd N)
    (hsW : 2 * s < 2 ^ W) (hjW : st0 + j < 2 ^ W) :
    TblDo A W w (tblBlock 60 [] (.add 56 50 53) ;; tblFoldEntry) s' (fun s'' =>
      s''.acc = (tblFoldSyms A w s t α P wd i (st0 + j)).reverse ++ s'.acc ∧
      ∀ x ∈ tblFoldKeepE, s''.val x = s'.val x) (1 + (310 * P + 200)) := by
  refine (TblDo.block [] (.add 56 50 53) ?_ rfl).seq (fun s₃ hs₃ => ?_)
  · simp [tblFitsList, TblIns.fits, h56, h50]; exact hjW
  subst hs₃
  set s₃ := tblExactList A w ([] ++ [.add 56 50 53]) s'
  have w3 : ∀ x : Fin 60, x ≠ 53 → s₃.val x = s'.val x := by
    intro x hx
    simp [s₃, tblExactList, TblIns.exact, Function.update_of_ne hx]
  have w53 : s₃.val 53 = st0 + j := by simp [s₃, tblExactList, TblIns.exact, h56, h50]
  have wacc : s₃.acc = s'.acc := by simp [s₃, tblExactList, TblIns.exact]
  have he := (tblFoldEntry_do (W := W) (w := w) s₃ (s := s) (t := t) (α := α) (P := P) (wd := wd)
    (i := i) (c := st0 + j) (N := N)
    (by rw [w3 18 (by decide), h18]) (by rw [w3 19 (by decide), h19])
    (by rw [w3 21 (by decide), h21]) (by rw [w3 22 (by decide), h22])
    (by rw [w3 34 (by decide), h34]) (by rw [w3 35 (by decide), h35])
    (by rw [w3 43 (by decide), h43]) (by rw [w3 38 (by decide), h38])
    (by rw [w3 39 (by decide), h39])
    (fun hi => by
      obtain ⟨a, b, c⟩ := hrow hi
      exact ⟨by rw [w3 37 (by decide), a], by rw [w3 41 (by decide), b], by rw [w3 42 (by decide), c]⟩)
    (by rw [w3 48 (by decide), h48]) w53 (by rw [w3 55 (by decide), h55])
    (by rw [w3 59 (by decide), h59]) hws hP hW hsW).keep
  refine he.mono (fun s'' ⟨hacc'', hk⟩ => ⟨by rw [hacc'', wacc], fun x hx => ?_⟩) le_rfl
  rw [hk x (tblFoldEntry_keep x hx), w3 x (by
    simp only [tblFoldKeepE, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)]

/-- Variables a row keeps. -/
def tblFoldLst : List (Fin 60) := [18, 19, 21, 22, 34, 35, 38, 39, 43, 48, 49, 51, 52, 55, 59]

/-- Variables the column loop keeps. -/
def tblFoldL2 : List (Fin 60) := [18, 19, 21, 22, 34, 35, 37, 38, 39, 41, 42, 43, 48, 49, 51, 52, 55,
  56, 59]

theorem tblFoldLst_pre : ∀ x ∈ tblFoldLst, x ≠ 0 ∧ x ≠ 37 ∧ x ≠ 41 ∧ x ≠ 42 ∧ x ≠ 58 := by decide
theorem tblFoldLst_ne56 : ∀ x ∈ tblFoldLst, x ≠ 56 := by decide
theorem tblFoldLst_L2 : ∀ x ∈ tblFoldLst, x ∈ tblFoldL2 := by decide
theorem tblFoldL2_ne50 : ∀ x ∈ tblFoldL2, x ≠ 50 := by decide
theorem tblFoldL2_keepE : ∀ x ∈ tblFoldL2, x ∈ tblFoldKeepE := by decide

/-- One folded row: the entries of row `i` on its `2B+1` columns. -/
theorem tblFoldRow_do {A W w : ℕ} (st : TblSt 60 A) {s t α P wd B i N : ℕ} [NeZero s]
    (h18 : st.val 18 = piN P) (h19 : st.val 19 = P) (h21 : st.val 21 = s * s)
    (h22 : st.val 22 = 1) (h34 : st.val 34 = s) (h35 : st.val 35 = t) (h43 : st.val 43 = α * α)
    (h38 : st.val 38 = 0) (h39 : st.val 39 = wd) (h48 : st.val 48 = i) (h51 : st.val 51 = 2 * B + 1)
    (h52 : st.val 52 = B) (h55 : st.val 55 = 2 ^ P) (h59 : st.val 59 = 2)
    (hws : 2 * wd + 1 < s) (hP : 13 ≤ P) (hW : TblOffW W P α s t wd N)
    (hsW : 2 * s * (t + 1) < 2 ^ W) (hiW : i + 2 * B + 1 < 2 ^ W) :
    TblDo A W w tblFoldRow st (fun s' => s'.acc =
      ((List.range (2 * B + 1)).flatMap fun j =>
        tblFoldSyms A w s t α P wd i (i - min i B + j)).reverse ++ st.acc ∧
      ∀ x ∈ tblFoldLst, s'.val x = st.val x)
      (11 + 2 + (1 + ((2 * B + 1) * (310 * P + 201 + 1 + 2) + 2))) := by
  have hs0 : 0 < s := Nat.pos_of_ne_zero (NeZero.ne s)
  -- phase 1: the row prelude
  have h₁ : TblDo A W w (.ite 48 34 tblFoldRowPre (.ins (.zero 58))) st (fun s₁ =>
      s₁.acc = st.acc ∧ (∀ x ∈ tblFoldLst, s₁.val x = st.val x) ∧
      (i < s → s₁.val 37 = (NLogN.PhaseCellMatrix.foldAt s i).val ∧
        s₁.val 41 = t * (NLogN.PhaseCellMatrix.foldAt s i).val % s ∧
        s₁.val 42 = (if t * (NLogN.PhaseCellMatrix.foldAt s i).val % s +
          t * (NLogN.PhaseCellMatrix.foldAt s i).val % s < s then 0 else s))) 11 := by
    by_cases hi : i < s
    · refine TblDo.iteT (by rw [h48, h34]; exact hi) ((tblFoldRowPre_do (W := W) (w := w) st h48 hi h59
        h22 h34 h35 hsW).mono (fun s' ⟨a, b, c, d, e⟩ => ⟨d, fun x hx => e x (tblFoldLst_pre x hx).1
          (tblFoldLst_pre x hx).2.1 (tblFoldLst_pre x hx).2.2.1 (tblFoldLst_pre x hx).2.2.2.1
          (tblFoldLst_pre x hx).2.2.2.2, fun _ => ⟨a, b, c⟩⟩) le_rfl)
    · refine TblDo.iteF (by rw [h48, h34]; exact hi) (TblDo.insX (.zero 58) trivial ?_) |>.mono
        (fun _ h => h) (by norm_num)
      refine ⟨by simp [TblIns.exact], fun x hx => ?_, fun h => absurd h hi⟩
      simp [TblIns.exact, Function.update_of_ne (tblFoldLst_pre x hx).2.2.2.2]
  refine h₁.seq (K₂ := 2 + (1 + ((2 * B + 1) * (310 * P + 201 + 1 + 2) + 2)))
    (fun s₁ ⟨acc₁, keep₁, row₁⟩ => ?_) |>.mono (fun _ h => h) (by omega)
  have g : ∀ x ∈ tblFoldLst, s₁.val x = st.val x := keep₁
  have g48 : s₁.val 48 = i := by rw [g 48 (by decide), h48]
  have g52 : s₁.val 52 = B := by rw [g 52 (by decide), h52]
  -- phase 2: the first column
  have h₂ : TblDo A W w (.ite 48 52 (.ins (.zero 56)) (.ins (.sub 48 52 56))) s₁
      (fun s₂ => s₂ = ⟨Function.update s₁.val 56 (i - min i B), s₁.acc⟩) 2 := by
    by_cases hib : i < B
    · exact TblDo.iteT (by rw [g48, g52]; exact hib) (TblDo.insX (.zero 56) trivial
        (by simp [TblIns.exact, show i - min i B = 0 by omega]))
    · exact TblDo.iteF (by rw [g48, g52]; exact hib) (TblDo.insX (.sub 48 52 56)
        (by simp [TblIns.fits, g48, g52]; omega)
        (by simp [TblIns.exact, g48, g52, show min i B = B by omega]))
  refine h₂.seq (fun s₂ hs₂ => ?_)
  subst hs₂
  set st0 := i - min i B with hst0
  set s₂ : TblSt 60 A := ⟨Function.update s₁.val 56 st0, s₁.acc⟩
  have v2 : ∀ x ∈ tblFoldLst, s₂.val x = st.val x := by
    intro x hx
    simp [s₂, Function.update_of_ne (tblFoldLst_ne56 x hx), g x hx]
  have v18 : s₂.val 18 = piN P := by rw [v2 18 (by decide), h18]
  have v19 : s₂.val 19 = P := by rw [v2 19 (by decide), h19]
  have v21 : s₂.val 21 = s * s := by rw [v2 21 (by decide), h21]
  have v22 : s₂.val 22 = 1 := by rw [v2 22 (by decide), h22]
  have v34 : s₂.val 34 = s := by rw [v2 34 (by decide), h34]
  have v35 : s₂.val 35 = t := by rw [v2 35 (by decide), h35]
  have v38 : s₂.val 38 = 0 := by rw [v2 38 (by decide), h38]
  have v39 : s₂.val 39 = wd := by rw [v2 39 (by decide), h39]
  have v43 : s₂.val 43 = α * α := by rw [v2 43 (by decide), h43]
  have v48 : s₂.val 48 = i := by rw [v2 48 (by decide), h48]
  have v51 : s₂.val 51 = 2 * B + 1 := by rw [v2 51 (by decide), h51]
  have v55 : s₂.val 55 = 2 ^ P := by rw [v2 55 (by decide), h55]
  have v59 : s₂.val 59 = 2 := by rw [v2 59 (by decide), h59]
  have v56 : s₂.val 56 = st0 := by simp [s₂]
  have vrow : i < s → s₂.val 37 = (NLogN.PhaseCellMatrix.foldAt s i).val ∧
      s₂.val 41 = t * (NLogN.PhaseCellMatrix.foldAt s i).val % s ∧
      s₂.val 42 = (if t * (NLogN.PhaseCellMatrix.foldAt s i).val % s +
        t * (NLogN.PhaseCellMatrix.foldAt s i).val % s < s then 0 else s) := by
    intro hi
    obtain ⟨a, b, c⟩ := row₁ hi
    exact ⟨by simp [s₂, a], by simp [s₂, b], by simp [s₂, c]⟩
  set F : ℕ → List (Fin (A + 4)) := fun j => tblFoldSyms A w s t α P wd i (st0 + j)
  have hNW : 2 * B + 1 < 2 ^ W := by omega
  have h2s : 2 * s < 2 ^ W := lt_of_le_of_lt (Nat.le_mul_of_pos_right _ (Nat.succ_pos t)) hsW
  have hst0 : st0 ≤ i := Nat.sub_le _ _
  refine TblDo.for (2 * B + 1) (310 * P + 201) v51 hNW (by decide)
    (fun j s' => s'.acc = ((List.range j).flatMap F).reverse ++ st.acc ∧ ∀ x ∈ tblFoldL2, s'.val x = s₂.val x)
    ⟨by simp [s₂, acc₁], fun x hx => ?_⟩ ?_ ?_
  · simp [Function.update_of_ne (tblFoldL2_ne50 x hx)]
  · intro j hj s' ⟨hacc, hv⟩ h50 h51
    have u : ∀ x ∈ tblFoldL2, s'.val x = s₂.val x := hv
    have hc := tblFoldCol_do (W := W) (w := w) s' (s := s) (t := t) (α := α) (P := P) (wd := wd)
      (i := i) (N := N) (st0 := st0) (j := j)
      (by rw [u 18 (by decide), v18]) (by rw [u 19 (by decide), v19])
      (by rw [u 21 (by decide), v21]) (by rw [u 22 (by decide), v22])
      (by rw [u 34 (by decide), v34]) (by rw [u 35 (by decide), v35])
      (by rw [u 43 (by decide), v43]) (by rw [u 38 (by decide), v38])
      (by rw [u 39 (by decide), v39])
      (fun hi => by
        obtain ⟨a, b, c⟩ := vrow hi
        exact ⟨by rw [u 37 (by decide), a], by rw [u 41 (by decide), b],
          by rw [u 42 (by decide), c]⟩)
      (by rw [u 48 (by decide), v48]) h50 (by rw [u 56 (by decide), v56])
      (by rw [u 55 (by decide), v55]) (by rw [u 59 (by decide), v59]) hws hP hW
      h2s (by omega)
    refine hc.mono (fun s'' ⟨hacc'', kE⟩ => ?_) (by omega)
    refine ⟨by rw [kE 50 (by decide), h50], by rw [kE 51 (by decide), h51],
      ?_, fun x hx => ?_⟩
    · show _ = _
      rw [hacc'', hacc, tbl_range_flatMap_succ F j, List.append_assoc]
    · show (Function.update s''.val 50 (j + 1)) x = _
      rw [Function.update_of_ne (tblFoldL2_ne50 x hx), kE x (tblFoldL2_keepE x hx), u x hx]
  · intro s' ⟨hacc, hv⟩ _ _
    refine ⟨hacc, fun x hx => ?_⟩
    rw [hv x (tblFoldLst_L2 x hx), v2 x hx]

/-- The setup: `π`, the constants `0`, `1`, `2`, `s²`, `α²`, and `2^P` into `55`. -/
def tblFoldSetup : TblCode 60 :=
  tblPiSetup48.rename tblFoldMap ;;
    tblBlock 60 [.zero 38, .zero 22, .inc 22, .mul 34 34 21, .mul 36 36 43, .add 22 22 59, .zero 55]
      (.inc 55) ;;
    tblFor 50 19 (.ins (.add 55 55 55))

/-- The folded row stream. -/
def tblFoldStreamCode : TblCode 60 := tblFoldSetup ;; tblFor 48 49 tblFoldRow

theorem tblFoldSetup_do {A W w : ℕ} (st : TblSt 60 A) {s α P : ℕ}
    (h19 : st.val 19 = P) (h34 : st.val 34 = s) (h36 : st.val 36 = α) (hP : 2 ≤ P)
    (hW : 5 * P + 16 ≤ W) (hsW : s * s < 2 ^ W) (hαW : α * α < 2 ^ W) (hPW : 2 ^ P < 2 ^ W) :
    TblDo A W w tblFoldSetup st (fun s' => s'.val 18 = piN P ∧ s'.val 19 = P ∧
      s'.val 21 = s * s ∧ s'.val 22 = 1 ∧ s'.val 38 = 0 ∧ s'.val 43 = α * α ∧ s'.val 55 = 2 ^ P ∧
      s'.val 59 = 2 ∧ s'.acc = st.acc ∧
      ∀ x : Fin 60, x ∈ ([34, 35, 36, 39, 48, 49, 51, 52] : List (Fin 60)) → s'.val x = st.val x)
      (1 + (150 * P + 400) + 8 + (1 + (P * (1 + 1 + 2) + 2))) := by
  have hPW' : P < 2 ^ W := lt_of_lt_of_le (Nat.lt_two_pow_self) (Nat.pow_le_pow_right (by norm_num)
    (by omega))
  have h19' : (st.restrict tblFoldMap).val 19 = P := h19
  have hpi := (tbl_pi48_do (A := A) (W := W) (w := w) (st.restrict tblFoldMap) (p := P) h19' hP hW).rename
    tblFoldMap_inj
  unfold tblFoldSetup
  refine (TblDo.seq hpi (K₂ := 8 + (1 + (P * (1 + 1 + 2) + 2))) ?_).mono (fun _ h => h) (by omega)
  intro s₁ hs₁
  obtain ⟨⟨p18, pacc, pkeep⟩, poth⟩ := hs₁
  have k₁ : ∀ x : Fin 60, 19 ≤ x.val → s₁.val x = st.val x := by
    intro x hx
    by_cases hx48 : x.val < 48
    · have := pkeep ⟨x.val, hx48⟩ hx
      simpa [TblSt.restrict, tblFoldMap] using this
    · exact poth x (fun y hy => by have := congrArg Fin.val hy; simp [tblFoldMap] at this; omega)
  have v18 : s₁.val 18 = piN P := p18
  have v19 : s₁.val 19 = P := by rw [k₁ 19 (by decide), h19]
  have v34 : s₁.val 34 = s := by rw [k₁ 34 (by decide), h34]
  have v36 : s₁.val 36 = α := by rw [k₁ 36 (by decide), h36]
  have vacc : s₁.acc = st.acc := pacc
  refine (TblDo.block [.zero 38, .zero 22, .inc 22, .mul 34 34 21, .mul 36 36 43, .add 22 22 59,
    .zero 55] (.inc 55) ?_ rfl).seq (K₂ := 1 + (P * (1 + 1 + 2) + 2)) (fun s₂ hs₂ => ?_) |>.mono
    (fun _ h => h) (by simp)
  · simp [tblFitsList, TblIns.fits, TblIns.exact, v34, v36]
    refine ⟨by omega, hsW, hαW, by omega, by omega⟩
  subst hs₂
  set s₂ := tblExactList A w ([.zero 38, .zero 22, .inc 22, .mul 34 34 21, .mul 36 36 43,
    .add 22 22 59, .zero 55] ++ [.inc 55]) s₁
  have w2 : ∀ x : Fin 60, x ∉ ([38, 22, 21, 43, 59, 55] : List (Fin 60)) → s₂.val x = s₁.val x := by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
    simp [s₂, tblExactList, TblIns.exact, Function.update_of_ne hx.1, Function.update_of_ne hx.2.1,
      Function.update_of_ne hx.2.2.1, Function.update_of_ne hx.2.2.2.1,
      Function.update_of_ne hx.2.2.2.2.1, Function.update_of_ne hx.2.2.2.2.2]
  have e : s₂.val 21 = s * s ∧ s₂.val 22 = 1 ∧ s₂.val 38 = 0 ∧ s₂.val 43 = α * α ∧
      s₂.val 55 = 1 ∧ s₂.val 59 = 2 ∧ s₂.acc = st.acc := by
    simp [s₂, tblExactList, TblIns.exact, v34, v36, vacc]
  obtain ⟨e21, e22, e38, e43, e55, e59, eacc⟩ := e
  refine TblDo.for P 1 (by rw [w2 19 (by decide), v19]) hPW' (by decide)
    (fun j s' => s'.val 55 = 2 ^ j ∧ s'.acc = st.acc ∧
      ∀ x : Fin 60, x ≠ 50 → x ≠ 55 → s'.val x = s₂.val x)
    ⟨by simp [e55], by simp [eacc], fun x h1 h2 => by simp [Function.update_of_ne h1]⟩ ?_ ?_
  · intro j hj s' ⟨a, b, c⟩ hi hn
    refine TblDo.insX (.add 55 55 55) (by
      simp only [TblIns.fits, a]
      calc 2 ^ j + 2 ^ j = 2 ^ (j + 1) := by ring
        _ ≤ 2 ^ P := Nat.pow_le_pow_right (by norm_num) hj
        _ < 2 ^ W := hPW) ?_ |>.mono (fun _ h => h) (by norm_num)
    refine ⟨by simp [TblIns.exact, hi], by simp [TblIns.exact, hn], ?_, ?_, fun x h1 h2 => ?_⟩
    · simp [TblIns.exact, a, pow_succ]; ring
    · simp [TblIns.exact, b]
    · simp [TblIns.exact, Function.update_of_ne h1, Function.update_of_ne h2, c x h1 h2]
  · intro s' ⟨a, b, c⟩ _ _
    refine ⟨by rw [c 18 (by decide) (by decide), w2 18 (by decide), v18],
      by rw [c 19 (by decide) (by decide), w2 19 (by decide), v19],
      by rw [c 21 (by decide) (by decide), e21], by rw [c 22 (by decide) (by decide), e22],
      by rw [c 38 (by decide) (by decide), e38], by rw [c 43 (by decide) (by decide), e43], a,
      by rw [c 59 (by decide) (by decide), e59], b, fun x hx => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      rw [c _ (by decide) (by decide), w2 _ (by decide), k₁ _ (by decide)]

/-- The emitted stream: rows `0, …, NR-1`, in row `i` the `2B+1` folded entries. -/
def tblFoldStream (A w s t α P wd B NR : ℕ) [NeZero s] : List (Fin (A + 4)) :=
  (List.range NR).flatMap fun i => (List.range (2 * B + 1)).flatMap fun j =>
    tblFoldSyms A w s t α P wd i (i - min i B + j)

theorem tblFoldLst_ne48 : ∀ x ∈ tblFoldLst, x ≠ 48 → x ∈ ([18, 19, 21, 22, 34, 35, 38, 39, 43, 49,
    51, 52, 55, 59] : List (Fin 60)) := by decide

/-- **The folded row stream.** -/
theorem tblFoldStream_do {A W w : ℕ} (st : TblSt 60 A) {s t α P wd B NR N : ℕ} [NeZero s]
    (h19 : st.val 19 = P) (h34 : st.val 34 = s) (h35 : st.val 35 = t) (h36 : st.val 36 = α)
    (h39 : st.val 39 = wd) (h49 : st.val 49 = NR) (h51 : st.val 51 = 2 * B + 1) (h52 : st.val 52 = B)
    (hws : 2 * wd + 1 < s) (hP : 13 ≤ P) (hW : TblOffW W P α s t wd N) (hW5 : 5 * P + 16 ≤ W)
    (hsW : 2 * s * (t + 1) < 2 ^ W) (hss : s * s < 2 ^ W) (hαW : α * α < 2 ^ W)
    (hPW : 2 ^ P < 2 ^ W) (hNW : NR + 2 * B + 1 < 2 ^ W) :
    TblDo A W w tblFoldStreamCode st (fun s' =>
      s'.acc = (tblFoldStream A w s t α P wd B NR).reverse ++ st.acc)
      (1 + (150 * P + 400) + 8 + (1 + (P * (1 + 1 + 2) + 2)) +
        (1 + (NR * (11 + 2 + (1 + ((2 * B + 1) * (310 * P + 201 + 1 + 2) + 2)) + 1 + 2) + 2))) := by
  unfold tblFoldStreamCode
  refine (tblFoldSetup_do (W := W) (w := w) st h19 h34 h36 (by omega) hW5 hss hαW hPW).seq ?_
  intro s₁ ⟨a18, a19, a21, a22, a38, a43, a55, a59, aacc, akeep⟩
  have b34 : s₁.val 34 = s := by rw [akeep 34 (by decide), h34]
  have b35 : s₁.val 35 = t := by rw [akeep 35 (by decide), h35]
  have b39 : s₁.val 39 = wd := by rw [akeep 39 (by decide), h39]
  have b49 : s₁.val 49 = NR := by rw [akeep 49 (by decide), h49]
  have b51 : s₁.val 51 = 2 * B + 1 := by rw [akeep 51 (by decide), h51]
  have b52 : s₁.val 52 = B := by rw [akeep 52 (by decide), h52]
  set R : ℕ → List (Fin (A + 4)) := fun i => (List.range (2 * B + 1)).flatMap fun j =>
    tblFoldSyms A w s t α P wd i (i - min i B + j)
  refine TblDo.for NR _ b49 (by omega) (by decide)
    (fun j s' => s'.acc = ((List.range j).flatMap R).reverse ++ st.acc ∧
      ∀ x ∈ tblFoldLst, x ≠ 48 → s'.val x = s₁.val x)
    ⟨by simp [aacc], fun x hx h48 => by simp [Function.update_of_ne h48]⟩ ?_ ?_
  · intro j hj s' ⟨hacc, hv⟩ hi hn
    have u : ∀ x ∈ tblFoldLst, x ≠ 48 → s'.val x = s₁.val x := hv
    have hr := tblFoldRow_do (W := W) (w := w) s' (s := s) (t := t) (α := α) (P := P) (wd := wd)
      (B := B) (i := j) (N := N)
      (by rw [u 18 (by decide) (by decide), a18]) (by rw [u 19 (by decide) (by decide), a19])
      (by rw [u 21 (by decide) (by decide), a21]) (by rw [u 22 (by decide) (by decide), a22])
      (by rw [u 34 (by decide) (by decide), b34]) (by rw [u 35 (by decide) (by decide), b35])
      (by rw [u 43 (by decide) (by decide), a43]) (by rw [u 38 (by decide) (by decide), a38])
      (by rw [u 39 (by decide) (by decide), b39]) hi
      (by rw [u 51 (by decide) (by decide), b51]) (by rw [u 52 (by decide) (by decide), b52])
      (by rw [u 55 (by decide) (by decide), a55]) (by rw [u 59 (by decide) (by decide), a59])
      hws hP hW hsW (by omega)
    refine hr.mono (fun s'' ⟨hacc'', hk⟩ => ⟨by rw [hk 48 (by decide), hi],
      by rw [hk 49 (by decide), hn], ?_, fun x hx h48 => ?_⟩) le_rfl
    · show _ = _
      rw [hacc'', hacc, tbl_range_flatMap_succ R j, List.append_assoc]
    · show (Function.update s''.val 48 (j + 1)) x = _
      rw [Function.update_of_ne h48, hk x hx, u x hx h48]
  · intro s' ⟨hacc, _⟩ _ _
    exact hacc

theorem tblFoldStream_cstream (A w s t α P wd B NR : ℕ) [NeZero s] :
    tblFoldStream A w s t α P wd B NR = cstream A w
      (((List.range' 0 NR).map (Mult.BandFactor.foldRowZ s t α P wd B)).flatten.map
        fun x => (⟨x, 0⟩ : GaussianInt)) := by
  have hrow : ∀ i, (List.range (2 * B + 1)).flatMap (fun j =>
      tblFoldSyms A w s t α P wd i (i - min i B + j)) =
      cstream A w ((Mult.BandFactor.foldRowZ s t α P wd B i).map fun x => (⟨x, 0⟩ : GaussianInt)) := by
    intro i
    simp only [Mult.BandFactor.foldRowZ, List.range'_eq_map_range, cstream, List.map_map,
      List.flatMap_map]
    rfl
  have hl : ∀ l : List ℕ, l.flatMap (fun i => (List.range (2 * B + 1)).flatMap (fun j =>
      tblFoldSyms A w s t α P wd i (i - min i B + j))) =
      cstream A w ((l.map (Mult.BandFactor.foldRowZ s t α P wd B)).flatten.map
        fun x => (⟨x, 0⟩ : GaussianInt)) := by
    intro l
    induction l with
    | nil => rfl
    | cons i l ih =>
      rw [List.flatMap_cons, ih, hrow, List.map_cons, List.flatten_cons, List.map_append,
        cstream_append]
  rw [tblFoldStream, hl, List.range_eq_range']

theorem length_tblFoldStream (A w s t α P wd B NR : ℕ) [NeZero s] :
    (tblFoldStream A w s t α P wd B NR).length = NR * (2 * B + 1) * w := by
  simp [tblFoldStream, tblFoldSyms, List.length_flatMap, coeffSyms, List.sum_replicate]
  ring

section Host

variable {T Q A : ℕ} {U : Type} {P' : Type} {body : P' → IntegerMultBounds.MathlibTM2.Host.Pr P' T Q A U}
  {rg : TblR 60 → Fin T}

/-- **The folded row stream on the host.** -/
theorem tblFoldStream_host (hrg : Function.Injective rg) {out : Fin T} (hout : ∀ r, rg r ≠ out)
    {W w : ℕ} (wl nl : List (Fin (A + 4))) (hwl : wl.length = W) (hnl : nl.length = w)
    (hw : w ≤ W) (st : TblSt 60 A) (hst : ∀ j, st.val j < 2 ^ W) (hacc : st.acc = [])
    {s t α P wd B NR N : ℕ} [NeZero s]
    (h19 : st.val 19 = P) (h34 : st.val 34 = s) (h35 : st.val 35 = t) (h36 : st.val 36 = α)
    (h39 : st.val 39 = wd) (h49 : st.val 49 = NR) (h51 : st.val 51 = 2 * B + 1) (h52 : st.val 52 = B)
    (hws : 2 * wd + 1 < s) (hP : 13 ≤ P) (hW : TblOffW W P α s t wd N) (hW5 : 5 * P + 16 ≤ W)
    (hsW : 2 * s * (t + 1) < 2 ^ W) (hss : s * s < 2 ^ W) (hαW : α * α < 2 ^ W)
    (hPW : 2 ^ P < 2 ^ W) (hNW : NR + 2 * B + 1 < 2 ^ W)
    (v : IntegerMultBounds.MathlibTM2.Host.HS T Q A U) (S : IntegerMultBounds.MathlibTM2.Host.Stacks T A)
    (hS : tblHolds rg S (tblRho W wl nl st)) :
    ∃ v' S' m, v'.user = v.user ∧
      m ≤ (1 + (150 * P + 400) + 8 + (1 + (P * (1 + 1 + 2) + 2)) +
        (1 + (NR * (11 + 2 + (1 + ((2 * B + 1) * (310 * P + 201 + 1 + 2) + 2)) + 1 + 2) + 2))) *
          tblC W w + 2 * (NR * (2 * B + 1) * w) + 2 ∧
      IntegerMultBounds.MathlibTM2.Stack.Exec body (tblHost rg tblFoldStreamCode out)
        (IntegerMultBounds.MathlibTM2.Host.mk v S) m (IntegerMultBounds.MathlibTM2.Host.mk v' S') ∧
      S'.R out = tblFoldStream A w s t α P wd B NR ++ S.R out ∧
      (∃ st' : TblSt 60 A, tblHolds rg S' (tblRho W wl nl st')) ∧
      S'.inp = S.inp ∧ S'.out = S.out ∧ S'.L = S.L ∧
      ∀ k, k ≠ out → (∀ r, rg r ≠ k) → S'.R k = S.R k := by
  have h := tbl_stream_host (body := body) hrg hout wl nl hwl hnl hw
    (tblFoldStream_do (W := W) (w := w) st h19 h34 h35 h36 h39 h49 h51 h52 hws hP hW hW5 hsW hss hαW
      hPW hNW) hst hacc v S hS
  rwa [length_tblFoldStream] at h

end Host

end IntegerMultBounds.MathlibTM2.Fast
