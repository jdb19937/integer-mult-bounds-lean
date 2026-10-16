module

public import IntegerMultBounds.Schoenhage.DriverBank
public import IntegerMultBounds.Schoenhage.ConvProgram
public import IntegerMultBounds.Schoenhage.ChunkRound
public import IntegerMultBounds.Schoenhage.LayoutMachines

/-! The primitives' tapes inside the drivers' bank: the twist machine on its
block (`twT`), the prefix-round machine on the ring product's bank with its five
data tapes on named tapes 0–4 (`pslot`), and what each call sees and changes
(`dstate_comp_twT`, `upd_dstate_twT`, `dstate_comp_pslot`, `upd_dstate_pslot`). -/

@[expose] public section

set_option maxRecDepth 10000

namespace IntegerMultBounds.Schoenhage

open Machine Strm Tp Schedule

variable {tL nL : ℕ}

/-! ### The twist block -/

theorem twT_injective : Function.Injective (twT tL nL) := fun _ _ h => twT_inj h

theorem dstate_comp_twT (v : Fin 13 → WTape) (tw : Fin 29 → WTape) : dstate tL nL v tw ∘ twT tL nL = tw := by
  funext j; exact dstate_twT v tw j

theorem upd_dstate_twT (v : Fin 13 → WTape) (tw tw' : Fin 29 → WTape) :
    upd (dstate tL nL v tw) (twT tL nL) tw' = dstate tL nL v tw' := by
  apply upd_eq_of _ twT_injective
  · intro j; exact dstate_twT v tw' j
  · intro x hx
    by_cases h1 : x.val < 13
    · rw [eq_nm h1, dstate_nm, dstate_nm]
    · by_cases h2 : 20 ≤ x.val ∧ x.val < 49
      · exact absurd (eq_twT h2.1 h2.2).symm (hx _)
      · rw [dstate_other _ _ (by omega) (by omega), dstate_other _ _ (by omega) (by omega)]

/-! ### The prefix-round machine -/

/-- The ring product's bank inside the drivers' bank: `zF, zO, kw, kS, xP` on named tapes 0–4. -/
def pslot (tL nL : ℕ) : Fin 𝕌 → Fin (DB tL nL) := fun x =>
  if x = zF then nm tL nL 0 else if x = zO then nm tL nL 1 else if x = kw then nm tL nL 2
  else if x = kS then nm tL nL 3 else if x = xP then nm tL nL 4
  else ⟨50 + x.val, by have := x.isLt; change x.val < 91 at this; unfold DB; omega⟩

theorem pslot_injective : Function.Injective (pslot tL nL) := by
  intro x y e
  have e' := congrArg Fin.val e
  unfold pslot nm at e'
  have hx := x.isLt; have hy := y.isLt
  change x.val < 91 at hx; change y.val < 91 at hy
  apply Fin.ext
  split_ifs at e' <;> (try subst_vars) <;> simp only [Fin.ext_iff] at * <;> first | rfl | omega |
    (simp at *; omega)

/-- What the prefix-round machine sees: its five data tapes from named tapes 0–4, all else empty. -/
def pview (v : Fin 13 → WTape) : Fin 𝕌 → WTape := fun x =>
  if x = zF then v 0 else if x = zO then v 1 else if x = kw then v 2 else if x = kS then v 3
  else if x = xP then v 4 else emp

theorem pslot_high {x : Fin 𝕌} (h1 : x ≠ zF) (h2 : x ≠ zO) (h3 : x ≠ kw) (h4 : x ≠ kS) (h5 : x ≠ xP) :
    (pslot tL nL x).val = 50 + x.val := by
  simp [pslot, h1, h2, h3, h4, h5]

theorem dstate_comp_pslot (v : Fin 13 → WTape) (tw : Fin 29 → WTape) :
    dstate tL nL v tw ∘ pslot tL nL = pview v := by
  funext x
  simp only [Function.comp_apply, pview]
  by_cases h1 : x = zF
  · subst h1; simp (config := {decide := true}) [pslot, dstate_nm]
  · by_cases h2 : x = zO
    · subst h2; simp (config := {decide := true}) [pslot, dstate_nm]
    · by_cases h3 : x = kw
      · subst h3; simp (config := {decide := true}) [pslot, dstate_nm]
      · by_cases h4 : x = kS
        · subst h4; simp (config := {decide := true}) [pslot, dstate_nm]
        · by_cases h5 : x = xP
          · subst h5; simp (config := {decide := true}) [pslot, dstate_nm]
          · simp only [h1, h2, h3, h4, h5, ↓reduceIte]
            have := pslot_high (tL := tL) (nL := nL) h1 h2 h3 h4 h5
            exact dstate_other _ _ (by omega) (by omega)

/-- The named tapes after a prefix-round call. -/
def pnew (v : Fin 13 → WTape) (τ' : Fin 𝕌 → WTape) : Fin 13 → WTape := fun i =>
  if i = 0 then τ' zF else if i = 1 then τ' zO else if i = 2 then τ' kw else if i = 3 then τ' kS
  else if i = 4 then τ' xP else v i

theorem upd_dstate_pslot (v : Fin 13 → WTape) (tw : Fin 29 → WTape) (τ' : Fin 𝕌 → WTape)
    (hτ : ∀ x, x ≠ zF → x ≠ zO → x ≠ kw → x ≠ kS → x ≠ xP → τ' x = emp) :
    upd (dstate tL nL v tw) (pslot tL nL) τ' = dstate tL nL (pnew v τ') tw := by
  apply upd_eq_of _ pslot_injective
  · intro x
    by_cases h1 : x = zF
    · subst h1; simp (config := {decide := true}) [pslot, dstate_nm, pnew]
    · by_cases h2 : x = zO
      · subst h2; simp (config := {decide := true}) [pslot, dstate_nm, pnew]
      · by_cases h3 : x = kw
        · subst h3; simp (config := {decide := true}) [pslot, dstate_nm, pnew]
        · by_cases h4 : x = kS
          · subst h4; simp (config := {decide := true}) [pslot, dstate_nm, pnew]
          · by_cases h5 : x = xP
            · subst h5; simp (config := {decide := true}) [pslot, dstate_nm, pnew]
            · have := pslot_high (tL := tL) (nL := nL) h1 h2 h3 h4 h5
              rw [dstate_other _ _ (by omega) (by omega), hτ x h1 h2 h3 h4 h5]
  · intro x hx
    by_cases h1 : x.val < 13
    · rw [eq_nm h1, dstate_nm, dstate_nm]
      have n0 : (⟨x.val, h1⟩ : Fin 13) ≠ 0 := fun e => hx zF (by
        rw [show pslot tL nL zF = nm tL nL 0 by simp (config := {decide := true}) [pslot], ← e]
        exact (eq_nm h1).symm)
      have n1 : (⟨x.val, h1⟩ : Fin 13) ≠ 1 := fun e => hx zO (by
        rw [show pslot tL nL zO = nm tL nL 1 by simp (config := {decide := true}) [pslot], ← e]
        exact (eq_nm h1).symm)
      have n2 : (⟨x.val, h1⟩ : Fin 13) ≠ 2 := fun e => hx kw (by
        rw [show pslot tL nL kw = nm tL nL 2 by simp (config := {decide := true}) [pslot], ← e]
        exact (eq_nm h1).symm)
      have n3 : (⟨x.val, h1⟩ : Fin 13) ≠ 3 := fun e => hx kS (by
        rw [show pslot tL nL kS = nm tL nL 3 by simp (config := {decide := true}) [pslot], ← e]
        exact (eq_nm h1).symm)
      have n4 : (⟨x.val, h1⟩ : Fin 13) ≠ 4 := fun e => hx xP (by
        rw [show pslot tL nL xP = nm tL nL 4 by simp (config := {decide := true}) [pslot], ← e]
        exact (eq_nm h1).symm)
      simp [pnew, n0, n1, n2, n3, n4]
    · by_cases h2 : 20 ≤ x.val ∧ x.val < 49
      · rw [eq_twT h2.1 h2.2, dstate_twT, dstate_twT]
      · rw [dstate_other _ _ (by omega) (by omega), dstate_other _ _ (by omega) (by omega)]

/-! ### The layer program -/

/-- The layer program's tapes: header on named tape 5, array on named tape 0, the rest private. -/
def lslot (tL nL : ℕ) : Fin tL → Fin (DB tL nL) := fun x =>
  if x.val = 0 then nm tL nL 5 else if x.val = 1 then nm tL nL 0
  else ⟨141 + x.val, by have := x.isLt; unfold DB; omega⟩

theorem lslot_injective : Function.Injective (lslot tL nL) := by
  intro x y e
  have e' := congrArg Fin.val e
  unfold lslot nm at e'
  apply Fin.ext
  split_ifs at e' <;> simp only at * <;> omega

theorem dstate_comp_lslot (_ht : 2 ≤ tL) (v : Fin 13 → WTape) (tw : Fin 29 → WTape) {hdr A : List Bool}
    (h5 : v 5 = reg hdr) (h0 : v 0 = reg A) : dstate tL nL v tw ∘ lslot tL nL = start1 tL hdr A := by
  funext x
  simp only [Function.comp_apply, lslot, start1]
  split_ifs with a b
  · rw [dstate_nm, h5]
  · rw [dstate_nm, h0]
  · exact dstate_other _ _ (by simp; omega) (by simp; omega)

theorem upd_dstate_lslot (ht : 2 ≤ tL) (v : Fin 13 → WTape) (tw : Fin 29 → WTape) (hdr A' : List Bool) :
    upd (dstate tL nL v tw) (lslot tL nL) (start1 tL hdr A') =
      dstate tL nL (Function.update (Function.update v 5 (reg hdr)) 0 (reg A')) tw := by
  apply upd_eq_of _ lslot_injective
  · intro x
    simp only [lslot, start1]
    split_ifs with a b
    · rw [dstate_nm]; simp
    · rw [dstate_nm]; simp
    · exact dstate_other _ _ (by simp; omega) (by simp; omega)
  · intro x hx
    by_cases h1 : x.val < 13
    · rw [eq_nm h1, dstate_nm, dstate_nm]
      have n5 : (⟨x.val, h1⟩ : Fin 13) ≠ 5 := fun e => hx ⟨0, by omega⟩ (by
        rw [show lslot tL nL ⟨0, by omega⟩ = nm tL nL 5 by simp [lslot], ← e]; exact (eq_nm h1).symm)
      have n0 : (⟨x.val, h1⟩ : Fin 13) ≠ 0 := fun e => hx ⟨1, by omega⟩ (by
        rw [show lslot tL nL ⟨1, by omega⟩ = nm tL nL 0 by simp [lslot], ← e]; exact (eq_nm h1).symm)
      simp [n5, n0]
    · by_cases h2 : 20 ≤ x.val ∧ x.val < 49
      · rw [eq_twT h2.1 h2.2, dstate_twT, dstate_twT]
      · rw [dstate_other _ _ (by omega) (by omega), dstate_other _ _ (by omega) (by omega)]

/-! ### The layout driver -/

/-- The layout driver's bank size. -/
noncomputable abbrev NL : ℕ := Resampling.AxisDriver.NB 1

open Resampling.AxisDriver in
/-- The layout driver's bank: array on named tape 0, script on named tape 7, the rest private. -/
noncomputable def aslot (tL : ℕ) : Fin (NL) → Fin (DB tL (NL)) := fun x =>
  if x = ax 0 then nm tL (NL) 0 else if x = scr then nm tL (NL) 7
  else ⟨160 + tL + x.val, by have := x.isLt; unfold DB; omega⟩

open Resampling.AxisDriver in
theorem aslot_injective : Function.Injective (aslot tL) := by
  intro x y e
  have e' := congrArg Fin.val e
  unfold aslot nm at e'
  have hax : (ax (E := 1) 0).val = SN := by simp [ax_val]
  have hsc : (scr (E := 1)).val = SN + 1 := rfl
  have hx := x.isLt; have hy := y.isLt
  change x.val < SN + 3 at hx; change y.val < SN + 3 at hy
  have h6 := six_le
  apply Fin.ext
  split_ifs at e' with a1 a2 a3 a4 <;> (try subst_vars) <;> simp only [Fin.ext_iff, hax, hsc] at * <;>
    omega

open Resampling.AxisDriver in
/-- The layout bank's tapes: interchange tapes, the array, the script and the junk tape. -/
theorem nl_cases (x : Fin NL) : (∃ i, x = sw i) ∨ x = ax 0 ∨ x = scr ∨ x = jnk := by
  have hx := x.isLt
  change x.val < SN + 3 at hx
  by_cases h1 : x.val < SN
  · exact Or.inl ⟨⟨x.val, h1⟩, Fin.ext (by simp [sw])⟩
  · right
    by_cases h2 : x.val = SN
    · left; exact Fin.ext (by simp [ax_val]; omega)
    · right
      by_cases h3 : x.val = SN + 1
      · left; exact Fin.ext (by simp [scr]; omega)
      · right; exact Fin.ext (by simp [jnk]; omega)

open Resampling.AxisDriver in
theorem aslot_ax : aslot tL (ax 0) = nm tL NL 0 := by simp [aslot]

open Resampling.AxisDriver in
theorem aslot_scr : aslot tL scr = nm tL NL 7 := by
  have : (scr : Fin NL) ≠ ax 0 := fun e => by have := congrArg Fin.val e; simp [scr, ax_val] at this
  simp [aslot, this]

open Resampling.AxisDriver in
theorem aslot_other {x : Fin NL} (h1 : x ≠ ax 0) (h2 : x ≠ scr) : 49 ≤ (aslot tL x).val := by
  simp [aslot, h1, h2]; omega

open Resampling.AxisDriver in
theorem dstate_comp_aslot (v : Fin 13 → WTape) (tw : Fin 29 → WTape) {A : List Bool} {S : WTape}
    (h0 : v 0 = reg A) (h7 : v 7 = S) :
    dstate tL NL v tw ∘ aslot tL = bank (fun _ => emp) 0 A S := by
  have hsx : ∀ i, (sw i : Fin NL) ≠ ax 0 := fun i e => by
    have := congrArg Fin.val e; simp [sw, ax_val] at this; omega
  have hss : ∀ i, (sw i : Fin NL) ≠ scr := fun i e => by
    have := congrArg Fin.val e; simp [sw, scr] at this; omega
  have hjx : (jnk : Fin NL) ≠ ax 0 := fun e => by have := congrArg Fin.val e; simp [jnk, ax_val] at this
  have hjs : (jnk : Fin NL) ≠ scr := fun e => by have := congrArg Fin.val e; simp [jnk, scr] at this
  apply bank_cases
  · intro i
    exact dstate_other _ _ (by have := aslot_other (tL := tL) (hsx i) (hss i); omega)
      (by have := aslot_other (tL := tL) (hsx i) (hss i); omega)
  · intro i
    have hi : i = 0 := Subsingleton.elim _ _
    subst hi
    simp [aslot_ax, dstate_nm, h0]
  · simp [aslot_scr, dstate_nm, h7]
  · exact dstate_other _ _ (by have := aslot_other (tL := tL) hjx hjs; omega)
      (by have := aslot_other (tL := tL) hjx hjs; omega)

open Resampling.AxisDriver in
theorem upd_dstate_aslot (v : Fin 13 → WTape) (tw : Fin 29 → WTape) (A' : List Bool) (S' : WTape) :
    upd (dstate tL NL v tw) (aslot tL) (bank (fun _ => emp) 0 A' S') =
      dstate tL NL (Function.update (Function.update v 0 (reg A')) 7 S') tw := by
  apply upd_eq_of _ aslot_injective
  · intro x
    rcases nl_cases x with ⟨i, rfl⟩ | rfl | rfl | rfl
    · have h1 : (sw i : Fin NL) ≠ ax 0 := fun e => by
        have := congrArg Fin.val e; simp [sw, ax_val] at this; omega
      have h2 : (sw i : Fin NL) ≠ scr := fun e => by
        have := congrArg Fin.val e; simp [sw, scr] at this; omega
      have := aslot_other (tL := tL) h1 h2
      rw [bank_sw, dstate_other _ _ (by omega) (by omega)]
    · rw [aslot_ax, dstate_nm, bank_ax]; simp
    · rw [aslot_scr, dstate_nm, bank_scr]; simp
    · have h1 : (jnk : Fin NL) ≠ ax 0 := fun e => by have := congrArg Fin.val e; simp [jnk, ax_val] at this
      have h2 : (jnk : Fin NL) ≠ scr := fun e => by have := congrArg Fin.val e; simp [jnk, scr] at this
      have := aslot_other (tL := tL) h1 h2
      rw [bank_jnk, dstate_other _ _ (by omega) (by omega)]
  · intro x hx
    by_cases h1 : x.val < 13
    · rw [eq_nm h1, dstate_nm, dstate_nm]
      have n0 : (⟨x.val, h1⟩ : Fin 13) ≠ 0 := fun e => hx (ax 0) (by rw [aslot_ax, ← e]; exact (eq_nm h1).symm)
      have n7 : (⟨x.val, h1⟩ : Fin 13) ≠ 7 := fun e => hx scr (by rw [aslot_scr, ← e]; exact (eq_nm h1).symm)
      simp [n0, n7]
    · by_cases h2 : 20 ≤ x.val ∧ x.val < 49
      · rw [eq_twT h2.1 h2.2, dstate_twT, dstate_twT]
      · rw [dstate_other _ _ (by omega) (by omega), dstate_other _ _ (by omega) (by omega)]

end IntegerMultBounds.Schoenhage
