module

public import IntegerMultBounds.Schoenhage.DriverWords
public import IntegerMultBounds.Schoenhage.TwistBank

/-! The transform drivers' bank (§6 task 6): thirteen named word tapes, the
twist machine's 29 tapes as a persistent block from tape 20, and private
blocks for the other primitives, empty between calls (`dstate`). Updates of a
named tape or a twist tape stay in this form (`update_nm`, `update_tw`). -/

@[expose] public section

namespace IntegerMultBounds.Schoenhage

open Machine

/-- The bank size, for a layer program on `tL` tapes and a layout bank of `nL` tapes. -/
abbrev DB (tL nL : ℕ) : ℕ := 160 + tL + nL

variable {tL nL : ℕ}

/-- Named tape `i`. -/
def nm (tL nL : ℕ) (i : Fin 13) : Fin (DB tL nL) := ⟨i.val, by have := i.isLt; unfold DB; omega⟩

/-- Tape `j` of the twist block. -/
def twT (tL nL : ℕ) (j : Fin 29) : Fin (DB tL nL) := ⟨20 + j.val, by have := j.isLt; unfold DB; omega⟩

/-- Named tapes `v`, the twist block `tw`, every other tape empty. -/
def dstate (tL nL : ℕ) (v : Fin 13 → WTape) (tw : Fin 29 → WTape) : Fin (DB tL nL) → WTape := fun x =>
  if h : x.val < 13 then v ⟨x.val, h⟩
  else if h' : 20 ≤ x.val ∧ x.val < 49 then tw ⟨x.val - 20, by omega⟩ else emp

theorem dstate_nm (v : Fin 13 → WTape) (tw : Fin 29 → WTape) (i : Fin 13) :
    dstate tL nL v tw (nm tL nL i) = v i := by
  simp [dstate, nm]

theorem dstate_twT (v : Fin 13 → WTape) (tw : Fin 29 → WTape) (j : Fin 29) :
    dstate tL nL v tw (twT tL nL j) = tw j := by
  have := j.isLt
  simp [dstate, twT, show ¬ 20 + j.val < 13 by omega, show 20 + j.val < 49 by omega]

theorem dstate_other (v : Fin 13 → WTape) (tw : Fin 29 → WTape) {x : Fin (DB tL nL)}
    (h1 : 13 ≤ x.val) (h2 : x.val < 20 ∨ 49 ≤ x.val) : dstate tL nL v tw x = emp := by
  simp only [dstate, show ¬ x.val < 13 by omega, ↓reduceDIte]
  rw [dite_eq_right (by omega)]

theorem eq_nm {x : Fin (DB tL nL)} (h : x.val < 13) : x = nm tL nL ⟨x.val, h⟩ := Fin.ext rfl

theorem eq_twT {x : Fin (DB tL nL)} (h1 : 20 ≤ x.val) (h2 : x.val < 49) :
    x = twT tL nL ⟨x.val - 20, by omega⟩ := Fin.ext (by simp [twT]; omega)

theorem nm_inj {i i' : Fin 13} (h : nm tL nL i = nm tL nL i') : i = i' :=
  Fin.ext (by have := congrArg Fin.val h; simpa [nm] using this)

theorem twT_inj {j j' : Fin 29} (h : twT tL nL j = twT tL nL j') : j = j' :=
  Fin.ext (by have := congrArg Fin.val h; simp [twT] at this; omega)

theorem nm_ne_twT (i : Fin 13) (j : Fin 29) : nm tL nL i ≠ twT tL nL j := fun h => by
  have := congrArg Fin.val h; simp [nm, twT] at this; have := i.isLt; omega

theorem update_nm (v : Fin 13 → WTape) (tw : Fin 29 → WTape) (i : Fin 13) (u : WTape) :
    Function.update (dstate tL nL v tw) (nm tL nL i) u = dstate tL nL (Function.update v i u) tw := by
  funext x
  by_cases h1 : x.val < 13
  · rw [eq_nm h1, dstate_nm]
    by_cases hi : (⟨x.val, h1⟩ : Fin 13) = i
    · rw [hi]; simp
    · rw [Function.update_of_ne (fun e => hi (nm_inj e)), Function.update_of_ne hi, dstate_nm]
  · have hx : x ≠ nm tL nL i := fun e => h1 (by rw [e]; simp [nm])
    rw [Function.update_of_ne hx]
    by_cases h2 : 20 ≤ x.val ∧ x.val < 49
    · rw [eq_twT h2.1 h2.2, dstate_twT, dstate_twT]
    · rw [dstate_other _ _ (by omega) (by omega), dstate_other _ _ (by omega) (by omega)]

theorem update_tw (v : Fin 13 → WTape) (tw : Fin 29 → WTape) (j : Fin 29) (u : WTape) :
    Function.update (dstate tL nL v tw) (twT tL nL j) u = dstate tL nL v (Function.update tw j u) := by
  funext x
  by_cases h1 : x.val < 13
  · rw [eq_nm h1, dstate_nm, Function.update_of_ne (nm_ne_twT _ _), dstate_nm]
  · by_cases h2 : 20 ≤ x.val ∧ x.val < 49
    · rw [eq_twT h2.1 h2.2, dstate_twT]
      by_cases hj : (⟨x.val - 20, by omega⟩ : Fin 29) = j
      · rw [hj]; simp
      · rw [Function.update_of_ne (fun e => hj (twT_inj e)), Function.update_of_ne hj, dstate_twT]
    · have hx : x ≠ twT tL nL j := fun e => h2 (by rw [e]; simp [twT]; omega)
      rw [Function.update_of_ne hx, dstate_other _ _ (by omega) (by omega), dstate_other _ _ (by omega) (by omega)]

end IntegerMultBounds.Schoenhage
