module

public import IntegerMultBounds.Resampling.AxisStep
public import IntegerMultBounds.Schoenhage.SwapPrim

/-! The tensor driver: one loop over a script tape. A script entry is either
an axis record (tag `[true]`, then the words loaded into the axis program's
registers) or a swap record (tag `[false]`, then the headers `P, G, B, h, d`
of one address-field interchange). The axis program runs on its own block of
the bank; the interchange runs on the swap block with the axis array as its
payload. The driver is generic in the axis program, given its contract
(`AxisContract`); `runs_drive` follows a whole script. -/

@[expose] public section

set_option maxRecDepth 10000

namespace IntegerMultBounds.Resampling.AxisDriver
noncomputable section

open Machine Schoenhage
open Networks.Shared50ModularControl (prime)

/-- The swap block. -/
abbrev SN := BinaryInterchangeRun.bankCount 6 + 1

theorem six_le : 6 ≤ SN := by unfold SN BinaryInterchangeRun.bankCount; omega

variable {E : ℕ}

/-- The driver bank: the swap block, the axis block, the script and a junk tape. -/
abbrev NB (E : ℕ) := SN + (E + 2)

def ax (i : Fin E) : Fin (NB E) := Fin.natAdd SN (Fin.castAdd 2 i)
def sw (i : Fin SN) : Fin (NB E) := Fin.castAdd (E + 2) i
def scr : Fin (NB E) := Fin.natAdd SN (Fin.natAdd E 0)
def jnk : Fin (NB E) := Fin.natAdd SN (Fin.natAdd E 1)

theorem ax_val (i : Fin E) : (ax i).val = SN + i.val := rfl
theorem sw_val (i : Fin SN) : (sw (E := E) i).val = i.val := rfl
theorem scr_val : (scr (E := E)).val = SN + E := rfl
theorem jnk_val : (jnk (E := E)).val = SN + E + 1 := by simp [jnk]; omega

theorem ax_inj : Function.Injective (ax (E := E)) := fun i j h => Fin.ext (by
  have := congrArg Fin.val h; rw [ax_val, ax_val] at this; omega)
theorem ax_ne_scr (i : Fin E) : ax i ≠ scr := fun h => by
  have := congrArg Fin.val h; rw [ax_val, scr_val] at this; have := i.isLt; omega
theorem ax_ne_jnk (i : Fin E) : ax i ≠ jnk := fun h => by
  have := congrArg Fin.val h; rw [ax_val, jnk_val] at this; have := i.isLt; omega
theorem sw_ne_ax (i : Fin SN) (j : Fin E) : sw i ≠ ax j := fun h => by
  have := congrArg Fin.val h; rw [sw_val, ax_val] at this; have := i.isLt; omega
theorem sw_ne_scr (i : Fin SN) : sw i ≠ (scr : Fin (NB E)) := fun h => by
  have := congrArg Fin.val h; rw [sw_val, scr_val] at this; have := i.isLt; omega
theorem sw_ne_jnk (i : Fin SN) : sw i ≠ (jnk : Fin (NB E)) := fun h => by
  have := congrArg Fin.val h; rw [sw_val, jnk_val] at this; have := i.isLt; omega
theorem scr_ne_jnk : (scr : Fin (NB E)) ≠ jnk := fun h => by
  have := congrArg Fin.val h; rw [scr_val, jnk_val] at this; omega
theorem sw_inj : Function.Injective (sw (E := E)) := fun i j h => Fin.ext (by
  have := congrArg Fin.val h; rwa [sw_val, sw_val] at this)

/-- The swap's tapes: its own block, except the payload, which is the axis array `X`. -/
def swSlot (X : Fin E) (i : Fin SN) : Fin (NB E) := if i.val = 5 then ax X else sw i

theorem swSlot_inj (X : Fin E) : Function.Injective (swSlot X) := by
  intro i j h
  unfold swSlot at h
  split_ifs at h with hi hj hj
  · exact Fin.ext (by omega)
  · exact absurd h.symm (sw_ne_ax _ _)
  · exact absurd h (sw_ne_ax _ _)
  · exact sw_inj h

/-- The swap's header tape `j`. -/
def hd (j : Fin 5) : Fin (NB E) := sw (BinaryInterchangeRun.slot (Fin.castSucc j))

theorem hd_val (j : Fin 5) : (hd (E := E) j).val = j.val := rfl

/-! ### The bank between records -/

/-- Between records: the swap block and the junk tape empty, the axis block at rest with
the array on `X`, the script on `scr`. -/
def bank (ρ : Fin E → WTape) (X : Fin E) (A : List Bool) (S : WTape) : Fin (NB E) → WTape :=
  Fin.addCases (fun _ => emp) (Fin.addCases (Function.update ρ X (reg A)) ![S, emp])

theorem bank_ax (ρ : Fin E → WTape) (X : Fin E) (A : List Bool) (S : WTape) (i : Fin E) :
    bank ρ X A S (ax i) = Function.update ρ X (reg A) i := by
  simp [bank, ax]

theorem bank_sw (ρ : Fin E → WTape) (X : Fin E) (A : List Bool) (S : WTape) (i : Fin SN) :
    bank ρ X A S (sw i) = emp := by
  simp [bank, sw]

theorem bank_scr (ρ : Fin E → WTape) (X : Fin E) (A : List Bool) (S : WTape) :
    bank ρ X A S scr = S := by
  simp [bank, scr]

theorem bank_jnk (ρ : Fin E → WTape) (X : Fin E) (A : List Bool) (S : WTape) :
    bank ρ X A S jnk = emp := by
  simp [bank, jnk]

/-- Every tape of the driver bank is a swap tape, an axis tape, the script or the junk tape. -/
theorem cases (x : Fin (NB E)) : (∃ i, x = sw i) ∨ (∃ i, x = ax i) ∨ x = scr ∨ x = jnk := by
  rcases x with ⟨v, hv⟩
  have hv' : v < SN + (E + 2) := hv
  by_cases h1 : v < SN
  · exact Or.inl ⟨⟨v, h1⟩, rfl⟩
  by_cases h2 : v < SN + E
  · exact Or.inr (Or.inl ⟨⟨v - SN, by omega⟩, Fin.ext (by simp [ax_val]; omega)⟩)
  by_cases h3 : v = SN + E
  · exact Or.inr (Or.inr (Or.inl (Fin.ext (by simp [scr_val, h3]))))
  · exact Or.inr (Or.inr (Or.inr (Fin.ext (by simp [jnk_val]; omega))))

/-! ### Loading registers from the script and clearing tapes -/

/-- Fill registers `rs` with the next words of the script. -/
def loadAll : List (Fin (NB E)) → Cmd prime (NB E)
  | [] => rewind jnk
  | r :: rs => if h : scr ≠ r then .seq (regIn scr r h) (loadAll rs) else rewind jnk

/-- The registers `rs` holding the words `ws`. -/
def setRegs {n : ℕ} (σ : Fin n → WTape) : List (Fin n) → List (List Bool) → Fin n → WTape
  | r :: rs, w :: ws => Function.update (setRegs σ rs ws) r (reg w)
  | _, _ => σ

theorem setRegs_other {n : ℕ} (σ : Fin n → WTape) (x : Fin n) :
    ∀ (rs : List (Fin n)) (ws : List (List Bool)), x ∉ rs → setRegs σ rs ws x = σ x
  | [], _, _ => by simp [setRegs]
  | _ :: _, [], _ => by simp [setRegs]
  | r :: rs, w :: ws, hx => by
    simp only [List.mem_cons, not_or] at hx
    simp only [setRegs]; rw [Function.update_of_ne hx.1, setRegs_other σ x rs ws hx.2]

theorem setRegs_base {n : ℕ} (σ σ' : Fin n → WTape) (x : Fin n) :
    ∀ (rs : List (Fin n)) (ws : List (List Bool)), ws.length = rs.length → x ∈ rs →
      setRegs σ rs ws x = setRegs σ' rs ws x
  | [], _, _, hx => by simp at hx
  | _ :: _, [], hl, _ => by simp at hl
  | r :: rs, w :: ws, hl, hx => by
    simp only [setRegs]
    by_cases h : x = r
    · subst h; simp
    · rw [Function.update_of_ne h, Function.update_of_ne h,
        setRegs_base σ σ' x rs ws (by simpa using hl) (by simpa [h] using hx)]

/-- The cost of loading `ws`. -/
def loadCost : List (List Bool) → ℕ
  | [] => 2
  | w :: ws => 2 * w.length + 12 + 1 + loadCost ws

theorem runs_loadAll : ∀ (rs : List (Fin (NB E))) (ws : List (List Bool)) (σ : Fin (NB E) → WTape)
    (L R : List (List Bool)), ws.length = rs.length → rs.Nodup → scr ∉ rs → jnk ∉ rs →
    (∀ r ∈ rs, σ r = emp) → σ scr = ⟨L, ws ++ R⟩ → σ jnk = emp →
    Runs (loadAll rs) σ (· = Function.update (setRegs σ rs ws) scr ⟨ws.reverse ++ L, R⟩) (loadCost ws)
  | [], [], σ, L, R, _, _, _, _, _, hs, hj => by
    refine (runs_rewind jnk σ).mono (fun σ' e => ?_) (by simp [hj, emp, loadCost])
    rw [e, hj]; funext x
    by_cases h1 : x = scr
    · subst h1; simp [setRegs, Function.update_of_ne scr_ne_jnk, hs]
    · by_cases h2 : x = jnk
      · subst h2; simp [setRegs, h1, hj, emp]
      · simp [setRegs, h1, h2]
  | [], _ :: _, _, _, _, hl, _, _, _, _, _, _ => by simp at hl
  | _ :: _, [], _, _, _, hl, _, _, _, _, _, _ => by simp at hl
  | r :: rs, w :: ws, σ, L, R, hl, hnd, hscr, hjnk, he, hs, hj => by
    simp only [List.mem_cons, not_or] at hscr hjnk
    simp only [List.nodup_cons] at hnd
    have hne : scr ≠ r := fun e => hscr.1 e
    have s1 := runs_regIn (a := prime) hne σ (L := L) (R := ws ++ R) (w := w) (by simpa using hs) (he r (by simp))
    set σ1 := Function.update (Function.update σ scr ⟨w :: L, ws ++ R⟩) r (reg w)
    have ih := runs_loadAll rs ws σ1 (w :: L) R (by simpa using hl) hnd.2 hscr.2 hjnk.2
      (fun r' hr' => by
        have hne' : r' ≠ r := fun e => hnd.1 (e ▸ hr')
        have hs' : r' ≠ scr := fun e => hscr.2 (e ▸ hr')
        simp only [σ1]; rw [Function.update_of_ne hne', Function.update_of_ne hs']; exact he r' (by simp [hr']))
      (by simp only [σ1]; rw [Function.update_of_ne hne, Function.update_self])
      (by simp only [σ1]; rw [Function.update_of_ne hjnk.1, Function.update_of_ne scr_ne_jnk.symm, hj])
    simp only [loadAll, hne, ne_eq, not_false_eq_true, dite_true]
    refine (Runs.then s1 ih).mono (fun σ' e => ?_) (by simp [loadCost])
    rw [e]; funext x
    by_cases h1 : x = scr
    · subst h1; simp
    · rw [Function.update_of_ne h1, Function.update_of_ne h1]
      by_cases h2 : x ∈ rs
      · simp only [setRegs]
        have hxr : x ≠ r := fun e => hnd.1 (e ▸ h2)
        rw [Function.update_of_ne hxr]
        exact setRegs_base _ _ x rs ws (by simpa using hl) h2
      · rw [setRegs_other _ _ _ _ h2]
        simp only [σ1, setRegs]
        by_cases h3 : x = r
        · subst h3; simp
        · rw [Function.update_of_ne h3, Function.update_of_ne h3, Function.update_of_ne h1, setRegs_other _ _ _ _ h2]

end
end IntegerMultBounds.Resampling.AxisDriver
