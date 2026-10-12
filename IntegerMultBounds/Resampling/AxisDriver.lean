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

/-- Empty the tapes `js`. -/
def clearAll : List (Fin (NB E)) → Cmd prime (NB E)
  | [] => rewind jnk
  | j :: js => .seq (clear j) (clearAll js)

/-- The tapes `js` emptied. -/
def setEmp {n : ℕ} (σ : Fin n → WTape) (js : List (Fin n)) : Fin n → WTape :=
  fun x => if x ∈ js then emp else σ x

/-- The cost of emptying `js`. -/
def clearCost {n : ℕ} (σ : Fin n → WTape) : List (Fin n) → ℕ
  | [] => 2
  | j :: js => 2 * clen (σ j).words + 2 + 1 + clearCost σ js

theorem runs_clearAll : ∀ (js : List (Fin (NB E))) (σ : Fin (NB E) → WTape), js.Nodup → σ jnk = emp →
    Runs (clearAll js) σ (· = setEmp σ js) (clearCost σ js)
  | [], σ, _, hj => by
    refine (runs_rewind jnk σ).mono (fun σ' e => ?_) (by simp [hj, emp, clearCost])
    rw [e, hj]; funext x
    by_cases h : x = jnk
    · subst h; simp [setEmp, hj, emp]
    · simp [setEmp, h]
  | j :: js, σ, hnd, hj => by
    simp only [List.nodup_cons] at hnd
    have s1 := runs_clear (a := prime) j σ
    set σ1 := Function.update σ j ⟨[], []⟩
    have hj1 : σ1 jnk = emp := by
      simp only [σ1]; by_cases h : jnk = j
      · rw [h, Function.update_self]; rfl
      · rw [Function.update_of_ne h, hj]
    have ih := runs_clearAll js σ1 hnd.2 hj1
    have hc : clearCost σ1 js = clearCost σ js := by
      clear ih s1
      induction js with
      | nil => rfl
      | cons k ks ihk =>
        simp only [List.mem_cons, not_or, List.nodup_cons] at hnd
        have hk : k ≠ j := fun e => hnd.1.1 e.symm
        simp only [clearCost, σ1, Function.update_of_ne hk]
        rw [ihk ⟨hnd.1.2, hnd.2.2⟩]
    refine (Runs.then s1 ih).mono (fun σ' e => ?_) (by rw [hc]; simp [clearCost])
    rw [e]; funext x
    simp only [setEmp, σ1, List.mem_cons]
    by_cases h1 : x = j
    · subst h1; simp [emp]
    · rw [Function.update_of_ne h1]; simp [h1]

/-! ### Swap records -/

theorem upd_update {n m : ℕ} (σ : Fin n → WTape) {f : Fin m → Fin n} (hf : Function.Injective f) (i : Fin m)
    (v : WTape) : upd σ f (Function.update (σ ∘ f) i v) = Function.update σ (f i) v := by
  funext x
  by_cases hx : ∃ j, f j = x
  · obtain ⟨j, rfl⟩ := hx
    rw [upd_slot σ hf]
    by_cases hj : j = i
    · subst hj; simp
    · rw [Function.update_of_ne hj, Function.update_of_ne (fun e => hj (hf e))]; rfl
  · push Not at hx
    rw [upd_other σ f _ x hx, Function.update_of_ne (fun e => hx i e.symm)]

/-- The swap block as the interchange reads it: five headers, the array, empty private tapes. -/
def swIn (hs : List (List Bool)) (A : List Bool) : Fin SN → WTape :=
  fun i => if i.val < 5 then reg (hs.getD i.val []) else if i.val = 5 then reg A else emp

/-- The array after one swap record. -/
def swapF (hs : List (List Bool)) (A : List Bool) : List Bool := SwapPrim.swapped (swIn hs A)

theorem hd_inj {i j : Fin 5} : hd (E := E) i = hd j ↔ i = j :=
  ⟨fun h => Fin.ext (by have := congrArg Fin.val h; rwa [hd_val, hd_val] at this), fun h => h ▸ rfl⟩

/-- The header registers. -/
def hds : List (Fin (NB E)) := [hd 0, hd 1, hd 2, hd 3, hd 4]

theorem hds_nodup : (hds (E := E)).Nodup := by
  simp [hds, hd_inj]

theorem hd_ne_ax (j : Fin 5) (i : Fin E) : hd j ≠ ax i := sw_ne_ax _ _
theorem hd_ne_scr (j : Fin 5) : hd j ≠ (scr : Fin (NB E)) := sw_ne_scr _
theorem hd_ne_jnk (j : Fin 5) : hd j ≠ (jnk : Fin (NB E)) := sw_ne_jnk _

theorem mem_hds {x : Fin (NB E)} (hx : x ∈ hds) : ∃ j : Fin 5, x = hd j := by
  simp only [hds, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with h | h | h | h | h <;> exact ⟨_, h⟩

/-- Skip the tag, load the headers, interchange, clear the headers. -/
def swapBranch (X : Fin E) : Cmd prime (NB E) :=
  .seq (skp scr jnk scr_ne_jnk) <| .seq (loadAll hds) <|
  .seq (.prim SwapPrim.prim (swSlot X) (swSlot_inj X)) (clearAll hds)

/-- The cost of a swap record. -/
noncomputable def swapCost (hs : List (List Bool)) (A : List Bool) : ℕ :=
  6 + 1 + (loadCost hs + 1 + (SwapPrim.cost (swIn hs A) + 1 + (10 * clen hs + 30)))

theorem bank_cases {ρ : Fin E → WTape} {X : Fin E} {A : List Bool} {S : WTape} (G : Fin (NB E) → WTape)
    (h1 : ∀ i, G (sw i) = emp) (h2 : ∀ i, G (ax i) = Function.update ρ X (reg A) i) (h3 : G scr = S)
    (h4 : G jnk = emp) : G = bank ρ X A S := by
  funext x
  rcases cases x with ⟨i, rfl⟩ | ⟨i, rfl⟩ | rfl | rfl
  · rw [h1, bank_sw]
  · rw [h2, bank_ax]
  · rw [h3, bank_scr]
  · rw [h4, bank_jnk]

theorem runs_swapBranch (ρ : Fin E → WTape) (X : Fin E) (A : List Bool) (L R hs : List (List Bool))
    (hl : hs.length = 5) (hpre : SwapPrim.Pre (swIn hs A)) :
    Runs (swapBranch X) (bank ρ X A ⟨L, ([false] :: hs) ++ R⟩)
      (· = bank ρ X (swapF hs A) ⟨hs.reverse ++ [false] :: L, R⟩) (swapCost hs A) := by
  obtain ⟨h0, h1, h2, h3, h4, rfl⟩ : ∃ h0 h1 h2 h3 h4, hs = [h0, h1, h2, h3, h4] := by
    match hs, hl with
    | [h0, h1, h2, h3, h4], _ => exact ⟨h0, h1, h2, h3, h4, rfl⟩
  set σ := bank ρ X A ⟨L, ([false] :: [h0, h1, h2, h3, h4]) ++ R⟩
  -- 1. skip the tag
  have s1 := runs_skp (a := prime) scr_ne_jnk σ (by simp [σ, bank_scr]) (by simp [σ, bank_jnk])
  set σ1 := Function.update σ scr (σ scr).next
  have hσ1s : σ1 scr = ⟨[false] :: L, [h0, h1, h2, h3, h4] ++ R⟩ := by simp [σ1, σ, bank_scr]
  -- 2. load the headers
  have s2 := runs_loadAll hds [h0, h1, h2, h3, h4] σ1 ([false] :: L) R rfl hds_nodup
    (fun h => by obtain ⟨j, e⟩ := mem_hds h; exact hd_ne_scr j e.symm)
    (fun h => by obtain ⟨j, e⟩ := mem_hds h; exact hd_ne_jnk j e.symm)
    (fun r hr => by
      obtain ⟨j, rfl⟩ := mem_hds hr
      simp only [σ1, σ]; rw [Function.update_of_ne (hd_ne_scr j)]; exact bank_sw _ _ _ _ _)
    hσ1s (by simp only [σ1, σ]; rw [Function.update_of_ne scr_ne_jnk.symm]; exact bank_jnk _ _ _ _)
  set σ2 := Function.update (setRegs σ1 hds [h0, h1, h2, h3, h4]) scr
    ⟨[h0, h1, h2, h3, h4].reverse ++ [false] :: L, R⟩
  -- 3. the interchange
  have hσ2 : σ2 ∘ swSlot X = swIn [h0, h1, h2, h3, h4] A := by
    funext i
    simp only [Function.comp_apply, swIn]
    by_cases hi5 : i.val < 5
    · have hsw : swSlot X i = hd ⟨i.val, hi5⟩ := by
        simp only [swSlot, show i.val ≠ 5 by omega, ite_false]; exact Fin.ext rfl
      rw [hsw, ite_eq_left_of_eq_true _ _ (eq_true hi5)]
      simp only [σ2]; rw [Function.update_of_ne (hd_ne_scr _)]
      obtain ⟨v, hv⟩ := i
      simp only at hi5 ⊢
      interval_cases v <;> simp [setRegs, hds, hd_inj]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false hi5)]
      by_cases h5 : i.val = 5
      · have hsw : swSlot X i = ax X := by simp [swSlot, h5]
        rw [hsw, ite_eq_left_of_eq_true _ _ (eq_true h5)]
        simp only [σ2]; rw [Function.update_of_ne (ax_ne_scr X), setRegs_other _ _ _ _ (fun h => by
          obtain ⟨j, e⟩ := mem_hds h; exact hd_ne_ax j X e.symm)]
        simp only [σ1, σ]; rw [Function.update_of_ne (ax_ne_scr X), bank_ax]; simp
      · have hsw : swSlot X i = sw i := by simp [swSlot, h5]
        rw [hsw, ite_eq_right_of_eq_false _ _ (eq_false h5)]
        simp only [σ2]; rw [Function.update_of_ne (sw_ne_scr i), setRegs_other _ _ _ _ (fun h => by
          obtain ⟨j, e⟩ := mem_hds h; have := congrArg Fin.val e; rw [sw_val, hd_val] at this; omega)]
        simp only [σ1, σ]; rw [Function.update_of_ne (sw_ne_scr i), bank_sw]
  have hs5 : swSlot X (BinaryInterchangeRun.slot 5) = ax X := by
    simp [swSlot, SwapPrim.slot_val]
  set σ3 := Function.update σ2 (ax X) (reg (swapF [h0, h1, h2, h3, h4] A))
  have s3 : Runs (.prim SwapPrim.prim (swSlot X) (swSlot_inj X)) σ2 (· = σ3)
      (SwapPrim.cost (swIn [h0, h1, h2, h3, h4] A)) := by
    refine ⟨_, _, Exec.prim (P := SwapPrim.prim) (by show SwapPrim.Pre (σ2 ∘ swSlot X); rw [hσ2]; exact hpre), ?_,
      by show SwapPrim.cost (σ2 ∘ swSlot X) ≤ _; rw [hσ2]⟩
    show upd σ2 (swSlot X) (SwapPrim.sem (σ2 ∘ swSlot X)) = σ3
    rw [SwapPrim.sem, upd_update σ2 (swSlot_inj X), hs5, hσ2]; rfl
  -- 4. clear the headers
  have hσ3j : σ3 jnk = emp := by
    simp only [σ3, σ2]
    rw [Function.update_of_ne (ax_ne_jnk X).symm, Function.update_of_ne scr_ne_jnk.symm,
      setRegs_other _ _ _ _ (fun h => by obtain ⟨j, e⟩ := mem_hds h; exact hd_ne_jnk j e.symm)]
    simp only [σ1, σ]; rw [Function.update_of_ne scr_ne_jnk.symm, bank_jnk]
  have s4 := runs_clearAll hds σ3 hds_nodup hσ3j
  refine (Runs.then s1 (Runs.then s2 (Runs.then s3 s4))).mono (fun σ' e => ?_) ?_
  · rw [e]
    apply bank_cases
    · intro i
      simp only [setEmp]
      split_ifs with h
      · rfl
      · simp only [σ3, σ2]
        rw [Function.update_of_ne (sw_ne_ax i X), Function.update_of_ne (sw_ne_scr i), setRegs_other _ _ _ _ h]
        simp only [σ1, σ]; rw [Function.update_of_ne (sw_ne_scr i), bank_sw]
    · intro i
      have hni : ax i ∉ (hds : List (Fin (NB E))) := fun h => by
        obtain ⟨j, e⟩ := mem_hds h; exact hd_ne_ax j i e.symm
      simp only [setEmp, hni, ite_false, σ3, σ2]
      by_cases hiX : i = X
      · subst hiX; simp
      · rw [Function.update_of_ne (fun e => hiX (ax_inj e)), Function.update_of_ne (ax_ne_scr i),
          setRegs_other _ _ _ _ hni]
        simp only [σ1, σ]; rw [Function.update_of_ne (ax_ne_scr i), bank_ax, Function.update_of_ne hiX,
          Function.update_of_ne hiX]
    · have hn : scr ∉ (hds : List (Fin (NB E))) := fun h => by
        obtain ⟨j, e⟩ := mem_hds h; exact hd_ne_scr j e.symm
      simp only [setEmp, hn, ite_false, σ3, σ2]
      rw [Function.update_of_ne (ax_ne_scr X).symm, Function.update_self]
    · have hn : jnk ∉ (hds : List (Fin (NB E))) := fun h => by
        obtain ⟨j, e⟩ := mem_hds h; exact hd_ne_jnk j e.symm
      simp only [setEmp, hn, ite_false]; exact hσ3j
  · have hc : ∀ j : Fin 5, σ3 (hd j) = reg ([h0, h1, h2, h3, h4].getD j.val []) := by
      intro j
      simp only [σ3, σ2]
      rw [Function.update_of_ne (hd_ne_ax j X), Function.update_of_ne (hd_ne_scr j)]
      fin_cases j <;> simp [setRegs, hds, hd_inj]
    simp only [clearCost, hds, hc, swapCost, σ, bank_scr]
    simp [reg, WTape.words, clen]
    omega

/-! ### Axis records -/

/-- A per-axis program on the axis block with its contract: from the rest bank `ρ` with the
array `A` on `X` and the record's words in `regs`, it leaves `f ws A` on `X`, touches only `X`
and the `junk` tapes (each left with at most `J ws A` cells), within `cost ws A` steps. -/
structure AxisSpec (E : ℕ) where
  cmd : Cmd prime E
  X : Fin E
  regs : List (Fin E)
  junk : List (Fin E)
  ρ : Fin E → WTape
  Good : List (List Bool) → List Bool → Prop
  f : List (List Bool) → List Bool → List Bool
  cost : List (List Bool) → List Bool → ℕ
  J : List (List Bool) → List Bool → ℕ
  regs_nodup : regs.Nodup
  junk_nodup : junk.Nodup
  regs_junk : ∀ r ∈ regs, r ∈ junk
  X_junk : X ∉ junk
  ρ_junk : ∀ j ∈ junk, ρ j = emp
  run : ∀ ws A, Good ws A → ws.length = regs.length →
    Runs cmd (setRegs (Function.update ρ X (reg A)) regs ws)
      (fun τ => τ X = reg (f ws A) ∧ (∀ x, x ∉ junk → x ≠ X → τ x = ρ x) ∧
        ∀ j ∈ junk, clen (τ j).words ≤ J ws A) (cost ws A)

theorem setRegs_map {n m : ℕ} (σ : Fin n → WTape) {f : Fin m → Fin n} (hf : Function.Injective f) (y : Fin m) :
    ∀ (rs : List (Fin m)) (ws : List (List Bool)), setRegs σ (rs.map f) ws (f y) = setRegs (σ ∘ f) rs ws y
  | [], _ => by simp [setRegs]
  | _ :: _, [] => by simp [setRegs]
  | r :: rs, w :: ws => by
    simp only [List.map_cons, setRegs]
    by_cases h : y = r
    · subst h; simp
    · rw [Function.update_of_ne (fun e => h (hf e)), Function.update_of_ne h, setRegs_map σ hf y rs ws]

theorem clearCost_le {n : ℕ} (σ : Fin n → WTape) (J : ℕ) :
    ∀ js : List (Fin n), (∀ j ∈ js, clen (σ j).words ≤ J) → clearCost σ js ≤ js.length * (2 * J + 3) + 2
  | [], _ => by simp [clearCost]
  | j :: js, h => by
    have h1 := h j (by simp)
    have h2 := clearCost_le σ J js (fun k hk => h k (by simp [hk]))
    simp only [clearCost, List.length_cons]; nlinarith

/-- Skip the tag, load the registers, run the axis program, clear its junk. -/
def axisBranch (S : AxisSpec E) : Cmd prime (NB E) :=
  .seq (skp scr jnk scr_ne_jnk) <| .seq (loadAll (S.regs.map ax)) <|
  .seq (S.cmd.map ax ax_inj) (clearAll (S.junk.map ax))

/-- The cost of an axis record. -/
def axisCost (S : AxisSpec E) (ws : List (List Bool)) (A : List Bool) : ℕ :=
  6 + 1 + (loadCost ws + 1 + (S.cost ws A + 1 + (S.junk.length * (2 * S.J ws A + 3) + 2)))

theorem runs_axisBranch (S : AxisSpec E) (A : List Bool) (L R ws : List (List Bool))
    (hl : ws.length = S.regs.length) (hg : S.Good ws A) :
    Runs (axisBranch S) (bank S.ρ S.X A ⟨L, ([true] :: ws) ++ R⟩)
      (· = bank S.ρ S.X (S.f ws A) ⟨ws.reverse ++ [true] :: L, R⟩) (axisCost S ws A) := by
  set σ := bank S.ρ S.X A ⟨L, ([true] :: ws) ++ R⟩
  have s1 := runs_skp (a := prime) scr_ne_jnk σ (by simp [σ, bank_scr]) (by simp [σ, bank_jnk])
  set σ1 := Function.update σ scr (σ scr).next
  have hσ1s : σ1 scr = ⟨[true] :: L, ws ++ R⟩ := by simp [σ1, σ, bank_scr]
  have hσ1a : ∀ i, σ1 (ax i) = Function.update S.ρ S.X (reg A) i := fun i => by
    simp only [σ1, σ]; rw [Function.update_of_ne (ax_ne_scr i), bank_ax]
  have hregs : ∀ r ∈ S.regs.map ax, r ≠ scr ∧ r ≠ jnk := fun r hr => by
    simp only [List.mem_map] at hr; obtain ⟨i, -, rfl⟩ := hr; exact ⟨ax_ne_scr i, ax_ne_jnk i⟩
  have s2 := runs_loadAll (S.regs.map ax) ws σ1 ([true] :: L) R (by simpa using hl)
    (S.regs_nodup.map ax_inj) (fun h => (hregs _ h).1 rfl) (fun h => (hregs _ h).2 rfl)
    (fun r hr => by
      simp only [List.mem_map] at hr; obtain ⟨i, hi, rfl⟩ := hr
      rw [hσ1a, Function.update_of_ne (fun e => S.X_junk (by rw [← e]; exact S.regs_junk i hi))]
      exact S.ρ_junk i (S.regs_junk i hi))
    hσ1s (by simp only [σ1, σ]; rw [Function.update_of_ne scr_ne_jnk.symm, bank_jnk])
  set σ2 := Function.update (setRegs σ1 (S.regs.map ax) ws) scr ⟨ws.reverse ++ [true] :: L, R⟩
  have hσ2a : σ2 ∘ ax = setRegs (Function.update S.ρ S.X (reg A)) S.regs ws := by
    funext y
    simp only [Function.comp_apply, σ2]
    rw [Function.update_of_ne (ax_ne_scr y), setRegs_map σ1 ax_inj]
    congr 1; funext z; exact hσ1a z
  have s3 := (S.run ws A hg hl).map ax ax_inj σ2 hσ2a
  have hjm : ∀ j ∈ S.junk.map ax, ∃ i ∈ S.junk, j = ax i := fun j hj => by
    simp only [List.mem_map] at hj; obtain ⟨i, hi, rfl⟩ := hj; exact ⟨i, hi, rfl⟩
  have s34 : Runs (.seq (S.cmd.map ax ax_inj) (clearAll (S.junk.map ax))) σ2
      (· = bank S.ρ S.X (S.f ws A) ⟨ws.reverse ++ [true] :: L, R⟩)
      (S.cost ws A + 1 + (S.junk.length * (2 * S.J ws A + 3) + 2)) := by
    refine Runs.seq (s3.mono (fun τ ⟨⟨hX, hρ, hJ⟩, ho⟩ => ?_) le_rfl)
    have hτj : τ jnk = emp := by
      rw [ho jnk (fun y e => ax_ne_jnk y e)]
      simp only [σ2]; rw [Function.update_of_ne scr_ne_jnk.symm, setRegs_other _ _ _ _ (fun h => (hregs _ h).2 rfl)]
      simp only [σ1, σ]; rw [Function.update_of_ne scr_ne_jnk.symm, bank_jnk]
    refine (runs_clearAll (S.junk.map ax) τ (S.junk_nodup.map ax_inj) hτj).mono (fun σ' e => ?_)
      (by
        have := clearCost_le τ (S.J ws A) (S.junk.map ax) (fun j hj => by
          obtain ⟨i, hi, rfl⟩ := hjm j hj; exact hJ i hi)
        simpa using this)
    rw [e]
    have hσ2o : ∀ x, (∀ y, ax y ≠ x) → x ≠ scr → τ x = σ x := fun x hx hs => by
      rw [ho x hx]; simp only [σ2]
      rw [Function.update_of_ne hs, setRegs_other _ _ _ _ (fun h => by
        obtain ⟨i, -, rfl⟩ := List.mem_map.mp h; exact hx i rfl)]
      simp only [σ1]; rw [Function.update_of_ne hs]
    apply bank_cases
    · intro i
      have hn : sw i ∉ S.junk.map ax := fun h => by obtain ⟨k, -, e⟩ := hjm _ h; exact sw_ne_ax i k e
      simp only [setEmp, hn, ite_false]
      rw [hσ2o _ (fun y e => sw_ne_ax i y e.symm) (sw_ne_scr i)]; exact bank_sw _ _ _ _ _
    · intro i
      by_cases hi : i ∈ S.junk
      · have hm : ax i ∈ S.junk.map ax := List.mem_map_of_mem hi
        simp only [setEmp, hm, ite_true]
        rw [Function.update_of_ne (fun e => S.X_junk (by rw [← e]; exact hi)), S.ρ_junk i hi]
      · have hn : ax i ∉ S.junk.map ax := fun h => by
          obtain ⟨k, hk, e⟩ := hjm _ h; exact hi (by rw [ax_inj e]; exact hk)
        simp only [setEmp, hn, ite_false]
        by_cases hiX : i = S.X
        · subst hiX; simp only [Function.update_self]; exact hX
        · rw [Function.update_of_ne hiX]; exact hρ i hi hiX
    · have hn : scr ∉ S.junk.map ax := fun h => by obtain ⟨k, -, e⟩ := hjm _ h; exact ax_ne_scr k e.symm
      simp only [setEmp, hn, ite_false]
      rw [ho scr (fun y e => ax_ne_scr y e)]
      simp only [σ2, Function.update_self]
    · have hn : jnk ∉ S.junk.map ax := fun h => by obtain ⟨k, -, e⟩ := hjm _ h; exact ax_ne_jnk k e.symm
      simp only [setEmp, hn, ite_false]; exact hτj
  refine (Runs.then s1 (Runs.then s2 s34)).mono (fun σ' e => e) ?_
  simp [axisCost, σ, bank_scr]

end
end IntegerMultBounds.Resampling.AxisDriver
