module

public import IntegerMultBounds.Schoenhage.ConvPrims

/-! The synthetic convolution as one word program over given forward and
opposite transform programs: transform both operands, multiply pointwise,
transform back, scale by `M` and write `Γ(w_M)`, then clear the scratch tapes
(`runs_convCore`). -/

@[expose] public section

set_option maxRecDepth 10000

namespace IntegerMultBounds.Schoenhage

open Machine Strm Tp Schedule Spec.SignedRingProduct

variable {t q₁ q₂ a : ℕ}

/-- The bank: nine data tapes, then private tapes for the primitives. -/
abbrev NB (t : ℕ) : ℕ := t + 100

/-- Data tapes `v` on tapes 0–8, every other tape empty. -/
def cb (t : ℕ) (v : Fin 9 → WTape) : Fin (NB t) → WTape :=
  fun x => if h : x.val < 9 then v ⟨x.val, h⟩ else emp

/-- Data tape `j`. -/
def dt (t : ℕ) (j : Fin 9) : Fin (NB t) := ⟨j.val, by have := j.isLt; unfold NB; omega⟩

/-- A transform's tapes: header on 0, operand on `i`, output on `o`, the rest private. -/
def fwdSlot (t : ℕ) (i o : Fin 9) : Fin t → Fin (NB t) := fun x =>
  if x.val = 0 then dt t 0 else if x.val = 1 then dt t i else if x.val = 3 then dt t o
  else ⟨9 + x.val, by have := x.isLt; unfold NB; omega⟩

theorem fwdSlot_inj {i o : Fin 9} (hi : i.val ≠ 0) (ho : o.val ≠ 0) (hio : i ≠ o) :
    Function.Injective (fwdSlot t i o) := by
  intro x y h
  have h' := congrArg Fin.val h
  unfold fwdSlot dt at h'
  apply Fin.ext
  have := Fin.val_ne_of_ne hio
  have := i.isLt; have := o.isLt
  split_ifs at h' <;> simp only [Fin.val_mk] at h' <;> omega

/-- The ring product bank's tapes: header, two operands and the output on given data tapes. -/
def uSlot (t : ℕ) (h f g o : Fin 9) : Fin 𝕌 → Fin (NB t) := fun x =>
  if x = zH then dt t h else if x = zF then dt t f else if x = zG then dt t g else if x = zO then dt t o
  else ⟨9 + x.val, by have := x.isLt; change x.val < 91 at this; unfold NB; omega⟩

theorem val_zH : (zH : Fin 𝕌).val = 87 := rfl
theorem val_zF : (zF : Fin 𝕌).val = 88 := rfl
theorem val_zG : (zG : Fin 𝕌).val = 89 := rfl
theorem val_zO : (zO : Fin 𝕌).val = 90 := rfl

theorem uSlot_inj {h f g o : Fin 9} (hd : [h, f, g, o].Nodup) : Function.Injective (uSlot t h f g o) := by
  intro x y e
  have e' := congrArg Fin.val e
  unfold uSlot dt at e'
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hd
  obtain ⟨⟨n1, n2, n3⟩, ⟨n4, n5⟩, n6, -⟩ := hd
  have := Fin.val_ne_of_ne n1; have := Fin.val_ne_of_ne n2; have := Fin.val_ne_of_ne n3
  have := Fin.val_ne_of_ne n4; have := Fin.val_ne_of_ne n5; have := Fin.val_ne_of_ne n6
  have := h.isLt; have := f.isLt; have := g.isLt; have := o.isLt
  have hx := x.isLt; have hy := y.isLt
  change x.val < 91 at hx; change y.val < 91 at hy
  apply Fin.ext
  split_ifs at e' <;> simp only [Fin.val_mk, Fin.ext_iff, val_zH, val_zF, val_zG, val_zO] at * <;> omega

/-- Replacing slotted tapes, described tape by tape. -/
theorem upd_eq_of {n m : ℕ} (σ : Fin n → WTape) {f : Fin m → Fin n} (hf : Function.Injective f)
    (τ : Fin m → WTape) (ρ : Fin n → WTape) (h1 : ∀ i, ρ (f i) = τ i)
    (h2 : ∀ x, (∀ i, f i ≠ x) → ρ x = σ x) : upd σ f τ = ρ := by
  funext x
  by_cases hx : ∃ i, f i = x
  · obtain ⟨i, rfl⟩ := hx
    rw [upd_slot σ hf, h1]
  · push Not at hx
    rw [upd_other σ f _ x hx, h2 x hx]

/-! ### Views through the slots -/

theorem cb_dt (v : Fin 9 → WTape) (j : Fin 9) : cb t v (dt t j) = v j := by
  simp [cb, dt]

theorem cb_high (v : Fin 9 → WTape) {x : Fin (NB t)} (hx : 9 ≤ x.val) : cb t v x = emp := by
  simp [cb, show ¬ x.val < 9 by omega]

theorem eq_dt {x : Fin (NB t)} (hx : x.val < 9) : x = dt t ⟨x.val, hx⟩ := Fin.ext rfl

theorem fwdSlot_0 (ht : 4 ≤ t) (i o : Fin 9) : fwdSlot t i o (tp ht 0 (by decide)) = dt t 0 := by
  simp [fwdSlot, tp]
theorem fwdSlot_1 (ht : 4 ≤ t) (i o : Fin 9) : fwdSlot t i o (tp ht 1 (by decide)) = dt t i := by
  simp [fwdSlot, tp]
theorem fwdSlot_3 (ht : 4 ≤ t) (i o : Fin 9) : fwdSlot t i o (tp ht 3 (by decide)) = dt t o := by
  simp [fwdSlot, tp]
theorem fwdSlot_high (i o : Fin 9) {x : Fin t} (a0 : x.val ≠ 0) (a1 : x.val ≠ 1) (a3 : x.val ≠ 3) :
    9 ≤ (fwdSlot t i o x).val := by
  simp [fwdSlot, a0, a1, a3]

/-- What a transform sees: header, operand and output from data tapes `0`, `i`, `o`. -/
def fView (t : ℕ) (v : Fin 9 → WTape) (i o : Fin 9) : Fin t → WTape := fun x =>
  if x.val = 0 then v 0 else if x.val = 1 then v i else if x.val = 3 then v o else emp

theorem cb_comp_fwdSlot (v : Fin 9 → WTape) (i o : Fin 9) : cb t v ∘ fwdSlot t i o = fView t v i o := by
  funext x
  simp only [Function.comp_apply, fView]
  by_cases a0 : x.val = 0
  · simp [fwdSlot, a0, cb_dt]
  · by_cases a1 : x.val = 1
    · simp [fwdSlot, a1, cb_dt]
    · by_cases a3 : x.val = 3
      · simp [fwdSlot, a3, cb_dt]
      · simp only [a0, a1, a3, ↓reduceIte]
        exact cb_high v (fwdSlot_high i o a0 a1 a3)

theorem upd_cb_fwdSlot {i o : Fin 9} (hi : i ≠ 0) (ho : o ≠ 0) (hio : i ≠ o) (v : Fin 9 → WTape)
    (τ : Fin t → WTape) (hτ : ∀ x : Fin t, x.val ≠ 0 → x.val ≠ 1 → x.val ≠ 3 → τ x = emp) (ht : 4 ≤ t) :
    upd (cb t v) (fwdSlot t i o) τ = cb t (fun j => if j = 0 then τ (tp ht 0 (by decide))
      else if j = i then τ (tp ht 1 (by decide)) else if j = o then τ (tp ht 3 (by decide)) else v j) := by
  have hinj := fwdSlot_inj (t := t) (fun e => hi (Fin.ext e)) (fun e => ho (Fin.ext e)) hio
  apply upd_eq_of _ hinj
  · intro x
    by_cases a0 : x.val = 0
    · have : x = tp ht 0 (by decide) := Fin.ext a0
      subst this; rw [fwdSlot_0, cb_dt]; simp
    · by_cases a1 : x.val = 1
      · have : x = tp ht 1 (by decide) := Fin.ext a1
        subst this; rw [fwdSlot_1, cb_dt]; simp [hi]
      · by_cases a3 : x.val = 3
        · have : x = tp ht 3 (by decide) := Fin.ext a3
          subst this; rw [fwdSlot_3, cb_dt]; simp [ho, Ne.symm hio]
        · rw [cb_high _ (fwdSlot_high i o a0 a1 a3), hτ x a0 a1 a3]
  · intro x hx
    by_cases h9 : x.val < 9
    · rw [eq_dt h9, cb_dt, cb_dt]
      have n0 : (⟨x.val, h9⟩ : Fin 9) ≠ 0 := fun e => hx (tp ht 0 (by decide)) (by
        rw [fwdSlot_0, ← e]; exact (eq_dt h9).symm)
      have ni : (⟨x.val, h9⟩ : Fin 9) ≠ i := fun e => hx (tp ht 1 (by decide)) (by
        rw [fwdSlot_1, ← e]; exact (eq_dt h9).symm)
      have no : (⟨x.val, h9⟩ : Fin 9) ≠ o := fun e => hx (tp ht 3 (by decide)) (by
        rw [fwdSlot_3, ← e]; exact (eq_dt h9).symm)
      simp [n0, ni, no]
    · rw [cb_high _ (by omega), cb_high _ (by omega)]

theorem zF_ne_zH : (zF : Fin 𝕌) ≠ zH := by decide
theorem zG_ne_zH : (zG : Fin 𝕌) ≠ zH := by decide
theorem zG_ne_zF : (zG : Fin 𝕌) ≠ zF := by decide
theorem zO_ne_zH : (zO : Fin 𝕌) ≠ zH := by decide
theorem zO_ne_zF : (zO : Fin 𝕌) ≠ zF := by decide
theorem zO_ne_zG : (zO : Fin 𝕌) ≠ zG := by decide

theorem uSlot_zH (h f g o : Fin 9) : uSlot t h f g o zH = dt t h := by simp [uSlot]
theorem uSlot_zF (h f g o : Fin 9) : uSlot t h f g o zF = dt t f := by simp [uSlot, zF_ne_zH]
theorem uSlot_zG (h f g o : Fin 9) : uSlot t h f g o zG = dt t g := by simp [uSlot, zG_ne_zH, zG_ne_zF]
theorem uSlot_zO (h f g o : Fin 9) : uSlot t h f g o zO = dt t o := by simp [uSlot, zO_ne_zH, zO_ne_zF, zO_ne_zG]
theorem uSlot_high (h f g o : Fin 9) {x : Fin 𝕌} (a0 : x ≠ zH) (a1 : x ≠ zF) (a2 : x ≠ zG) (a3 : x ≠ zO) :
    9 ≤ (uSlot t h f g o x).val := by
  simp [uSlot, a0, a1, a2, a3]

/-- What the ring product's bank sees: tapes `h`, `f`, `g`, `o` on `zH`, `zF`, `zG`, `zO`. -/
def uView (v : Fin 9 → WTape) (h f g o : Fin 9) : Fin 𝕌 → WTape := fun x =>
  if x = zH then v h else if x = zF then v f else if x = zG then v g else if x = zO then v o else emp

theorem cb_comp_uSlot (v : Fin 9 → WTape) (h f g o : Fin 9) : cb t v ∘ uSlot t h f g o = uView v h f g o := by
  funext x
  simp only [Function.comp_apply, uView]
  by_cases a0 : x = zH
  · subst a0; simp [uSlot_zH, cb_dt]
  · by_cases a1 : x = zF
    · subst a1; simp [uSlot_zF, cb_dt, zF_ne_zH]
    · by_cases a2 : x = zG
      · subst a2; simp [uSlot_zG, cb_dt, zG_ne_zH, zG_ne_zF]
      · by_cases a3 : x = zO
        · subst a3; simp [uSlot_zO, cb_dt, zO_ne_zH, zO_ne_zF, zO_ne_zG]
        · simp only [a0, a1, a2, a3, ↓reduceIte]
          exact cb_high v (uSlot_high h f g o a0 a1 a2 a3)

theorem upd_cb_uSlot {h f g o : Fin 9} (hd : [h, f, g, o].Nodup) (v : Fin 9 → WTape) (τ : Fin 𝕌 → WTape)
    (hτ : ∀ x, x ≠ zH → x ≠ zF → x ≠ zG → x ≠ zO → τ x = emp) :
    upd (cb t v) (uSlot t h f g o) τ = cb t (fun j => if j = h then τ zH else if j = f then τ zF
      else if j = g then τ zG else if j = o then τ zO else v j) := by
  have hd' := hd
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hd'
  obtain ⟨⟨n1, n2, n3⟩, ⟨n4, n5⟩, n6, -⟩ := hd'
  apply upd_eq_of _ (uSlot_inj hd)
  · intro x
    by_cases a0 : x = zH
    · subst a0; rw [uSlot_zH, cb_dt]; simp
    · by_cases a1 : x = zF
      · subst a1; rw [uSlot_zF, cb_dt]; simp [Ne.symm n1]
      · by_cases a2 : x = zG
        · subst a2; rw [uSlot_zG, cb_dt]; simp [Ne.symm n2, Ne.symm n4]
        · by_cases a3 : x = zO
          · subst a3; rw [uSlot_zO, cb_dt]; simp [Ne.symm n3, Ne.symm n5, Ne.symm n6]
          · rw [cb_high _ (uSlot_high h f g o a0 a1 a2 a3), hτ x a0 a1 a2 a3]
  · intro x hx
    by_cases h9 : x.val < 9
    · rw [eq_dt h9, cb_dt, cb_dt]
      have nh : (⟨x.val, h9⟩ : Fin 9) ≠ h := fun e => hx zH (by rw [uSlot_zH, ← e]; exact (eq_dt h9).symm)
      have nf : (⟨x.val, h9⟩ : Fin 9) ≠ f := fun e => hx zF (by rw [uSlot_zF, ← e]; exact (eq_dt h9).symm)
      have ng : (⟨x.val, h9⟩ : Fin 9) ≠ g := fun e => hx zG (by rw [uSlot_zG, ← e]; exact (eq_dt h9).symm)
      have no : (⟨x.val, h9⟩ : Fin 9) ≠ o := fun e => hx zO (by rw [uSlot_zO, ← e]; exact (eq_dt h9).symm)
      simp [nh, nf, ng, no]
    · rw [cb_high _ (by omega), cb_high _ (by omega)]

/-! ### The calls -/

theorem fView_eq_start2 {v : Fin 9 → WTape} {i o : Fin 9} {hdr F : List Bool} (h0 : v 0 = reg hdr)
    (hi : v i = reg F) (ho : v o = emp) : fView t v i o = start2 t hdr F := by
  funext x
  simp only [fView, start2]
  split_ifs <;> first | rfl | omega | simp_all

/-- A transform call: data tape `o` receives the output word. -/
theorem runs_fwdCall (M : Program t q₁ a) (ht : 4 ≤ t) {i o : Fin 9} (hi : i ≠ 0) (ho : o ≠ 0) (hio : i ≠ o)
    (hinj : Function.Injective (fwdSlot t i o)) (v : Fin 9 → WTape) {hdr F O : List Bool} {k : ℕ}
    (h0 : v 0 = reg hdr) (hvi : v i = reg F) (hvo : v o = emp)
    (hM : HoareTime M (· = bank hdr F [] []) (· = bank hdr F [] O) k) :
    Runs (.prim (Prim.ofHoare (prog2 M ht) (by omega)) (fwdSlot t i o) hinj) (cb t v)
      (· = cb t (Function.update v o (reg O))) (k + 4 * (hdr.length + F.length + O.length) + 40) := by
  have hT : HoareTo (prog2 M ht) (cb t v ∘ fwdSlot t i o)
      (Function.update (start2 t hdr F) (tp ht 3 (by decide)) (reg O))
      (k + 4 * (hdr.length + F.length + O.length) + 40) := by
    rw [cb_comp_fwdSlot, fView_eq_start2 h0 hvi hvo]
    exact prog2_hoare M ht hM
  refine (runs_ofHoare _ _ hinj hT).mono (fun σ' h => ?_) le_rfl
  rw [h, upd_cb_fwdSlot hi ho hio v _ ?_ ht]
  · congr 1
    funext j
    by_cases j0 : j = 0
    · subst j0; simp [start2, tp, Ne.symm ho, h0]
    · by_cases ji : j = i
      · subst ji; rw [Function.update_of_ne hio, hvi]; simp [start2, tp, j0]
      · by_cases jo : j = o
        · subst jo; simp [start2, tp, j0, ji]
        · simp [j0, ji, jo]
  · intro x a0 a1 a3
    have n3 : x ≠ tp ht 3 (by decide) := fun e => a3 (by rw [e]; rfl)
    simp [Function.update_of_ne n3, start2, a0, a1]

/-- A call of a ring-product bank program: data tapes `h, f, g, o` on `zH, zF, zG, zO`. -/
theorem runs_uCall {q : ℕ} (M : Program 𝕌 q 0) {h f g o : Fin 9} (hd : [h, f, g, o].Nodup)
    (hinj : Function.Injective (uSlot t h f g o)) (v : Fin 9 → WTape) (τ' : Fin 𝕌 → WTape) {k : ℕ}
    (hM : HoareTo M (uView v h f g o) τ' k)
    (hτ : ∀ x, x ≠ zH → x ≠ zF → x ≠ zG → x ≠ zO → τ' x = emp) :
    Runs (a := a) (.prim (Prim.lift (Prim.ofHoare M (by decide))) (uSlot t h f g o) hinj) (cb t v)
      (· = cb t (fun j => if j = h then τ' zH else if j = f then τ' zF
        else if j = g then τ' zG else if j = o then τ' zO else v j)) k := by
  have hT : HoareTo M (cb t v ∘ uSlot t h f g o) τ' k := by rw [cb_comp_uSlot]; exact hM
  refine (runs_ofHoare_lift _ _ hinj hT).mono (fun σ' e => ?_) le_rfl
  rw [e, upd_cb_uSlot hd v τ' hτ]

theorem runs_clearData (j : Fin 9) (v : Fin 9 → WTape) :
    Runs (a := a) (clear (dt t j)) (cb t v) (· = cb t (Function.update v j emp)) (2 * clen (v j).words + 2) := by
  refine (runs_clear (dt t j) (cb t v)).mono (fun σ' e => ?_) (by rw [cb_dt])
  rw [e]
  funext x
  by_cases hx : x = dt t j
  · subst hx; simp [cb_dt, emp]
  · rw [Function.update_of_ne hx]
    by_cases h9 : x.val < 9
    · rw [eq_dt h9, cb_dt, cb_dt, Function.update_of_ne (fun e => hx (by rw [eq_dt h9, e]))]
    · rw [cb_high _ (by omega), cb_high _ (by omega)]

end IntegerMultBounds.Schoenhage
