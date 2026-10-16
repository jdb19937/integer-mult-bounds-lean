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
  split_ifs at h' <;> simp only at h' <;> omega

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
  split_ifs at e' <;> simp only [Fin.ext_iff, val_zH, val_zF, val_zG, val_zO] at * <;> omega

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
        · subst jo; simp [tp, j0, ji]
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

/-! ### The core -/

/-- The compiled scaling step. -/
noncomputable def scProg : Program 𝕌 (compile (a := 0) (by decide) convScale).1 0 :=
  (compile (a := 0) (by decide) convScale).2

/-- The scaling step's start: the header on `zH`, the opposite transform's output on `zF`. -/
def scaleStart (hdr V : List Bool) : Fin 𝕌 → WTape :=
  Function.update (Function.update (fun _ => emp) zH (reg hdr)) zF (reg V)

/-- Forward transforms of both operands, pointwise products, the opposite transform, scaling, cleanup. -/
noncomputable def convCore (Mf : Program t q₁ a) (Mo : Program t q₂ a) (ht : 4 ≤ t) : Cmd a (NB t) :=
  .seq (.prim (Prim.ofHoare (prog2 Mf ht) (by omega)) (fwdSlot t 1 5) (fwdSlot_inj (by decide) (by decide) (by decide))) <|
  .seq (.prim (Prim.ofHoare (prog2 Mf ht) (by omega)) (fwdSlot t 2 6) (fwdSlot_inj (by decide) (by decide) (by decide))) <|
  .seq (.prim (Prim.lift (Prim.ofHoare pwCoreProg (by decide))) (uSlot t 0 5 6 7) (uSlot_inj (by decide))) <|
  .seq (.prim (Prim.ofHoare (prog2 Mo ht) (by omega)) (fwdSlot t 7 8) (fwdSlot_inj (by decide) (by decide) (by decide))) <|
  .seq (.prim (Prim.lift (Prim.ofHoare scProg (by decide))) (uSlot t 0 8 4 3) (uSlot_inj (by decide))) <|
  .seq (clear (dt t 5)) <| .seq (clear (dt t 6)) <| .seq (clear (dt t 7)) (clear (dt t 8))

theorem uView_startBank {v : Fin 9 → WTape} {h f g o : Fin 9} {hdr F G : List Bool} (h0 : v h = reg hdr)
    (hf : v f = reg F) (hg : v g = reg G) (ho : v o = emp) : uView v h f g o = startBank hdr F G := by
  funext x
  simp only [uView, startBank]
  by_cases a0 : x = zH
  · subst a0; simp [h0, zF_ne_zH.symm, zG_ne_zH.symm]
  · by_cases a1 : x = zF
    · subst a1; simp [hf, zF_ne_zH, zG_ne_zF.symm]
    · by_cases a2 : x = zG
      · subst a2; simp [hg, zG_ne_zH, zG_ne_zF]
      · by_cases a3 : x = zO
        · subst a3; simp [ho, zO_ne_zH, zO_ne_zF, zO_ne_zG]
        · simp [a0, a1, a2, a3]

theorem uView_scaleStart {v : Fin 9 → WTape} {h f g o : Fin 9} {hdr V : List Bool} (h0 : v h = reg hdr)
    (hf : v f = reg V) (hg : v g = emp) (ho : v o = emp) : uView v h f g o = scaleStart hdr V := by
  funext x
  simp only [uView, scaleStart]
  by_cases a0 : x = zH
  · subst a0; simp [h0, zF_ne_zH.symm]
  · by_cases a1 : x = zF
    · subst a1; simp [hf, zF_ne_zH]
    · by_cases a2 : x = zG
      · subst a2; simp [hg, zG_ne_zH, zG_ne_zF]
      · by_cases a3 : x = zO
        · subst a3; simp [ho, zO_ne_zH, zO_ne_zF, zO_ne_zG]
        · simp [a0, a1, a2, a3]

/-- The core's cost beyond its five calls. -/
def coreExtra (hdr F G Fh Gh U V : ℕ) : ℕ := 4 * (3 * hdr + F + G + 2 * Fh + 2 * Gh + 2 * U + 2 * V) + 400

set_option maxHeartbeats 8000000 in
theorem runs_convCore (Mf : Program t q₁ a) (Mo : Program t q₂ a) (ht : 4 ≤ t)
    {hdr F G Fh Gh U V Out Desc : List Bool} {kF kG kP kO kS : ℕ}
    (hF : HoareTime Mf (· = bank hdr F [] []) (· = bank hdr F [] Fh) kF)
    (hG : HoareTime Mf (· = bank hdr G [] []) (· = bank hdr G [] Gh) kG)
    (hP : HoareTo pwCoreProg (startBank hdr Fh Gh) (Function.update (startBank hdr Fh Gh) zO (reg U)) kP)
    (hO : HoareTime Mo (· = bank hdr U [] []) (· = bank hdr U [] V) kO)
    (hS : HoareTo scProg (scaleStart hdr V)
      (Function.update (Function.update (scaleStart hdr V) zO (reg Out)) zG (reg Desc)) kS) :
    Runs (convCore Mf Mo ht) (cb t ![reg hdr, reg F, reg G, emp, emp, emp, emp, emp, emp])
      (· = cb t ![reg hdr, reg F, reg G, reg Out, reg Desc, emp, emp, emp, emp])
      (kF + kG + kP + kO + kS + coreExtra hdr.length F.length G.length Fh.length Gh.length U.length V.length) := by
  set v0 : Fin 9 → WTape := ![reg hdr, reg F, reg G, emp, emp, emp, emp, emp, emp]
  have s1 := runs_fwdCall Mf ht (i := 1) (o := 5) (by decide) (by decide) (by decide)
    (fwdSlot_inj (by decide) (by decide) (by decide)) v0 rfl rfl rfl hF
  set v1 := Function.update v0 5 (reg Fh)
  have s2 := runs_fwdCall Mf ht (i := 2) (o := 6) (by decide) (by decide) (by decide)
    (fwdSlot_inj (by decide) (by decide) (by decide)) v1 rfl rfl rfl hG
  set v2 := Function.update v1 6 (reg Gh)
  have hv2 : uView v2 0 5 6 7 = startBank hdr Fh Gh := uView_startBank rfl rfl rfl rfl
  have s3 := runs_uCall (t := t) (a := a) pwCoreProg (h := 0) (f := 5) (g := 6) (o := 7) (by decide)
    (uSlot_inj (by decide)) v2 _ (by rw [hv2]; exact hP)
    (fun x a0 a1 a2 a3 => by simp [Function.update_of_ne a3, startBank, a0, a1, a2])
  set v3 := Function.update v2 7 (reg U)
  have hv3 : (fun j : Fin 9 => if j = 0 then Function.update (startBank hdr Fh Gh) zO (reg U) zH
      else if j = 5 then Function.update (startBank hdr Fh Gh) zO (reg U) zF
      else if j = 6 then Function.update (startBank hdr Fh Gh) zO (reg U) zG
      else if j = 7 then Function.update (startBank hdr Fh Gh) zO (reg U) zO else v2 j) = v3 := by
    funext j
    fin_cases j <;> simp [v3, v2, v1, v0, startBank, zO_ne_zH.symm, zO_ne_zF.symm, zO_ne_zG.symm,
      zF_ne_zH.symm, zG_ne_zH.symm, zG_ne_zF.symm]
  have s3' := s3.mono (fun σ h => h.trans (congrArg (cb t) hv3)) le_rfl
  have s4 := runs_fwdCall Mo ht (i := 7) (o := 8) (by decide) (by decide) (by decide)
    (fwdSlot_inj (by decide) (by decide) (by decide)) v3 rfl rfl rfl hO
  set v4 := Function.update v3 8 (reg V)
  have hv4 : uView v4 0 8 4 3 = scaleStart hdr V := uView_scaleStart rfl rfl rfl rfl
  have s5 := runs_uCall (t := t) (a := a) scProg (h := 0) (f := 8) (g := 4) (o := 3) (by decide)
    (uSlot_inj (by decide)) v4 _ (by rw [hv4]; exact hS)
    (fun x a0 a1 a2 a3 => by
      simp [Function.update_of_ne a3, Function.update_of_ne a2, scaleStart, a0, a1])
  set v5 := Function.update (Function.update v4 3 (reg Out)) 4 (reg Desc)
  have hv5 : (fun j : Fin 9 => if j = 0 then
        Function.update (Function.update (scaleStart hdr V) zO (reg Out)) zG (reg Desc) zH
      else if j = 8 then Function.update (Function.update (scaleStart hdr V) zO (reg Out)) zG (reg Desc) zF
      else if j = 4 then Function.update (Function.update (scaleStart hdr V) zO (reg Out)) zG (reg Desc) zG
      else if j = 3 then Function.update (Function.update (scaleStart hdr V) zO (reg Out)) zG (reg Desc) zO
      else v4 j) = v5 := by
    funext j
    fin_cases j <;> simp [v5, v4, v3, v2, v1, v0, scaleStart, zO_ne_zH.symm, zO_ne_zF.symm, 
      zF_ne_zH.symm, zG_ne_zH.symm, zG_ne_zF.symm, zO_ne_zG]
  have s5' := s5.mono (fun σ h => h.trans (congrArg (cb t) hv5)) le_rfl
  have c5 := runs_clearData (t := t) (a := a) 5 v5
  have c6 := runs_clearData (t := t) (a := a) 6 (Function.update v5 5 emp)
  have c7 := runs_clearData (t := t) (a := a) 7 (Function.update (Function.update v5 5 emp) 6 emp)
  have c8 := runs_clearData (t := t) (a := a) 8
    (Function.update (Function.update (Function.update v5 5 emp) 6 emp) 7 emp)
  have hfin : Function.update (Function.update (Function.update (Function.update v5 5 emp) 6 emp) 7 emp) 8 emp =
      ![reg hdr, reg F, reg G, reg Out, reg Desc, emp, emp, emp, emp] := by
    funext j
    fin_cases j <;> rfl
  refine (Runs.then s1 (Runs.then s2 (Runs.then s3' (Runs.then s4 (Runs.then s5' (Runs.then c5
    (Runs.then c6 (Runs.then c7 c8)))))))).mono (fun σ h => by rw [h, hfin]) ?_
  simp only [coreExtra, v5, v4, v3, v2, v1, v0, Function.update_apply]
  simp [reg, WTape.words, clen]
  omega

/-! ### The program in the paper's format -/

/-- Seal the header and operands, run the core, unseal the five data tapes. -/
noncomputable def convProg (Mf : Program t q₁ a) (Mo : Program t q₂ a) (ht : 4 ≤ t) :=
  Machine.seq (sealAt (dt t 0)) <| Machine.seq (sealAt (dt t 1)) <| Machine.seq (sealAt (dt t 2)) <|
  Machine.seq (compile (by unfold NB; omega) (convCore Mf Mo ht)).2 <|
  Machine.seq (unsealAt (dt t 0)) <| Machine.seq (unsealAt (dt t 1)) <| Machine.seq (unsealAt (dt t 2)) <|
  Machine.seq (unsealAt (dt t 3)) (unsealAt (dt t 4))

theorem cb_pos (v : Fin 9 → WTape) (hv : ∀ j, (v j).left = []) (x : Fin (NB t)) : (cb t v x).pos = 0 := by
  simp only [cb]
  split_ifs
  · simp [WTape.pos, hv]
  · rfl

theorem dt_ne {i j : Fin 9} (h : i ≠ j) : dt t i ≠ dt t j := fun e => h (Fin.ext (by
  have := congrArg Fin.val e; simpa [dt] using this))

theorem tape_cases {f g : Fin (NB t) → ℤ → Fin (a + 4)} (hlow : ∀ j : Fin 9, f (dt t j) = g (dt t j))
    (hhigh : ∀ x : Fin (NB t), 9 ≤ x.val → f x = g x) : f = g := by
  funext x
  by_cases h9 : x.val < 9
  · rw [eq_dt h9]; exact hlow _
  · exact hhigh x (by omega)

theorem bank5_low (hdr F G O D : List Bool) (j : Fin 9) :
    (bank5 (t := NB t) (a := a) hdr F G O D).tape (dt t j) =
      (![wordAt hdr, wordAt F, wordAt G, wordAt O, wordAt D, fun _ => blank, fun _ => blank, fun _ => blank,
        fun _ => blank] : Fin 9 → ℤ → Fin (a + 4)) j := by
  fin_cases j <;> rfl

theorem bank5_high (hdr F G O D : List Bool) {x : Fin (NB t)} (hx : 9 ≤ x.val) :
    (bank5 (t := NB t) (a := a) hdr F G O D).tape x = fun _ => blank := by
  have h0 : x.val ≠ 0 := by omega
  have h1 : x.val ≠ 1 := by omega
  have h2 : x.val ≠ 2 := by omega
  have h3 : x.val ≠ 3 := by omega
  have h4 : x.val ≠ 4 := by omega
  simp only [bank5, h0, h1, h2, h3, h4, ↓reduceIte]

theorem enc_cb_low (v : Fin 9 → WTape) (j : Fin 9) : (enc (a := a) (cb t v)).tape (dt t j) = (v j).tape := by
  simp [enc, cb_dt]

theorem enc_cb_high (v : Fin 9 → WTape) {x : Fin (NB t)} (hx : 9 ≤ x.val) :
    (enc (a := a) (cb t v)).tape x = fun _ => blank := by
  simp [enc, cb_high v hx, emp_tape']

set_option maxHeartbeats 8000000 in
theorem convProg_hoare (Mf : Program t q₁ a) (Mo : Program t q₂ a) (ht : 4 ≤ t)
    {hdr F G Fh Gh U V Out Desc : List Bool} {kF kG kP kO kS : ℕ}
    (hF : HoareTime Mf (· = bank hdr F [] []) (· = bank hdr F [] Fh) kF)
    (hG : HoareTime Mf (· = bank hdr G [] []) (· = bank hdr G [] Gh) kG)
    (hP : HoareTo pwCoreProg (startBank hdr Fh Gh) (Function.update (startBank hdr Fh Gh) zO (reg U)) kP)
    (hO : HoareTime Mo (· = bank hdr U [] []) (· = bank hdr U [] V) kO)
    (hS : HoareTo scProg (scaleStart hdr V)
      (Function.update (Function.update (scaleStart hdr V) zO (reg Out)) zG (reg Desc)) kS) :
    HoareTime (convProg Mf Mo ht) (· = bank5 hdr F G [] []) (· = bank5 hdr F G Out Desc)
      (kF + kG + kP + kO + kS + coreExtra hdr.length F.length G.length Fh.length Gh.length U.length V.length +
        4 * (hdr.length + F.length + G.length + Out.length + Desc.length) + 60) := by
  obtain ⟨σ', k, hx, hq, hk⟩ := runs_convCore Mf Mo ht hF hG hP hO hS
  subst hq
  have hcore := compile_correct (by unfold NB; omega : 0 < NB t) hx
  have n10 : dt t 1 ≠ dt t 0 := dt_ne (by decide)
  have n20 : dt t 2 ≠ dt t 0 := dt_ne (by decide)
  have n21 : dt t 2 ≠ dt t 1 := dt_ne (by decide)
  have n30 : dt t 3 ≠ dt t 0 := dt_ne (by decide)
  have n31 : dt t 3 ≠ dt t 1 := dt_ne (by decide)
  have n32 : dt t 3 ≠ dt t 2 := dt_ne (by decide)
  have n40 : dt t 4 ≠ dt t 0 := dt_ne (by decide)
  have n41 : dt t 4 ≠ dt t 1 := dt_ne (by decide)
  have n42 : dt t 4 ≠ dt t 2 := dt_ne (by decide)
  have n43 : dt t 4 ≠ dt t 3 := dt_ne (by decide)
  set u0 := bank5 (t := NB t) (a := a) hdr F G [] []
  have h1 := sealAt_hoare (a := a) (dt t 0) hdr u0 rfl (bank5_low hdr F G [] [] 0)
  set u1 : Tapes (NB t) a := ⟨u0.head, Function.update u0.tape (dt t 0) (⟨[], [hdr]⟩ : WTape).tape⟩
  have h2 := sealAt_hoare (a := a) (dt t 1) F u1 rfl
    (by simp only [u1]; rw [Function.update_of_ne n10]; exact bank5_low hdr F G [] [] 1)
  set u2 : Tapes (NB t) a := ⟨u1.head, Function.update u1.tape (dt t 1) (⟨[], [F]⟩ : WTape).tape⟩
  have h3 := sealAt_hoare (a := a) (dt t 2) G u2 rfl
    (by simp only [u2, u1]; rw [Function.update_of_ne n21, Function.update_of_ne n20];
        exact bank5_low hdr F G [] [] 2)
  have e3 : (⟨u2.head, Function.update u2.tape (dt t 2) (⟨[], [G]⟩ : WTape).tape⟩ : Tapes (NB t) a) =
      enc (cb t ![reg hdr, reg F, reg G, emp, emp, emp, emp, emp, emp]) := by
    have hh : u2.head = (enc (a := a) (cb t ![reg hdr, reg F, reg G, emp, emp, emp, emp, emp, emp])).head := by
      funext x; exact (cb_pos _ (fun j => by fin_cases j <;> rfl) x).symm
    rw [Tapes.mk.injEq]
    refine ⟨hh, tape_cases (fun j => ?_) (fun x hx => ?_)⟩
    · rw [enc_cb_low]
      simp only [u2, u1, u0]
      fin_cases j <;> simp [dt_ne, bank5_low, n30, n31, n32, n40, n41,
        n42, Ne.symm n10, Ne.symm n20, Ne.symm n21, 
        emp_tape', wordAt_nil', reg] <;>
        first | rfl | simp [dt, Fin.ext_iff, bank5]
    · rw [enc_cb_high _ hx]
      simp only [u2, u1, u0]
      have hne : ∀ j : Fin 9, x ≠ dt t j := fun j e => by
        have := congrArg Fin.val e; simp [dt] at this; omega
      rw [Function.update_of_ne (hne 2), Function.update_of_ne (hne 1), Function.update_of_ne (hne 0),
        bank5_high _ _ _ _ _ hx]
  set w0 := enc (a := a) (cb t ![reg hdr, reg F, reg G, reg Out, reg Desc, emp, emp, emp, emp])
  have hw0 : w0.head = fun _ => 0 := by
    funext x; exact cb_pos _ (fun j => by fin_cases j <;> rfl) x
  have g1 := unsealAt_hoare (a := a) (dt t 0) hdr w0 (by rw [hw0]) (enc_cb_low _ 0)
  set w1 : Tapes (NB t) a := ⟨w0.head, Function.update w0.tape (dt t 0) (wordAt hdr)⟩
  have g2 := unsealAt_hoare (a := a) (dt t 1) F w1 (by simp [w1, hw0])
    (by simp only [w1]; rw [Function.update_of_ne n10]; exact enc_cb_low _ 1)
  set w2 : Tapes (NB t) a := ⟨w1.head, Function.update w1.tape (dt t 1) (wordAt F)⟩
  have g3 := unsealAt_hoare (a := a) (dt t 2) G w2 (by simp [w2, w1, hw0])
    (by simp only [w2, w1]; rw [Function.update_of_ne n21, Function.update_of_ne n20]; exact enc_cb_low _ 2)
  set w3 : Tapes (NB t) a := ⟨w2.head, Function.update w2.tape (dt t 2) (wordAt G)⟩
  have g4 := unsealAt_hoare (a := a) (dt t 3) Out w3 (by simp [w3, w2, w1, hw0])
    (by simp only [w3, w2, w1]; rw [Function.update_of_ne n32, Function.update_of_ne n31,
        Function.update_of_ne n30]; exact enc_cb_low _ 3)
  set w4 : Tapes (NB t) a := ⟨w3.head, Function.update w3.tape (dt t 3) (wordAt Out)⟩
  have g5 := unsealAt_hoare (a := a) (dt t 4) Desc w4 (by simp [w4, w3, w2, w1, hw0])
    (by simp only [w4, w3, w2, w1]; rw [Function.update_of_ne n43, Function.update_of_ne n42,
        Function.update_of_ne n41, Function.update_of_ne n40]; exact enc_cb_low _ 4)
  have e5 : (⟨w4.head, Function.update w4.tape (dt t 4) (wordAt Desc)⟩ : Tapes (NB t) a) =
      bank5 hdr F G Out Desc := by
    rw [Tapes.mk.injEq]
    refine ⟨hw0, tape_cases (fun j => ?_) (fun x hx => ?_)⟩
    · rw [bank5_low]
      simp only [w4, w3, w2, w1, w0]
      fin_cases j <;> simp [Function.update_apply, 
        Ne.symm n10, Ne.symm n20, Ne.symm n21, Ne.symm n30, Ne.symm n31, Ne.symm n32, Ne.symm n40,
        Ne.symm n41, Ne.symm n42, Ne.symm n43, enc_cb_low, emp_tape'] <;>
        first | rfl | simp [dt, Fin.ext_iff, enc, cb, emp_tape']
    · rw [bank5_high _ _ _ _ _ hx]
      simp only [w4, w3, w2, w1, w0]
      have hne : ∀ j : Fin 9, x ≠ dt t j := fun j e => by
        have := congrArg Fin.val e; simp [dt] at this; omega
      rw [Function.update_of_ne (hne 4), Function.update_of_ne (hne 3), Function.update_of_ne (hne 2),
        Function.update_of_ne (hne 1), Function.update_of_ne (hne 0), enc_cb_high _ hx]
  refine (h1.seq (h2.seq ((h3.consequence (fun v h => h) (fun v h => h.trans e3) le_rfl).seq
    ((hcore.consequence (fun v h => h) (fun v h => h) hk).seq (g1.seq (g2.seq (g3.seq (g4.seq g5)))))))).consequence
    (fun v h => h) (fun v h => h.trans e5) ?_
  omega

end IntegerMultBounds.Schoenhage
