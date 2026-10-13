module

public import IntegerMultBounds.Schoenhage.ScriptParts
public import IntegerMultBounds.Schoenhage.ScriptOps
public import IntegerMultBounds.Schoenhage.DriverScript

/-! The slot loop of the round-script writer (§6) on its own bank of 37 tapes. The bank holds
the script being written (`mO`), the chunk-group layer headers (`mHD`), the current slot `h`
and `h·D` in unary, the loop's ticks, and the constants the slots need: `b`, the long-axis
flags, `L`, the top bits, the axis rows, the prefix exponents, `ℓ ± 1`, `ℓ - 2` and `D`. A
slot's twist words are its exponent table (`runs_tableGenX`) with the table's length in unary
(`runs_twSlot`). -/

@[expose] public section

set_option maxRecDepth 100000

namespace IntegerMultBounds.Schoenhage

open Machine Strm TwistDescriptors Spec.SignedRingProduct ScriptOps ScriptParts

namespace ScriptMain

/-! ### The bank -/

abbrev mO : Fin 37 := 0
abbrev mHD : Fin 37 := 1
abbrev mH : Fin 37 := 2
abbrev mHDD : Fin 37 := 3
abbrev mT : Fin 37 := 4
abbrev mKC : Fin 37 := 5
abbrev mB : Fin 37 := 6
abbrev mFL : Fin 37 := 7
abbrev mLL : Fin 37 := 8
abbrev mTP : Fin 37 := 9
abbrev mRW : Fin 37 := 10
abbrev mE0 : Fin 37 := 11
abbrev mET : Fin 37 := 12
abbrev mP1 : Fin 37 := 13
abbrev mM1 : Fin 37 := 14
abbrev mM2 : Fin 37 := 15
abbrev mN : Fin 37 := 16
abbrev mF1 : Fin 37 := 17
abbrev mF2 : Fin 37 := 18
abbrev mPK : Fin 37 := 19
abbrev mPW : Fin 37 := 20
abbrev mPC : Fin 37 := 21
abbrev mEX : Fin 37 := 22
abbrev mAx : Fin 37 := 23
abbrev mTH : Fin 37 := 24
abbrev mRest : Fin 37 := 25
abbrev mFull : Fin 37 := 26
abbrev mS : Fin 37 := 27
abbrev mX : Fin 37 := 28
abbrev mW0 : Fin 37 := 29
abbrev mW : Fin 37 := 30
abbrev mTT : Fin 37 := 31
abbrev mTab : Fin 37 := 32
abbrev mTJ : Fin 37 := 33
abbrev mCnt : Fin 37 := 34
abbrev mTmp : Fin 37 := 35
abbrev mJ : Fin 37 := 36

/-- The table generators' bank inside the slot bank. -/
def tg : Fin 14 → Fin 37 := ![mAx, mTH, mRest, mFull, mFL, mRW, mTP, mS, mX, mW0, mW, mTT, mTab, mTJ]

theorem tg_injective : Function.Injective tg := by decide

/-! ### Relabelled runs -/

theorem upd_update {s n : ℕ} {f : Fin s → Fin n} (hf : Function.Injective f) (τ : Fin n → WTape)
    (σ : Fin s → WTape) (i : Fin s) (v : WTape) :
    upd τ f (Function.update σ i v) = Function.update (upd τ f σ) (f i) v := by
  funext x
  by_cases hx : ∃ j, f j = x
  · obtain ⟨j, rfl⟩ := hx
    rw [upd_slot τ hf]
    by_cases hj : j = i
    · subst hj; simp
    · rw [Function.update_of_ne hj, Function.update_of_ne (fun e => hj (hf e)), upd_slot τ hf]
  · push Not at hx
    rw [upd_other τ f _ x hx, Function.update_of_ne (fun e => hx i e.symm), upd_other τ f _ x hx]

theorem upd_comp_self {s n : ℕ} {f : Fin s → Fin n} (hf : Function.Injective f) (τ : Fin n → WTape) :
    upd τ f (τ ∘ f) = τ := by
  funext x
  by_cases hx : ∃ j, f j = x
  · obtain ⟨j, rfl⟩ := hx; rw [upd_slot τ hf]; rfl
  · push Not at hx; rw [upd_other τ f _ x hx]

theorem runs_lift {s n : ℕ} (f : Fin s → Fin n) (hf : Function.Injective f) {c : Cmd 0 s} {τ : Fin n → WTape}
    {σ₁ : Fin s → WTape} {B : ℕ} (h : Runs c (τ ∘ f) (· = σ₁) B) : Runs (c.map f hf) τ (· = upd τ f σ₁) B := by
  refine (h.map f hf τ rfl).mono (fun τ' ⟨e, o⟩ => ?_) le_rfl
  funext x
  by_cases hx : ∃ y, f y = x
  · obtain ⟨y, rfl⟩ := hx
    rw [upd_slot τ hf]
    exact congrFun e y
  · simp only [not_exists] at hx
    rw [o x hx, upd_other τ f _ x hx]

/-! ### The values -/

/-- The long-axis flags as words. -/
def flagsW (ts : List ℕ) (ℓ : ℕ) : List (List Bool) := (List.range ts.length).map fun i => [decide (axLen ts i = ℓ)]

/-- The long axes' top bits as words. -/
def topsW (ts : List ℕ) (ℓ K : ℕ) : List (List Bool) := (longs ts ℓ).map fun i => ones (paperSigma ts ℓ K i (ℓ - 1))

/-- The constants of the slot bank. -/
def mconst (ℓ K : ℕ) (ts : List ℕ) : Fin 37 → WTape :=
  let D := ts.length
  let q := (ℓ - 1) / K
  let b := (ℓ - 1) % K
  Function.update (Function.update (Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update
    (fun _ => emp)
    mKC (reg [true])) mB (reg (ones b))) mFL ⟨[], flagsW ts ℓ⟩) mLL (reg (ones (longs ts ℓ).length)))
    mTP ⟨[], topsW ts ℓ K⟩) mRW ⟨[], rowWords ts ℓ K⟩) mE0 (reg (ones (ℓ + 1 + q * (D * K)))))
    mET (reg (ones (ℓ + 1 + q * (D * K) + b * D)))) mP1 (reg (ones (ℓ + 1)))) mM1 (reg (ones (ℓ - 1))))
    mM2 (reg (ones (ℓ - 2)))) mN (reg (ones D))

/-- A state of the slot loop: headers `hd`, script `o`, ticks `tt`, slot `h`. -/
def mst (ℓ K : ℕ) (ts : List ℕ) (hd o tt : WTape) (h : ℕ) : Fin 37 → WTape :=
  Function.update (Function.update (Function.update (Function.update (Function.update (mconst ℓ K ts)
    mO o) mHD hd) mH (reg (ones h))) mHDD (reg (ones (h * ts.length)))) mT tt

/-! ### The twist words of a slot below the top -/

/-- The twist words of a slot below the top: ticks for the table, its exponent weight, the
table, then the table with its length. -/
noncomputable def twSlot : Cmd 0 37 :=
  .seq (ticksReg mN mAx (by decide)) <| .seq (ticksReg mH mTH (by decide)) <|
  .seq (dropReg mM2 mH mTmp (by decide) (by decide) (by decide)) <| .seq (ticksReg mTmp mRest (by decide)) <|
  .seq (clear mTmp) <| .seq (dropReg mP1 mH mTmp (by decide) (by decide) (by decide)) <|
  .seq (pow2 mTmp mPK mW0 mPC mJ (by decide) (by decide) (by decide)) <| .seq (clear mTmp) <|
  .seq (SigmaTableTape.tableGen.map tg tg_injective) <| .seq (rewind mRW) <| .seq (clear mAx) <|
  .seq (clear mTH) <| .seq (clear mRest) <| .seq (clear mW0) <|
  emitTab mTab mO mCnt mKC mJ (by decide) (by decide) (by decide) (by decide)

theorem pow_weight {ℓ h : ℕ} (hh : h < ℓ) : 2 ^ (ℓ + 1 - h) = 2 * (2 * 2 ^ ℓ / 2 ^ (h + 1)) := by
  have e : 2 * 2 ^ ℓ = 2 ^ (ℓ - h) * 2 ^ (h + 1) := by
    rw [← pow_add, show ℓ - h + (h + 1) = ℓ + 1 by omega, pow_succ]; ring
  rw [e, Nat.mul_div_cancel _ (by positivity), ← pow_succ']
  congr 1; omega

/-- The bound on the words of a slot's table. -/
theorem tableWords_le {ℓ K : ℕ} {ts : List ℕ} (hL : LayoutOK (2 ^ ℓ) ts ℓ K) {h : ℕ} :
    ∀ w ∈ tableWords (slotTable (paperPerm hL) (2 ^ ℓ) ts (slotAxes ts h) h),
      w.length ≤ Nat.log 2 ts.prod + 4 * 2 ^ ℓ := by
  have hok : TableOK (2 ^ ℓ) (Nat.log 2 ts.prod) (slotTable (paperPerm hL) (2 ^ ℓ) ts (slotAxes ts h) h) :=
    slotTable_ok _ _ _ _ _ (fun i hi => by
      obtain ⟨hi1, hi2⟩ := slotAxes_valid ts h i hi
      have := axOff_add_len_le hL.1 hi1; omega)
  intro w hw
  simp only [tableWords, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false] at hw
  obtain ⟨e, he, hw⟩ := hw
  obtain ⟨h1, h2, h3⟩ := hok e he
  rcases hw with rfl | rfl | rfl <;> simp <;> omega

theorem length_tableWords {n : ℕ} (π : BitPerm n) (r : ℕ) (ts Is : List ℕ) (h : ℕ) :
    (tableWords (slotTable π r ts Is h)).length = 3 * (Is.length * h) := by
  simp only [tableWords, slotTable, List.length_flatMap, List.length_cons, List.length_nil, List.map_const',
    List.sum_replicate, List.flatMap_assoc, List.length_map, List.length_range, smul_eq_mul]
  induction Is with
  | nil => simp
  | cons i Is ih => simp at ih ⊢; ring

theorem tg_vals : tg 0 = mAx ∧ tg 1 = mTH ∧ tg 2 = mRest ∧ tg 3 = mFull ∧ tg 4 = mFL ∧ tg 5 = mRW ∧
    tg 6 = mTP ∧ tg 7 = mS ∧ tg 8 = mX ∧ tg 9 = mW0 ∧ tg 10 = mW ∧ tg 11 = mTT ∧ tg 12 = mTab ∧
    tg 13 = mTJ := by decide

@[simp] theorem tg_0 : tg 0 = mAx := rfl
@[simp] theorem tg_1 : tg 1 = mTH := rfl
@[simp] theorem tg_2 : tg 2 = mRest := rfl
@[simp] theorem tg_3 : tg 3 = mFull := rfl
@[simp] theorem tg_4 : tg 4 = mFL := rfl
@[simp] theorem tg_5 : tg 5 = mRW := rfl
@[simp] theorem tg_6 : tg 6 = mTP := rfl
@[simp] theorem tg_7 : tg 7 = mS := rfl
@[simp] theorem tg_8 : tg 8 = mX := rfl
@[simp] theorem tg_9 : tg 9 = mW0 := rfl
@[simp] theorem tg_10 : tg 10 = mW := rfl
@[simp] theorem tg_11 : tg 11 = mTT := rfl
@[simp] theorem tg_12 : tg 12 = mTab := rfl
@[simp] theorem tg_13 : tg 13 = mTJ := rfl

/-- The cost of a slot's twist words below the top. -/
def twCost (ℓ K : ℕ) (ts : List ℕ) (h : ℕ) : ℕ :=
  3 * ts.length + 20 + 1 + (3 * h + 20 + 1 + (4 * (ℓ - 2) + 4 * h + 40 + 1 + (3 * (ℓ - 2 - h) + 20 + 1 +
    (2 * (ℓ - 2 - h + 1) + 2 + 1 + (4 * (ℓ + 1) + 4 * h + 40 + 1 +
    ((ℓ + 1 - h) * (8 * 2 ^ (ℓ + 1 - h) + 50) + 6 * (ℓ + 1 - h) + 30 + 1 + (2 * (ℓ + 1 - h + 1) + 2 + 1 +
    (ts.length * (SigmaTableTape.roundAxisCost (ℓ - 1) h (Nat.log 2 ts.prod) (2 * (2 * 2 ^ ℓ / 2 ^ (h + 1))) + 2) +
      1 + (clen (rowWords ts ℓ K) + 2 + 1 + (2 * ts.length + 2 + 1 + (2 * h + 2 + 1 + (2 * (ℓ - 1 - 1 - h) + 2 + 1 +
    (2 * (2 ^ (ℓ + 1 - h) + 1) + 2 + 1 +
    (3 * (ts.length * h) * (7 * (Nat.log 2 ts.prod + 4 * 2 ^ ℓ) + 60) + 80))))))))))))))

set_option maxHeartbeats 64000000 in
/-- `runs_twSlot`: below the top, the slot's twist words go to the script and every other tape
of the slot bank is restored. -/
theorem runs_twSlot {ℓ K : ℕ} {ts : List ℕ} (hL : LayoutOK (2 ^ ℓ) ts ℓ K) {h : ℕ} (hh : h < ℓ - 1)
    (hd tt : WTape) (acc : List (List Bool)) :
    Runs twSlot (mst ℓ K ts hd ⟨acc, []⟩ tt h)
      (· = mst ℓ K ts hd ⟨(twistWords (paperPerm hL) (2 ^ ℓ) ts h).reverse ++ acc, []⟩ tt h)
      (twCost ℓ K ts h) := by
  set σ := mst ℓ K ts hd ⟨acc, []⟩ tt h with hσ
  have s1 := runs_ticksReg (a := 0) (show mN ≠ mAx by decide) σ (u := ones ts.length) (by tsimp [hσ, mst, mconst])
    (by tsimp [hσ, mst, mconst])
  set σ₁ := Function.update σ mAx ⟨[], List.replicate (ones ts.length).length []⟩ with hσ₁
  have s2 := runs_ticksReg (a := 0) (show mH ≠ mTH by decide) σ₁ (u := ones h) (by tsimp [hσ₁, hσ, mst, mconst])
    (by tsimp [hσ₁, hσ, mst, mconst])
  set σ₂ := Function.update σ₁ mTH ⟨[], List.replicate (ones h).length []⟩ with hσ₂
  have s3 := runs_dropReg (a := 0) (show mM2 ≠ mH by decide) (show mM2 ≠ mTmp by decide)
    (show mH ≠ mTmp by decide) σ₂ (u := ones (ℓ - 2)) (v := ones h) (by tsimp [hσ₂, hσ₁, hσ, mst, mconst])
    (by tsimp [hσ₂, hσ₁, hσ, mst, mconst]) (by tsimp [hσ₂, hσ₁, hσ, mst, mconst])
  set σ₃ := Function.update σ₂ mTmp (reg ((ones (ℓ - 2)).drop (ones h).length)) with hσ₃
  have s4 := runs_ticksReg (a := 0) (show mTmp ≠ mRest by decide) σ₃ (u := ones (ℓ - 2 - h))
    (by tsimp [hσ₃]) (by tsimp [hσ₃, hσ₂, hσ₁, hσ, mst, mconst])
  set σ₄ := Function.update σ₃ mRest ⟨[], List.replicate (ones (ℓ - 2 - h)).length []⟩ with hσ₄
  have s5 := runs_clear' (a := 0) mTmp σ₄ (T := reg (ones (ℓ - 2 - h))) (by tsimp [hσ₄, hσ₃])
  set σ₅ := Function.update σ₄ mTmp emp with hσ₅
  have s6 := runs_dropReg (a := 0) (show mP1 ≠ mH by decide) (show mP1 ≠ mTmp by decide)
    (show mH ≠ mTmp by decide) σ₅ (u := ones (ℓ + 1)) (v := ones h)
    (by tsimp [hσ₅, hσ₄, hσ₃, hσ₂, hσ₁, hσ, mst, mconst]) (by tsimp [hσ₅, hσ₄, hσ₃, hσ₂, hσ₁, hσ, mst, mconst])
    (by tsimp [hσ₅])
  set σ₆ := Function.update σ₅ mTmp (reg ((ones (ℓ + 1)).drop (ones h).length)) with hσ₆
  have s7 := runs_pow2 (a := 0) (show mTmp ≠ mPK by decide) (show mW0 ≠ mPC by decide) (show mPK ≠ mJ by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) σ₆ (e := ℓ + 1 - h)
    (by tsimp [hσ₆]) (by tsimp [hσ₆, hσ₅, hσ₄, hσ₃, hσ₂, hσ₁, hσ, mst, mconst])
    (by tsimp [hσ₆, hσ₅, hσ₄, hσ₃, hσ₂, hσ₁, hσ, mst, mconst]) (by tsimp [hσ₆, hσ₅, hσ₄, hσ₃, hσ₂, hσ₁, hσ, mst, mconst])
    (by tsimp [hσ₆, hσ₅, hσ₄, hσ₃, hσ₂, hσ₁, hσ, mst, mconst])
  set σ₇ := Function.update σ₆ mW0 ⟨[ones (2 ^ (ℓ + 1 - h))], []⟩ with hσ₇
  have s8 := runs_clear' (a := 0) mTmp σ₇ (T := reg (ones (ℓ + 1 - h))) (by tsimp [hσ₇, hσ₆])
  set σ₈ := Function.update σ₇ mTmp emp with hσ₈
  have hw0 : 2 ^ (ℓ + 1 - h) = 2 * (2 * 2 ^ ℓ / 2 ^ (h + 1)) := pow_weight (by omega)
  have st := runs_tableGenX hL (2 ^ ℓ) hh (σ₈ ∘ tg)
    (by simp only [Function.comp_apply, tg_0]; tsimp [hσ₈, hσ₇, hσ₆, hσ₅, hσ₄, hσ₃, hσ₂, hσ₁, SigmaRowsTape.ticks])
    (by simp only [Function.comp_apply, tg_1]; tsimp [hσ₈, hσ₇, hσ₆, hσ₅, hσ₄, hσ₃, hσ₂, SigmaRowsTape.ticks])
    (by rw [show ℓ - 1 - 1 - h = ℓ - 2 - h by omega]; simp only [Function.comp_apply, tg_2]
        tsimp [hσ₈, hσ₇, hσ₆, hσ₅, hσ₄, SigmaRowsTape.ticks])
    (by simp only [Function.comp_apply, tg_5]; tsimp [hσ₈, hσ₇, hσ₆, hσ₅, hσ₄, hσ₃, hσ₂, hσ₁, hσ, mst, mconst])
    (by simp only [Function.comp_apply, tg_7]; tsimp [hσ₈, hσ₇, hσ₆, hσ₅, hσ₄, hσ₃, hσ₂, hσ₁, hσ, mst, mconst])
    (by simp only [Function.comp_apply, tg_8]; tsimp [hσ₈, hσ₇, hσ₆, hσ₅, hσ₄, hσ₃, hσ₂, hσ₁, hσ, mst, mconst])
    (by simp only [Function.comp_apply, tg_10]; tsimp [hσ₈, hσ₇, hσ₆, hσ₅, hσ₄, hσ₃, hσ₂, hσ₁, hσ, mst, mconst])
    (by simp only [Function.comp_apply, tg_9]; tsimp [hσ₈, hσ₇, SigmaRowsTape.endv, hw0])
    (by simp only [Function.comp_apply, tg_11]; tsimp [hσ₈, hσ₇, hσ₆, hσ₅, hσ₄, hσ₃, hσ₂, hσ₁, hσ, mst, mconst])
    (by simp only [Function.comp_apply, tg_12]; tsimp [hσ₈, hσ₇, hσ₆, hσ₅, hσ₄, hσ₃, hσ₂, hσ₁, hσ, mst, mconst])
    (by simp only [Function.comp_apply, tg_13]; tsimp [hσ₈, hσ₇, hσ₆, hσ₅, hσ₄, hσ₃, hσ₂, hσ₁, hσ, mst, mconst])
  have s9 := runs_lift tg tg_injective st
  set T := tableWords (slotTable (paperPerm hL) (2 ^ ℓ) ts (slotAxes ts h) h) with hT
  set σ₉ := Function.update (Function.update (Function.update σ₈ mRW ⟨(rowWords ts ℓ K).reverse, []⟩) mTab
    ⟨T.reverse, []⟩) mAx ⟨List.replicate ts.length [], []⟩ with hσ₉
  have e9 : upd σ₈ tg (Function.update (Function.update (Function.update (σ₈ ∘ tg)
      SigmaTableTape.tR ⟨(rowWords ts ℓ K).reverse, []⟩)
      SigmaTableTape.tTab ⟨T.reverse, []⟩) SigmaTableTape.tAx ⟨List.replicate ts.length [], []⟩) = σ₉ := by
    rw [upd_update tg_injective, upd_update tg_injective, upd_update tg_injective, upd_comp_self tg_injective]
    rfl
  rw [e9] at s9
  have s10 := runs_rewind' (a := 0) mRW σ₉ (L := (rowWords ts ℓ K).reverse) (R := []) (by tsimp [hσ₉])
  set σ₁₀ := Function.update σ₉ mRW ⟨[], (rowWords ts ℓ K).reverse.reverse ++ []⟩ with hσ₁₀
  have s11 := runs_clear' (a := 0) mAx σ₁₀ (T := ⟨List.replicate ts.length [], []⟩) (by tsimp [hσ₁₀, hσ₉])
  set σ₁₁ := Function.update σ₁₀ mAx emp with hσ₁₁
  have s12 := runs_clear' (a := 0) mTH σ₁₁ (T := ⟨[], List.replicate (ones h).length []⟩)
    (by tsimp [hσ₁₁, hσ₁₀, hσ₉, hσ₈, hσ₇, hσ₆, hσ₅, hσ₄, hσ₃, hσ₂])
  set σ₁₂ := Function.update σ₁₁ mTH emp with hσ₁₂
  have s13 := runs_clear' (a := 0) mRest σ₁₂ (T := ⟨[], List.replicate (ones (ℓ - 2 - h)).length []⟩)
    (by tsimp [hσ₁₂, hσ₁₁, hσ₁₀, hσ₉, hσ₈, hσ₇, hσ₆, hσ₅, hσ₄])
  set σ₁₃ := Function.update σ₁₂ mRest emp with hσ₁₃
  have s14 := runs_clear' (a := 0) mW0 σ₁₃ (T := ⟨[ones (2 ^ (ℓ + 1 - h))], []⟩)
    (by tsimp [hσ₁₃, hσ₁₂, hσ₁₁, hσ₁₀, hσ₉, hσ₈, hσ₇])
  set σ₁₄ := Function.update σ₁₃ mW0 emp with hσ₁₄
  have hW := tableWords_le hL (h := h)
  have s15 := runs_emitTab (a := 0) (show mTab ≠ mJ by decide) (show mKC ≠ mCnt by decide)
    (show mCnt ≠ mO by decide) (show mTab ≠ mO by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (Nat.log 2 ts.prod + 4 * 2 ^ ℓ) σ₁₄ T acc
    (by tsimp [hσ₁₄, hσ₁₃, hσ₁₂, hσ₁₁, hσ₁₀, hσ₉])
    (by tsimp [hσ₁₄, hσ₁₃, hσ₁₂, hσ₁₁, hσ₁₀, hσ₉, hσ₈, hσ₇, hσ₆, hσ₅, hσ₄, hσ₃, hσ₂, hσ₁, hσ, mst, mconst])
    (by tsimp [hσ₁₄, hσ₁₃, hσ₁₂, hσ₁₁, hσ₁₀, hσ₉, hσ₈, hσ₇, hσ₆, hσ₅, hσ₄, hσ₃, hσ₂, hσ₁, hσ, mst, mconst])
    (by tsimp [hσ₁₄, hσ₁₃, hσ₁₂, hσ₁₁, hσ₁₀, hσ₉, hσ₈, hσ₇, hσ₆, hσ₅, hσ₄, hσ₃, hσ₂, hσ₁, hσ, mst, mconst])
    (by tsimp [hσ₁₄, hσ₁₃, hσ₁₂, hσ₁₁, hσ₁₀, hσ₉, hσ₈, hσ₇, hσ₆, hσ₅, hσ₄, hσ₃, hσ₂, hσ₁, hσ, mst, mconst])
    hW
  have hlenT : T.length = 3 * (ts.length * h) := by
    rw [hT, length_tableWords, slotAxes_below_top hL hh, List.length_range]
  refine (Runs.then s1 (Runs.then s2 (Runs.then s3 (Runs.then s4 (Runs.then s5 (Runs.then s6 (Runs.then s7
    (Runs.then s8 (Runs.then s9 (Runs.then s10 (Runs.then s11 (Runs.then s12 (Runs.then s13 (Runs.then s14
    s15)))))))))))))).mono (fun σ' e => ?_) ?_
  · rw [e]
    have htw : (twistWords (paperPerm hL) (2 ^ ℓ) ts h).reverse ++ acc = T.reverse ++ ones T.length :: acc := by
      simp [twistWords, hT]
    rw [htw]
    funext i
    fin_cases i <;> first | rfl | tsimp [hσ₁₄, hσ₁₃, hσ₁₂, hσ₁₁, hσ₁₀, hσ₉, hσ₈, hσ₇, hσ₆, hσ₅, hσ₄, hσ₃, hσ₂, hσ₁,
      hσ, mst, mconst, emp]
  · rw [hlenT]
    simp only [twCost, length_ones, clen, WTape.words, reg, List.reverse_nil, List.nil_append, List.map_cons,
      List.map_nil, List.sum_cons, List.sum_nil, List.length_replicate, List.map_replicate, List.sum_replicate,
      List.length_nil, smul_eq_mul, List.drop_replicate, ones, List.reverse_reverse, List.append_nil,
      List.length_reverse, List.map_reverse, List.sum_reverse, List.length_append]
    omega

/-! ### Comparing two unary registers -/

/-- `o := [y < x]` for `d = ones x`, `e = ones y` (`o` empty before). -/
noncomputable def geqReg {t : ℕ} (d e o : Fin t) (h1 : d ≠ e) (h2 : d ≠ o) (h3 : e ≠ o) : Cmd 0 t :=
  .seq (op1 geq false d e o h1 h2 h3) <| .seq (rewind d) <| .seq (rewind e) (rewind o)

theorem runs_geqReg {t : ℕ} {d e o : Fin t} (h1 : d ≠ e) (h2 : d ≠ o) (h3 : e ≠ o) (σ : Fin t → WTape)
    {x y : ℕ} (hd : σ d = reg (ones x)) (he : σ e = reg (ones y)) (ho : σ o = emp) :
    Runs (geqReg d e o h1 h2 h3) σ (· = Function.update σ o (reg [decide (y < x)])) (2 * x + 2 * y + 30) := by
  have t1 : time geq (ones x) (fun _ => ones y) ≤ x + y + 7 :=
    (time_le geq (ones x) (fun _ => ones y) y (fun _ => by simp)).trans (by simp)
  have s1 : Runs (a := 0) (op1 geq false d e o h1 h2 h3) σ
      (· = Function.update (Function.update (Function.update σ d ⟨[ones x], []⟩) e ⟨[ones y], []⟩) o
        ⟨[[decide (y < x)]], []⟩) (x + y + 7) := by
    apply Runs.of_wp
    rw [wp_op1]
    simp only [hd, he, ho, reg_cur, reg_right, emp_right, output_geq, parse_syms, length_ones]
    refine ⟨⟨by simp, by simp, trivial, by simp, by simp⟩, ?_, ?_⟩
    · simp [emp]
    · exact t1
  set σ₁ := Function.update (Function.update (Function.update σ d ⟨[ones x], []⟩) e ⟨[ones y], []⟩) o
    ⟨[[decide (y < x)]], []⟩ with hσ₁
  have s2 := runs_rewind' (a := 0) d σ₁ (L := [ones x]) (R := []) (by simp [hσ₁, h1, h2])
  set σ₂ := Function.update σ₁ d ⟨[], [ones x].reverse ++ []⟩ with hσ₂
  have s3 := runs_rewind' (a := 0) e σ₂ (L := [ones y]) (R := []) (by simp [hσ₂, hσ₁, h1.symm, h3])
  set σ₃ := Function.update σ₂ e ⟨[], [ones y].reverse ++ []⟩ with hσ₃
  have s4 := runs_rewind' (a := 0) o σ₃ (L := [[decide (y < x)]]) (R := [])
    (by simp [hσ₃, hσ₂, hσ₁, h2.symm, h3.symm])
  refine (Runs.then s1 (Runs.then s2 (Runs.then s3 s4))).mono (fun σ' e' => ?_) ?_
  · rw [e']
    funext z
    by_cases hzo : z = o
    · subst hzo; simp [reg]
    · by_cases hze : z = e
      · subst hze; simp [hσ₃, hzo, he, reg]
      · by_cases hzd : z = d
        · subst hzd; simp [hσ₃, hσ₂, hzo, hze, hd, reg]
        · simp [hσ₃, hσ₂, hσ₁, hzo, hze, hzd]
  · simp [clen]; omega

/-! ### The top slot's twist words -/

/-- The top slot's twist words: the full row ticks, the weight `4`, the table, its length. -/
noncomputable def twTop : Cmd 0 37 :=
  .seq (ticksReg mM1 mFull (by decide)) <| .seq (emit [[true, true, true, true]] mW0) <|
  .seq (SigmaTableTape.topGen.map tg tg_injective) <| .seq (rewind mRW) <| .seq (rewind mTP) <|
  .seq (rewind mFL) <| .seq (clear mFull) <| .seq (clear mW0) <|
  emitTab mTab mO mCnt mKC mJ (by decide) (by decide) (by decide) (by decide)

/-- The cost of the top slot's twist words. -/
def twTopCost (ℓ K : ℕ) (ts : List ℕ) : ℕ :=
  3 * (ℓ - 1) + 20 + 1 + (8 + 1 + (ts.length * (SigmaTableTape.topAxisCost (ℓ - 1) (Nat.log 2 ts.prod)
    (2 * (2 * 2 ^ ℓ / 2 ^ (ℓ - 1 + 1))) + (ℓ - 1) * (Nat.log 2 ts.prod + 18) + 10) + 1 +
    (clen (rowWords ts ℓ K) + 2 + 1 + (clen (topsW ts ℓ K) + 2 + 1 + (clen (flagsW ts ℓ) + 2 + 1 +
    (2 * (ℓ - 1) + 2 + 1 + (12 + 1 +
    (3 * ((longs ts ℓ).length * (ℓ - 1)) * (7 * (Nat.log 2 ts.prod + 4 * 2 ^ ℓ) + 60) + 80))))))))

set_option maxHeartbeats 64000000 in
/-- `runs_twTop`: the top slot's twist words go to the script, every other tape restored. -/
theorem runs_twTop {ℓ K : ℕ} {ts : List ℕ} (hL : LayoutOK (2 ^ ℓ) ts ℓ K) (hd tt : WTape) (h : ℕ)
    (acc : List (List Bool)) :
    Runs twTop (mst ℓ K ts hd ⟨acc, []⟩ tt h)
      (· = mst ℓ K ts hd ⟨(twistWords (paperPerm hL) (2 ^ ℓ) ts (ℓ - 1)).reverse ++ acc, []⟩ tt h)
      (twTopCost ℓ K ts) := by
  have hℓ : 1 ≤ ℓ := hL.2.2.2
  set σ := mst ℓ K ts hd ⟨acc, []⟩ tt h with hσ
  have s1 := runs_ticksReg (a := 0) (show mM1 ≠ mFull by decide) σ (u := ones (ℓ - 1)) (by tsimp [hσ, mst, mconst])
    (by tsimp [hσ, mst, mconst])
  set σ₁ := Function.update σ mFull ⟨[], List.replicate (ones (ℓ - 1)).length []⟩ with hσ₁
  have s2 := runs_emit (a := 0) [[true, true, true, true]] mW0 σ₁ (by tsimp [hσ₁, hσ, mst, mconst])
  set σ₂ := Function.update σ₁ mW0 ⟨[ones 4], []⟩ with hσ₂
  have e2 : Function.update σ₁ mW0 ⟨[[true, true, true, true]].reverse ++ (σ₁ mW0).left, []⟩ = σ₂ := by
    tsimp [hσ₂, hσ₁, hσ, mst, mconst, ones]
  rw [e2] at s2
  have hw4 : 2 * (2 * 2 ^ ℓ / 2 ^ (ℓ - 1 + 1)) = 4 := by
    rw [show ℓ - 1 + 1 = ℓ by omega, Nat.mul_div_cancel _ (by positivity)]
  have st := runs_topGenX hL (2 ^ ℓ) (σ₂ ∘ tg)
    (by simp only [Function.comp_apply, tg_4]; tsimp [hσ₂, hσ₁, hσ, mst, mconst, flagsW])
    (by simp only [Function.comp_apply, tg_3]; tsimp [hσ₂, hσ₁, SigmaRowsTape.ticks])
    (by simp only [Function.comp_apply, tg_5]; tsimp [hσ₂, hσ₁, hσ, mst, mconst])
    (by simp only [Function.comp_apply, tg_6]; tsimp [hσ₂, hσ₁, hσ, mst, mconst, topsW])
    (by simp only [Function.comp_apply, tg_7]; tsimp [hσ₂, hσ₁, hσ, mst, mconst])
    (by simp only [Function.comp_apply, tg_8]; tsimp [hσ₂, hσ₁, hσ, mst, mconst])
    (by simp only [Function.comp_apply, tg_10]; tsimp [hσ₂, hσ₁, hσ, mst, mconst])
    (by simp only [Function.comp_apply, tg_9]; tsimp [hσ₂, SigmaRowsTape.endv, hw4])
    (by simp only [Function.comp_apply, tg_11]; tsimp [hσ₂, hσ₁, hσ, mst, mconst])
    (by simp only [Function.comp_apply, tg_12]; tsimp [hσ₂, hσ₁, hσ, mst, mconst])
    (by simp only [Function.comp_apply, tg_13]; tsimp [hσ₂, hσ₁, hσ, mst, mconst])
  have s3 := runs_lift tg tg_injective st
  set T := tableWords (slotTable (paperPerm hL) (2 ^ ℓ) ts (slotAxes ts (ℓ - 1)) (ℓ - 1)) with hT
  set σ₃ := Function.update (Function.update (Function.update (Function.update σ₂ mRW
    ⟨(rowWords ts ℓ K).reverse, []⟩) mTab ⟨T.reverse, []⟩) mTP ⟨(topsW ts ℓ K).reverse, []⟩)
    mFL ⟨(flagsW ts ℓ).reverse, []⟩ with hσ₃
  have e3 : upd σ₂ tg (Function.update (Function.update (Function.update (Function.update (σ₂ ∘ tg)
      SigmaTableTape.tR ⟨(rowWords ts ℓ K).reverse, []⟩)
      SigmaTableTape.tTab ⟨T.reverse, []⟩)
      SigmaTableTape.tTop ⟨((longs ts ℓ).map fun i => ones (paperSigma ts ℓ K i (ℓ - 1))).reverse, []⟩)
      SigmaTableTape.tF ⟨((List.range ts.length).map fun i => [decide (axLen ts i = ℓ)]).reverse, []⟩) = σ₃ := by
    rw [upd_update tg_injective, upd_update tg_injective, upd_update tg_injective, upd_update tg_injective,
      upd_comp_self tg_injective]
    rfl
  rw [e3] at s3
  have s4 := runs_rewind' (a := 0) mRW σ₃ (L := (rowWords ts ℓ K).reverse) (R := []) (by tsimp [hσ₃])
  set σ₄ := Function.update σ₃ mRW ⟨[], (rowWords ts ℓ K).reverse.reverse ++ []⟩ with hσ₄
  have s5 := runs_rewind' (a := 0) mTP σ₄ (L := (topsW ts ℓ K).reverse) (R := []) (by tsimp [hσ₄, hσ₃])
  set σ₅ := Function.update σ₄ mTP ⟨[], (topsW ts ℓ K).reverse.reverse ++ []⟩ with hσ₅
  have s6 := runs_rewind' (a := 0) mFL σ₅ (L := (flagsW ts ℓ).reverse) (R := []) (by tsimp [hσ₅, hσ₄, hσ₃])
  set σ₆ := Function.update σ₅ mFL ⟨[], (flagsW ts ℓ).reverse.reverse ++ []⟩ with hσ₆
  have s7 := runs_clear' (a := 0) mFull σ₆ (T := ⟨[], List.replicate (ones (ℓ - 1)).length []⟩)
    (by tsimp [hσ₆, hσ₅, hσ₄, hσ₃, hσ₂, hσ₁])
  set σ₇ := Function.update σ₆ mFull emp with hσ₇
  have s8 := runs_clear' (a := 0) mW0 σ₇ (T := ⟨[ones 4], []⟩) (by tsimp [hσ₇, hσ₆, hσ₅, hσ₄, hσ₃, hσ₂])
  set σ₈ := Function.update σ₇ mW0 emp with hσ₈
  have hW := tableWords_le hL (h := ℓ - 1)
  have s9 := runs_emitTab (a := 0) (show mTab ≠ mJ by decide) (show mKC ≠ mCnt by decide)
    (show mCnt ≠ mO by decide) (show mTab ≠ mO by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (Nat.log 2 ts.prod + 4 * 2 ^ ℓ) σ₈ T acc
    (by tsimp [hσ₈, hσ₇, hσ₆, hσ₅, hσ₄, hσ₃])
    (by tsimp [hσ₈, hσ₇, hσ₆, hσ₅, hσ₄, hσ₃, hσ₂, hσ₁, hσ, mst, mconst])
    (by tsimp [hσ₈, hσ₇, hσ₆, hσ₅, hσ₄, hσ₃, hσ₂, hσ₁, hσ, mst, mconst])
    (by tsimp [hσ₈, hσ₇, hσ₆, hσ₅, hσ₄, hσ₃, hσ₂, hσ₁, hσ, mst, mconst])
    (by tsimp [hσ₈, hσ₇, hσ₆, hσ₅, hσ₄, hσ₃, hσ₂, hσ₁, hσ, mst, mconst])
    hW
  have hslot : slotAxes ts (ℓ - 1) = longs ts ℓ := by
    unfold slotAxes longs
    apply List.filter_congr
    intro i hi
    have := hL.2.1 i (List.mem_range.mp hi)
    simp only [decide_eq_decide]
    omega
  have hlenT : T.length = 3 * ((longs ts ℓ).length * (ℓ - 1)) := by
    rw [hT, length_tableWords, hslot]
  refine (Runs.then s1 (Runs.then s2 (Runs.then s3 (Runs.then s4 (Runs.then s5 (Runs.then s6 (Runs.then s7
    (Runs.then s8 s9)))))))).mono (fun σ' e => ?_) ?_
  · rw [e]
    have htw : (twistWords (paperPerm hL) (2 ^ ℓ) ts (ℓ - 1)).reverse ++ acc = T.reverse ++ ones T.length :: acc := by
      simp [twistWords, hT]
    rw [htw]
    funext i
    fin_cases i <;> first | rfl | tsimp [hσ₈, hσ₇, hσ₆, hσ₅, hσ₄, hσ₃, hσ₂, hσ₁, hσ, mst, mconst, emp]
  · rw [hlenT]
    simp only [twTopCost, length_ones, clen, WTape.words, reg, List.reverse_nil, List.nil_append, List.map_cons,
      List.map_nil, List.sum_cons, List.sum_nil, List.length_replicate, List.map_replicate, List.sum_replicate,
      List.length_nil, smul_eq_mul, ones, List.reverse_reverse, List.append_nil, List.length_reverse,
      List.map_reverse, List.sum_reverse, List.length_append, List.length_cons]
    omega

/-! ### The Hadamard words -/

/-- Append `ones (2^e)` for the register `s = ones e` to the script. -/
noncomputable def powOut (s : Fin 37) (h : s ≠ mPK) (h' : s ≠ mPW) : Cmd 0 37 :=
  .seq (pow2 s mPK mPW mPC mJ h (by decide) (by decide)) <| .seq (rewind mPW) <| .seq (cpy mPW mO (by decide))
    (clear mPW)

theorem runs_powOut {s : Fin 37} (h : s ≠ mPK) (h' : s ≠ mPW) (hsc : s ≠ mPC) (hsj : s ≠ mJ) (hso : s ≠ mO)
    (σ : Fin 37 → WTape) {e : ℕ} {acc : List (List Bool)} (hs : σ s = reg (ones e)) (hk : σ mPK = emp)
    (hw : σ mPW = emp) (hc : σ mPC = emp) (hj : σ mJ = emp) (ho : σ mO = ⟨acc, []⟩) :
    Runs (powOut s h h') σ (· = Function.update σ mO ⟨ones (2 ^ e) :: acc, []⟩)
      (e * (8 * 2 ^ e + 50) + 6 * e + 30 + 1 + (2 ^ e + 3 + 1 + (2 ^ e + 6 + 1 + (2 * (2 ^ e + 1) + 2)))) := by
  have s1 := runs_pow2 (a := 0) h (show mPW ≠ mPC by decide) (show mPK ≠ mJ by decide) (by decide) (by decide)
    (by decide) (by decide) h' hsc σ hs hk hw hc (by rw [hj]; rfl)
  set σ₁ := Function.update σ mPW ⟨[ones (2 ^ e)], []⟩ with hσ₁
  have s2 := runs_rewind' (a := 0) mPW σ₁ (L := [ones (2 ^ e)]) (R := []) (by simp [hσ₁])
  set σ₂ := Function.update σ₁ mPW (reg (ones (2 ^ e))) with hσ₂
  have e2 : Function.update σ₁ mPW ⟨[], [ones (2 ^ e)].reverse ++ []⟩ = σ₂ := by simp [hσ₂, reg]
  rw [e2] at s2
  have s3 := runs_cpy (a := 0) (show mPW ≠ mO by decide) σ₂ (by simp [hσ₂, reg])
    (by simp [hσ₂, hσ₁, ho, show mO ≠ mPW by decide])
  set σ₃ := Function.update (Function.update σ₂ mPW ⟨[ones (2 ^ e)], []⟩) mO ⟨ones (2 ^ e) :: acc, []⟩ with hσ₃
  have e3 : Function.update (Function.update σ₂ mPW (σ₂ mPW).next) mO ((σ₂ mO).put false [(σ₂ mPW).cur]) = σ₃ := by
    simp [hσ₃, hσ₂, hσ₁, ho, show mO ≠ mPW by decide, reg]
  rw [e3] at s3
  have s4 := runs_clear' (a := 0) mPW σ₃ (T := ⟨[ones (2 ^ e)], []⟩) (by simp [hσ₃, show mPW ≠ mO by decide])
  refine (Runs.then s1 (Runs.then s2 (Runs.then s3 s4))).mono (fun σ' e' => ?_) ?_
  · rw [e']
    funext z
    by_cases hzw : z = mPW
    · subst hzw; simp [hw, show mPW ≠ mO by decide]
    · by_cases hzo : z = mO
      · subst hzo; simp [hσ₃, hzw]
      · simp [hσ₃, hσ₂, hσ₁, hzw, hzo]
  · simp [hσ₂, reg, clen, WTape.words, time_copy]

/-- The top slot's Hadamard words: `[false]`, `ones (2r·2^topBase)`, `ones L`. -/
noncomputable def hadTop : Cmd 0 37 :=
  .seq (emit [[false]] mO) <| .seq (powOut mET (by decide) (by decide)) (ScriptOps.cpyReg mLL mO (by decide))

/-- The prefix slot's Hadamard words: `[false]`, `ones (2r·2^prefixBase)`, `ones D`. -/
noncomputable def hadPre : Cmd 0 37 :=
  .seq (emit [[false]] mO) <| .seq (regDup mE0 mEX (by decide)) <| .seq (skp mEX mJ (by decide)) <|
  .seq (appendReg mHDD mEX (by decide)) <| .seq (rewind mEX) <| .seq (powOut mEX (by decide) (by decide)) <|
  .seq (clear mEX) (ScriptOps.cpyReg mN mO (by decide))

/-- A chunk-group slot's Hadamard words, forward: `[true]`, then the header before the head. -/
noncomputable def hadChF : Cmd 0 37 := .seq (emit [[true]] mO) (readBack mHD mO (by decide))

/-- A chunk-group slot's Hadamard words, opposite: `[true]`, then the header under the head. -/
noncomputable def hadChO : Cmd 0 37 := .seq (emit [[true]] mO) (cpy mHD mO (by decide))

end ScriptMain

end IntegerMultBounds.Schoenhage
