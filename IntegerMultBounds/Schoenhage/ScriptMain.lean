module

public import IntegerMultBounds.Schoenhage.TapeBank
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
    upd τ f (Function.update σ i v) = Function.update (upd τ f σ) (f i) v :=
  TapeBank.place_update hf τ σ i v

theorem upd_comp_self {s n : ℕ} {f : Fin s → Fin n} (hf : Function.Injective f) (τ : Fin n → WTape) :
    upd τ f (τ ∘ f) = τ :=
  TapeBank.place_self hf τ

theorem runs_lift {s n : ℕ} (f : Fin s → Fin n) (hf : Function.Injective f) {c : Cmd 0 s} {τ : Fin n → WTape}
    {σ₁ : Fin s → WTape} {B : ℕ} (h : Runs c (τ ∘ f) (· = σ₁) B) : Runs (c.map f hf) τ (· = upd τ f σ₁) B :=
  TapeBank.runs_place f hf h

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

/-! ### Slot states -/

theorem mst_update_O (ℓ K : ℕ) (ts : List ℕ) (hd o tt : WTape) (h : ℕ) (o' : WTape) :
    Function.update (mst ℓ K ts hd o tt h) mO o' = mst ℓ K ts hd o' tt h := by
  funext i; fin_cases i <;> tsimp [mst]

theorem mst_update_HD (ℓ K : ℕ) (ts : List ℕ) (hd o tt : WTape) (h : ℕ) (hd' : WTape) :
    Function.update (mst ℓ K ts hd o tt h) mHD hd' = mst ℓ K ts hd' o tt h := by
  funext i; fin_cases i <;> tsimp [mst]

theorem mst_update_T (ℓ K : ℕ) (ts : List ℕ) (hd o tt : WTape) (h : ℕ) (tt' : WTape) :
    Function.update (mst ℓ K ts hd o tt h) mT tt' = mst ℓ K ts hd o tt' h := by
  funext i; fin_cases i <;> tsimp [mst]

@[simp] theorem mst_O (ℓ K : ℕ) (ts : List ℕ) (hd o tt : WTape) (h : ℕ) : mst ℓ K ts hd o tt h mO = o := by
  tsimp [mst]

@[simp] theorem mst_HD (ℓ K : ℕ) (ts : List ℕ) (hd o tt : WTape) (h : ℕ) : mst ℓ K ts hd o tt h mHD = hd := by
  tsimp [mst]

@[simp] theorem mst_T (ℓ K : ℕ) (ts : List ℕ) (hd o tt : WTape) (h : ℕ) : mst ℓ K ts hd o tt h mT = tt := by
  tsimp [mst]

theorem runs_emitO (ℓ K : ℕ) (ts : List ℕ) (hd tt : WTape) (h : ℕ) (acc ws : List (List Bool)) :
    Runs (a := 0) (emit ws mO) (mst ℓ K ts hd ⟨acc, []⟩ tt h)
      (· = mst ℓ K ts hd ⟨ws.reverse ++ acc, []⟩ tt h) (clen ws) := by
  have := runs_emit (a := 0) ws mO (mst ℓ K ts hd ⟨acc, []⟩ tt h) (by simp)
  rw [mst_O, mst_update_O] at this
  exact this

theorem runs_cpyRegO {r : Fin 37} (hr : r ≠ mO) (ℓ K : ℕ) (ts : List ℕ) (hd tt : WTape) (h : ℕ)
    (acc : List (List Bool)) {u : List Bool} (hu : mst ℓ K ts hd ⟨acc, []⟩ tt h r = reg u) :
    Runs (a := 0) (ScriptOps.cpyReg r mO hr) (mst ℓ K ts hd ⟨acc, []⟩ tt h)
      (· = mst ℓ K ts hd ⟨u :: acc, []⟩ tt h) (2 * u.length + 10) := by
  have := ScriptOps.runs_cpyReg (a := 0) hr (mst ℓ K ts hd ⟨acc, []⟩ tt h) (M := acc) hu (by simp)
  rw [mst_update_O] at this
  exact this

/-! ### The Hadamard words of each kind -/

/-- The cost of `powOut`. -/
def powOutCost (e : ℕ) : ℕ :=
  e * (8 * 2 ^ e + 50) + 6 * e + 30 + 1 + (2 ^ e + 3 + 1 + (2 ^ e + 6 + 1 + (2 * (2 ^ e + 1) + 2)))

/-- The top slot's exponent `ℓ + 1 + topBase`. -/
def topExp (ℓ K : ℕ) (ts : List ℕ) : ℕ := ℓ + 1 + (ℓ - 1) / K * (ts.length * K) + (ℓ - 1) % K * ts.length

theorem runs_hadTop (ℓ K : ℕ) (ts : List ℕ) (hd tt : WTape) (h : ℕ) (acc : List (List Bool)) :
    Runs hadTop (mst ℓ K ts hd ⟨acc, []⟩ tt h)
      (· = mst ℓ K ts hd ⟨ones (longs ts ℓ).length :: ones (2 ^ topExp ℓ K ts) :: [false] :: acc, []⟩ tt h)
      (clen [[false]] + 1 + (powOutCost (topExp ℓ K ts) + 1 + (2 * (longs ts ℓ).length + 10))) := by
  have s1 := runs_emitO ℓ K ts hd tt h acc [[false]]
  have s2 := runs_powOut (show mET ≠ mPK by decide) (show mET ≠ mPW by decide) (by decide) (by decide)
    (by decide) (mst ℓ K ts hd ⟨[[false]].reverse ++ acc, []⟩ tt h) (e := topExp ℓ K ts)
    (acc := [[false]].reverse ++ acc) (by tsimp [mst, mconst, topExp])
    (by tsimp [mst, mconst]) (by tsimp [mst, mconst]) (by tsimp [mst, mconst])
    (by tsimp [mst, mconst]) (by simp)
  rw [mst_update_O] at s2
  have s3 := runs_cpyRegO (show mLL ≠ mO by decide) ℓ K ts hd tt h (ones (2 ^ topExp ℓ K ts) ::
    [[false]].reverse ++ acc) (u := ones (longs ts ℓ).length) (by tsimp [mst, mconst])
  exact (Runs.then s1 (Runs.then s2 s3)).mono (fun σ' e => by rw [e]; rfl) (by simp [powOutCost])

/-- The prefix exponent of slot `h`: `ℓ + 1 + prefixBase`. -/
def preExp (ℓ K : ℕ) (ts : List ℕ) (h : ℕ) : ℕ := ℓ + 1 + (ℓ - 1) / K * (ts.length * K) + h * ts.length

/-- A bound on the prefix slot's Hadamard words. -/
def hadPreCost (ℓ K : ℕ) (ts : List ℕ) (h : ℕ) : ℕ :=
  8 * preExp ℓ K ts h + powOutCost (preExp ℓ K ts h) + 2 * ts.length + 100

set_option maxHeartbeats 16000000 in
theorem runs_hadPre (ℓ K : ℕ) (ts : List ℕ) (hd tt : WTape) (h : ℕ) (acc : List (List Bool)) :
    Runs hadPre (mst ℓ K ts hd ⟨acc, []⟩ tt h)
      (· = mst ℓ K ts hd ⟨ones ts.length :: ones (2 ^ preExp ℓ K ts h) :: [false] :: acc, []⟩ tt h)
      (hadPreCost ℓ K ts h) := by
  obtain ⟨E0, hE0⟩ : ∃ E0, E0 = ℓ + 1 + (ℓ - 1) / K * (ts.length * K) := ⟨_, rfl⟩
  have s1 := runs_emitO ℓ K ts hd tt h acc [[false]]
  set σ₁ := mst ℓ K ts hd ⟨[[false]].reverse ++ acc, []⟩ tt h with hσ₁
  have s2 := runs_regDup (a := 0) (show mE0 ≠ mEX by decide) σ₁ (w := ones E0) (by tsimp [hσ₁, mst, mconst, hE0])
    (by tsimp [hσ₁, mst, mconst])
  set σ₂ := Function.update σ₁ mEX (reg (ones E0)) with hσ₂
  have s3 := runs_skp (a := 0) (show mEX ≠ mJ by decide) σ₂ (by tsimp [hσ₂, reg]) (by tsimp [hσ₂, hσ₁, mst, mconst])
  set σ₃ := Function.update σ₂ mEX ⟨[ones E0], []⟩ with hσ₃
  have e3 : Function.update σ₂ mEX (σ₂ mEX).next = σ₃ := by tsimp [hσ₃, hσ₂, reg]
  rw [e3] at s3
  have s4 := runs_appendReg (a := 0) (show mHDD ≠ mEX by decide) σ₃ (u := ones (h * ts.length)) (v := ones E0)
    (M := []) (by tsimp [hσ₃, hσ₂, hσ₁, mst]) (by tsimp [hσ₃])
  set σ₄ := Function.update σ₃ mEX ⟨[ones (preExp ℓ K ts h)], []⟩ with hσ₄
  have e4 : Function.update σ₃ mEX ⟨(ones E0 ++ ones (h * ts.length)) :: [], []⟩ = σ₄ := by
    rw [hσ₄, ones_append_ones, hE0]; rfl
  rw [e4] at s4
  have s5 := runs_rewind' (a := 0) mEX σ₄ (L := [ones (preExp ℓ K ts h)]) (R := []) (by tsimp [hσ₄])
  set σ₅ := Function.update σ₄ mEX (reg (ones (preExp ℓ K ts h))) with hσ₅
  have e5 : Function.update σ₄ mEX ⟨[], [ones (preExp ℓ K ts h)].reverse ++ []⟩ = σ₅ := by tsimp [hσ₅, reg]
  rw [e5] at s5
  have s6 := runs_powOut (show mEX ≠ mPK by decide) (show mEX ≠ mPW by decide) (by decide) (by decide)
    (by decide) σ₅ (e := preExp ℓ K ts h) (acc := [[false]].reverse ++ acc) (by tsimp [hσ₅])
    (by tsimp [hσ₅, hσ₄, hσ₃, hσ₂, hσ₁, mst, mconst]) (by tsimp [hσ₅, hσ₄, hσ₃, hσ₂, hσ₁, mst, mconst])
    (by tsimp [hσ₅, hσ₄, hσ₃, hσ₂, hσ₁, mst, mconst]) (by tsimp [hσ₅, hσ₄, hσ₃, hσ₂, hσ₁, mst, mconst])
    (by tsimp [hσ₅, hσ₄, hσ₃, hσ₂, hσ₁, mst])
  set σ₆ := Function.update σ₅ mO ⟨ones (2 ^ preExp ℓ K ts h) :: [[false]].reverse ++ acc, []⟩ with hσ₆
  have s7 := runs_clear' (a := 0) mEX σ₆ (T := reg (ones (preExp ℓ K ts h))) (by tsimp [hσ₆, hσ₅])
  set σ₇ := mst ℓ K ts hd ⟨ones (2 ^ preExp ℓ K ts h) :: [[false]].reverse ++ acc, []⟩ tt h with hσ₇
  have e7 : Function.update σ₆ mEX emp = σ₇ := by
    funext i; fin_cases i <;> tsimp [hσ₇, hσ₆, hσ₅, hσ₄, hσ₃, hσ₂, hσ₁, mst, mconst, emp]
  rw [e7] at s7
  have s8 := runs_cpyRegO (show mN ≠ mO by decide) ℓ K ts hd tt h (ones (2 ^ preExp ℓ K ts h) ::
    [[false]].reverse ++ acc) (u := ones ts.length) (by tsimp [mst, mconst])
  refine (Runs.then s1 (Runs.then s2 (Runs.then s3 (Runs.then s4 (Runs.then s5 (Runs.then s6 (Runs.then s7
    s8))))))).mono (fun σ' e => by rw [e]; rfl) ?_
  have hpe : preExp ℓ K ts h = E0 + h * ts.length := by rw [hE0]; rfl
  have hc : (σ₂ mEX).cur.length = E0 := by tsimp [hσ₂, reg]
  simp only [hadPreCost, clen, WTape.words, reg, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    length_ones, List.length_cons, List.length_nil, List.reverse_nil, List.nil_append, List.reverse_cons,
    List.append_nil]
  unfold powOutCost
  omega

theorem runs_hadChF (ℓ K : ℕ) (ts : List ℕ) (tt : WTape) (h : ℕ) (acc L R : List (List Bool)) (w : List Bool) :
    Runs hadChF (mst ℓ K ts ⟨w :: L, R⟩ ⟨acc, []⟩ tt h)
      (· = mst ℓ K ts ⟨L, w :: R⟩ ⟨w :: [true] :: acc, []⟩ tt h) (clen [[true]] + 1 + (3 * w.length + 15)) := by
  have s1 := runs_emitO ℓ K ts ⟨w :: L, R⟩ tt h acc [[true]]
  have s2 := runs_readBack (a := 0) (show mHD ≠ mO by decide)
    (mst ℓ K ts ⟨w :: L, R⟩ ⟨[[true]].reverse ++ acc, []⟩ tt h) (w := w) (L := L) (R := R)
    (M := [[true]].reverse ++ acc) (by simp) (by simp)
  rw [mst_update_HD, mst_update_O] at s2
  exact (Runs.then s1 s2).mono (fun σ' e => by rw [e]; rfl) le_rfl

theorem runs_hadChO (ℓ K : ℕ) (ts : List ℕ) (tt : WTape) (h : ℕ) (acc L R : List (List Bool)) (w : List Bool) :
    Runs hadChO (mst ℓ K ts ⟨L, w :: R⟩ ⟨acc, []⟩ tt h)
      (· = mst ℓ K ts ⟨w :: L, R⟩ ⟨w :: [true] :: acc, []⟩ tt h) (clen [[true]] + 1 + (w.length + 6)) := by
  have s1 := runs_emitO ℓ K ts ⟨L, w :: R⟩ tt h acc [[true]]
  have s2 := runs_cpy (a := 0) (show mHD ≠ mO by decide) (mst ℓ K ts ⟨L, w :: R⟩ ⟨[[true]].reverse ++ acc, []⟩ tt h)
    (by simp) (by simp)
  simp only [mst_HD, mst_O, WTape.next_mk, WTape.cur_mk, List.headD_cons, List.tail_cons, WTape.put_false]
    at s2
  rw [mst_update_HD, mst_update_O] at s2
  exact (Runs.then s1 s2).mono (fun σ' e => by rw [e]; rfl) le_rfl

/-! ### The slot counter -/

/-- Forward: lower `h` and `h·D` by one slot. -/
noncomputable def decF : Cmd 0 37 :=
  .seq (dropReg mH mKC mTmp (by decide) (by decide) (by decide)) <| .seq (clear mH) <|
  .seq (regMove mTmp mH (by decide)) <| .seq (dropReg mHDD mN mTmp (by decide) (by decide) (by decide)) <|
  .seq (clear mHDD) (regMove mTmp mHDD (by decide))

/-- Opposite: raise `h` and `h·D` by one slot. -/
noncomputable def incO : Cmd 0 37 :=
  .seq (skp mH mJ (by decide)) <| .seq (appendReg mKC mH (by decide)) <| .seq (rewind mH) <|
  .seq (skp mHDD mJ (by decide)) <| .seq (appendReg mN mHDD (by decide)) (rewind mHDD)

/-- A bound on a counter step. -/
def decCost (D h : ℕ) : ℕ := 20 * h + 20 * D + 20 * (h * D) + 400

set_option maxHeartbeats 16000000 in
theorem runs_decF (ℓ K : ℕ) (ts : List ℕ) (hd o tt : WTape) (h : ℕ) :
    Runs decF (mst ℓ K ts hd o tt h) (· = mst ℓ K ts hd o tt (h - 1)) (decCost ts.length h) := by
  set σ := mst ℓ K ts hd o tt h with hσ
  have s1 := runs_dropReg (a := 0) (show mH ≠ mKC by decide) (show mH ≠ mTmp by decide)
    (show mKC ≠ mTmp by decide) σ (u := ones h) (v := [true]) (by tsimp [hσ, mst, mconst])
    (by tsimp [hσ, mst, mconst]) (by tsimp [hσ, mst, mconst])
  set σ₁ := Function.update σ mTmp (reg (ones (h - 1))) with hσ₁
  have e1 : Function.update σ mTmp (reg ((ones h).drop [true].length)) = σ₁ := by
    rw [hσ₁, List.length_singleton, drop_ones]
  rw [e1] at s1
  have s2 := runs_clear' (a := 0) mH σ₁ (T := reg (ones h)) (by tsimp [hσ₁, hσ, mst])
  set σ₂ := Function.update σ₁ mH emp with hσ₂
  have s3 := runs_regMove (a := 0) (show mTmp ≠ mH by decide) σ₂ (w := ones (h - 1)) (by tsimp [hσ₂, hσ₁])
    (by tsimp [hσ₂])
  set σ₃ := Function.update (Function.update σ₂ mTmp emp) mH (reg (ones (h - 1))) with hσ₃
  have s4 := runs_dropReg (a := 0) (show mHDD ≠ mN by decide) (show mHDD ≠ mTmp by decide)
    (show mN ≠ mTmp by decide) σ₃ (u := ones (h * ts.length)) (v := ones ts.length)
    (by tsimp [hσ₃, hσ₂, hσ₁, hσ, mst]) (by tsimp [hσ₃, hσ₂, hσ₁, hσ, mst, mconst]) (by tsimp [hσ₃])
  set σ₄ := Function.update σ₃ mTmp (reg (ones ((h - 1) * ts.length))) with hσ₄
  have e4 : Function.update σ₃ mTmp (reg ((ones (h * ts.length)).drop (ones ts.length).length)) = σ₄ := by
    rw [hσ₄, length_ones, drop_ones, Nat.sub_one_mul]
  rw [e4] at s4
  have s5 := runs_clear' (a := 0) mHDD σ₄ (T := reg (ones (h * ts.length))) (by tsimp [hσ₄, hσ₃, hσ₂, hσ₁, hσ, mst])
  set σ₅ := Function.update σ₄ mHDD emp with hσ₅
  have s6 := runs_regMove (a := 0) (show mTmp ≠ mHDD by decide) σ₅ (w := ones ((h - 1) * ts.length))
    (by tsimp [hσ₅, hσ₄]) (by tsimp [hσ₅])
  refine (Runs.then s1 (Runs.then s2 (Runs.then s3 (Runs.then s4 (Runs.then s5 s6))))).mono
    (fun σ' e => ?_) ?_
  · rw [e]
    funext i; fin_cases i <;> tsimp [hσ₅, hσ₄, hσ₃, hσ₂, hσ₁, hσ, mst, mconst, emp]
  · have h1 : (h - 1) * ts.length ≤ h * ts.length := Nat.mul_le_mul_right _ (by omega)
    have h2 : h - 1 ≤ h := by omega
    simp only [decCost, clen, WTape.words, reg, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      length_ones, List.length_cons, List.length_nil, List.reverse_nil, List.nil_append]
    omega

set_option maxHeartbeats 16000000 in
theorem runs_incO (ℓ K : ℕ) (ts : List ℕ) (hd o tt : WTape) (h : ℕ) :
    Runs incO (mst ℓ K ts hd o tt h) (· = mst ℓ K ts hd o tt (h + 1)) (decCost ts.length (h + 1)) := by
  set σ := mst ℓ K ts hd o tt h with hσ
  have s1 := runs_skp (a := 0) (show mH ≠ mJ by decide) σ (by tsimp [hσ, mst, reg]) (by tsimp [hσ, mst, mconst])
  set σ₁ := Function.update σ mH ⟨[ones h], []⟩ with hσ₁
  have e1 : Function.update σ mH (σ mH).next = σ₁ := by tsimp [hσ₁, hσ, mst, reg]
  rw [e1] at s1
  have s2 := runs_appendReg (a := 0) (show mKC ≠ mH by decide) σ₁ (u := [true]) (v := ones h) (M := [])
    (by tsimp [hσ₁, hσ, mst, mconst]) (by tsimp [hσ₁])
  set σ₂ := Function.update σ₁ mH ⟨[ones (h + 1)], []⟩ with hσ₂
  have e2 : Function.update σ₁ mH ⟨(ones h ++ [true]) :: [], []⟩ = σ₂ := by
    rw [hσ₂]; congr 3; simp [ones, List.replicate_succ']
  rw [e2] at s2
  have s3 := runs_rewind' (a := 0) mH σ₂ (L := [ones (h + 1)]) (R := []) (by tsimp [hσ₂])
  set σ₃ := Function.update σ₂ mH (reg (ones (h + 1))) with hσ₃
  have e3 : Function.update σ₂ mH ⟨[], [ones (h + 1)].reverse ++ []⟩ = σ₃ := by tsimp [hσ₃, reg]
  rw [e3] at s3
  have s4 := runs_skp (a := 0) (show mHDD ≠ mJ by decide) σ₃ (by tsimp [hσ₃, hσ₂, hσ₁, hσ, mst, reg])
    (by tsimp [hσ₃, hσ₂, hσ₁, hσ, mst, mconst])
  set σ₄ := Function.update σ₃ mHDD ⟨[ones (h * ts.length)], []⟩ with hσ₄
  have e4 : Function.update σ₃ mHDD (σ₃ mHDD).next = σ₄ := by tsimp [hσ₄, hσ₃, hσ₂, hσ₁, hσ, mst, reg]
  rw [e4] at s4
  have s5 := runs_appendReg (a := 0) (show mN ≠ mHDD by decide) σ₄ (u := ones ts.length) (v := ones (h * ts.length))
    (M := []) (by tsimp [hσ₄, hσ₃, hσ₂, hσ₁, hσ, mst, mconst]) (by tsimp [hσ₄])
  set σ₅ := Function.update σ₄ mHDD ⟨[ones ((h + 1) * ts.length)], []⟩ with hσ₅
  have e5 : Function.update σ₄ mHDD ⟨(ones (h * ts.length) ++ ones ts.length) :: [], []⟩ = σ₅ := by
    rw [hσ₅, ones_append_ones, Nat.succ_mul]
  rw [e5] at s5
  have s6 := runs_rewind' (a := 0) mHDD σ₅ (L := [ones ((h + 1) * ts.length)]) (R := []) (by tsimp [hσ₅])
  refine (Runs.then s1 (Runs.then s2 (Runs.then s3 (Runs.then s4 (Runs.then s5 s6))))).mono
    (fun σ' e => ?_) ?_
  · rw [e]
    funext i; fin_cases i <;> tsimp [hσ₅, hσ₄, hσ₃, hσ₂, hσ₁, hσ, mst, mconst, reg]
  · have hc1 : (σ mH).cur.length = h := by tsimp [hσ, mst, reg]
    have hc2 : (σ₃ mHDD).cur.length = h * ts.length := by tsimp [hσ₃, hσ₂, hσ₁, hσ, mst, reg]
    rw [hc1, hc2]
    simp only [decCost, clen, WTape.words, reg, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      length_ones, List.length_cons, List.length_nil, List.reverse_nil, List.nil_append, Nat.succ_mul]
    omega

/-! ### Slot bodies -/

/-- One forward slot: test top, then prefix or chunk; Hadamard words, then twist words. -/
noncomputable def bodyF : Cmd 0 37 :=
  .seq (geqReg mM1 mH mF1 (by decide) (by decide) (by decide)) <|
  .cond mF1
    (.seq (clear mF1) <| .seq (geqReg mB mH mF2 (by decide) (by decide) (by decide)) <|
      .cond mF2 (.seq (clear mF2) (.seq hadPre twSlot)) (.seq (clear mF2) (.seq hadChF twSlot)))
    (.seq (clear mF1) (.seq hadTop twTop))

/-- One opposite slot: twist words, then Hadamard words. -/
noncomputable def bodyO : Cmd 0 37 :=
  .seq (geqReg mM1 mH mF1 (by decide) (by decide) (by decide)) <|
  .cond mF1
    (.seq (clear mF1) <| .seq (geqReg mB mH mF2 (by decide) (by decide) (by decide)) <|
      .cond mF2 (.seq (clear mF2) (.seq twSlot hadPre)) (.seq (clear mF2) (.seq twSlot hadChO)))
    (.seq (clear mF1) (.seq twTop hadTop))

theorem update_back {t : ℕ} (σ : Fin t → WTape) (i : Fin t) (v : WTape) (hi : σ i = emp) :
    Function.update (Function.update σ i v) i emp = σ := by
  rw [Function.update_idem, ← hi, Function.update_eq_self]

/-- The paper's Hadamard words of the top slot. -/
theorem hadWords_top (p d w : ℕ) {ℓ K : ℕ} (ts : List ℕ) (hℓ : 1 ≤ ℓ) :
    hadWords p d (2 ^ ℓ) w (Nat.log 2 ts.prod) ts ℓ K (ℓ - 1) =
      [[false], ones (2 ^ topExp ℓ K ts), ones (longs ts ℓ).length] := by
  have h1 : ¬ ℓ - 1 < (ℓ - 1) % K := Nat.not_lt.mpr (Nat.mod_le _ _)
  simp only [hadWords, h1, lt_irrefl, ↓reduceIte, if_false]
  congr 2
  unfold topExp topBase
  rw [show 2 * 2 ^ ℓ * 2 ^ (ts.length * ((ℓ - 1) / K) * K + ts.length * ((ℓ - 1) % K)) =
    2 ^ (ℓ + 1 + (ts.length * ((ℓ - 1) / K) * K + ts.length * ((ℓ - 1) % K))) by
      simp only [pow_add, pow_one]; ring]
  congr 1; ring

/-- The paper's Hadamard words of a prefix slot. -/
theorem hadWords_pre (p d w : ℕ) {ℓ K : ℕ} (ts : List ℕ) {h : ℕ} (hh : h < (ℓ - 1) % K) :
    hadWords p d (2 ^ ℓ) w (Nat.log 2 ts.prod) ts ℓ K h =
      [[false], ones (2 ^ preExp ℓ K ts h), ones ts.length] := by
  simp only [hadWords, hh, ↓reduceIte]
  congr 2
  unfold preExp prefixBase
  rw [show 2 * 2 ^ ℓ * 2 ^ (ts.length * ((ℓ - 1) / K) * K + h * ts.length) =
    2 ^ (ℓ + 1 + (ts.length * ((ℓ - 1) / K) * K + h * ts.length)) by
      simp only [pow_add, pow_one]; ring]
  congr 1; ring

/-- The paper's Hadamard words of a chunk-group slot. -/
theorem hadWords_ch (p d w : ℕ) {ℓ K : ℕ} (ts : List ℕ) {h : ℕ} (hb : (ℓ - 1) % K ≤ h) (ht : h < ℓ - 1) :
    hadWords p d (2 ^ ℓ) w (Nat.log 2 ts.prod) ts ℓ K h =
      [[true], chunkHdr p d (2 ^ ℓ) w (Nat.log 2 ts.prod) ts ℓ K h] := by
  simp only [hadWords, Nat.not_lt.mpr hb, ht, ↓reduceIte]

/-- A bound on one slot body, for every kind; the prefix words are counted only for prefix slots. -/
def bodyCost (ℓ K : ℕ) (ts : List ℕ) (h : ℕ) (hdLen : ℕ) : ℕ :=
  2 * (ℓ - 1) + 2 * h + 30 + 1 + (2 * (longs ts ℓ).length + 2 * (ℓ - 1) + 2 * h + 200 +
    (clen [[false]] + 1 + (powOutCost (topExp ℓ K ts) + 1 + (2 * (longs ts ℓ).length + 10))) + twTopCost ℓ K ts +
    hadPreCost ℓ K ts (min h ((ℓ - 1) % K)) + (clen [[true]] + 1 + (3 * hdLen + 15)) + twCost ℓ K ts h)

set_option maxHeartbeats 32000000 in
/-- `runs_bodyF`: a forward slot appends its Hadamard and twist words; a chunk-group slot reads its
header from before the head of the header tape. -/
theorem runs_bodyF (p d w : ℕ) {ℓ K : ℕ} {ts : List ℕ} (hL : LayoutOK (2 ^ ℓ) ts ℓ K) {h : ℕ} (hh : h < ℓ)
    (tt : WTape) (acc : List (List Bool)) (hd hd' : WTape) (hdLen : ℕ)
    (hHD : if (ℓ - 1) % K ≤ h ∧ h < ℓ - 1 then ∃ L R, hd = ⟨chunkHdr p d (2 ^ ℓ) w (Nat.log 2 ts.prod) ts ℓ K h :: L, R⟩ ∧
      hd' = ⟨L, chunkHdr p d (2 ^ ℓ) w (Nat.log 2 ts.prod) ts ℓ K h :: R⟩ ∧
      (chunkHdr p d (2 ^ ℓ) w (Nat.log 2 ts.prod) ts ℓ K h).length ≤ hdLen else hd' = hd) :
    Runs bodyF (mst ℓ K ts hd ⟨acc, []⟩ tt h)
      (· = mst ℓ K ts hd' ⟨(hadWords p d (2 ^ ℓ) w (Nat.log 2 ts.prod) ts ℓ K h ++
        twistWords (paperPerm hL) (2 ^ ℓ) ts h).reverse ++ acc, []⟩ tt h) (bodyCost ℓ K ts h hdLen) := by
  have hℓ : 1 ≤ ℓ := hL.2.2.2
  have hmod := Nat.mod_le (ℓ - 1) K
  set σ := mst ℓ K ts hd ⟨acc, []⟩ tt h with hσ
  have s1 := runs_geqReg (show mM1 ≠ mH by decide) (show mM1 ≠ mF1 by decide) (show mH ≠ mF1 by decide) σ
    (x := ℓ - 1) (y := h) (by tsimp [hσ, mst, mconst]) (by tsimp [hσ, mst, mconst]) (by tsimp [hσ, mst, mconst])
  set σ₁ := Function.update σ mF1 (reg [decide (h < ℓ - 1)]) with hσ₁
  have hF1 : σ mF1 = emp := by tsimp [hσ, mst, mconst]
  have hF2 : σ mF2 = emp := by tsimp [hσ, mst, mconst]
  have cl1 : Runs (a := 0) (clear mF1) σ₁ (· = σ) (2 * clen [[decide (h < ℓ - 1)]] + 2) :=
    (runs_clear' (a := 0) mF1 σ₁ (T := reg [decide (h < ℓ - 1)]) (by tsimp [hσ₁])).mono
      (fun σ' e => by rw [e, hσ₁, update_back σ mF1 _ hF1]) le_rfl
  by_cases htop : h < ℓ - 1
  · -- below the top
    have s2 := runs_geqReg (show mB ≠ mH by decide) (show mB ≠ mF2 by decide) (show mH ≠ mF2 by decide) σ
      (x := (ℓ - 1) % K) (y := h) (by tsimp [hσ, mst, mconst]) (by tsimp [hσ, mst, mconst]) hF2
    set σ₂ := Function.update σ mF2 (reg [decide (h < (ℓ - 1) % K)]) with hσ₂
    have cl2 : Runs (a := 0) (clear mF2) σ₂ (· = σ) (2 * clen [[decide (h < (ℓ - 1) % K)]] + 2) :=
      (runs_clear' (a := 0) mF2 σ₂ (T := reg [decide (h < (ℓ - 1) % K)]) (by tsimp [hσ₂])).mono
        (fun σ' e => by rw [e, hσ₂, update_back σ mF2 _ hF2]) le_rfl
    by_cases hpre : h < (ℓ - 1) % K
    · have hn : ¬ ((ℓ - 1) % K ≤ h ∧ h < ℓ - 1) := fun ⟨a, _⟩ => by omega
      simp only [hn, if_false] at hHD
      rw [hHD]
      have s3 := runs_hadPre ℓ K ts hd tt h acc
      have s4 := runs_twSlot hL htop hd tt (ones ts.length :: ones (2 ^ preExp ℓ K ts h) :: [false] :: acc)
      have sb := Runs.then cl2 (Runs.then s3 s4)
      have sc := Runs.cond_true (c := .seq (clear mF2) (.seq hadPre twSlot))
        (d := .seq (clear mF2) (.seq hadChF twSlot)) (i := mF2)
        (by rw [hσ₂, Function.update_self]; exact (startsOne_mk _ _ _ _).mpr (by simpa using hpre)) sb
      have sa := Runs.then cl1 (Runs.then s2 sc)
      have st := Runs.cond_true (c := .seq (clear mF1) (.seq (geqReg mB mH mF2 (by decide) (by decide) (by decide))
          (.cond mF2 (.seq (clear mF2) (.seq hadPre twSlot)) (.seq (clear mF2) (.seq hadChF twSlot)))))
        (d := .seq (clear mF1) (.seq hadTop twTop)) (i := mF1)
        (by rw [hσ₁, Function.update_self]; exact (startsOne_mk _ _ _ _).mpr (by simpa using htop)) sa
      refine (Runs.then s1 st).mono (fun σ' e => ?_) ?_
      · rw [e, hadWords_pre p d w ts hpre]
        congr 2
        simp [twistWords]
      · unfold bodyCost
        rw [Nat.min_eq_left hpre.le]
        simp only [clen, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
          List.length_nil]
        omega
    · have hc : (ℓ - 1) % K ≤ h ∧ h < ℓ - 1 := ⟨by omega, htop⟩
      simp only [hc, and_self, if_true] at hHD
      obtain ⟨L, R, rfl, rfl, hlen⟩ := hHD
      have s3 := runs_hadChF ℓ K ts tt h acc L R (chunkHdr p d (2 ^ ℓ) w (Nat.log 2 ts.prod) ts ℓ K h)
      have s4 := runs_twSlot hL htop ⟨L, chunkHdr p d (2 ^ ℓ) w (Nat.log 2 ts.prod) ts ℓ K h :: R⟩ tt
        (chunkHdr p d (2 ^ ℓ) w (Nat.log 2 ts.prod) ts ℓ K h :: [true] :: acc)
      have sb := Runs.then cl2 (Runs.then s3 s4)
      have sc := Runs.cond_false (c := .seq (clear mF2) (.seq hadPre twSlot))
        (d := .seq (clear mF2) (.seq hadChF twSlot)) (i := mF2)
        (by rw [hσ₂, Function.update_self]; intro hs; have := (startsOne_mk _ _ _ _).mp hs; simp at this; omega) sb
      have sa := Runs.then cl1 (Runs.then s2 sc)
      have st := Runs.cond_true (c := .seq (clear mF1) (.seq (geqReg mB mH mF2 (by decide) (by decide) (by decide))
          (.cond mF2 (.seq (clear mF2) (.seq hadPre twSlot)) (.seq (clear mF2) (.seq hadChF twSlot)))))
        (d := .seq (clear mF1) (.seq hadTop twTop)) (i := mF1)
        (by rw [hσ₁, Function.update_self]; exact (startsOne_mk _ _ _ _).mpr (by simpa using htop)) sa
      refine (Runs.then s1 st).mono (fun σ' e => ?_) ?_
      · rw [e, hadWords_ch p d w ts hc.1 hc.2]
        congr 2
        simp [twistWords]
      · unfold bodyCost
        simp only [clen, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
          List.length_nil]
        omega
  · -- the top slot
    have hht : h = ℓ - 1 := by omega
    have hn : ¬ ((ℓ - 1) % K ≤ h ∧ h < ℓ - 1) := fun ⟨_, b⟩ => htop b
    simp only [hn, if_false] at hHD
    rw [hHD]
    have s3 := runs_hadTop ℓ K ts hd tt h acc
    have s4 := runs_twTop hL hd tt h (ones (longs ts ℓ).length :: ones (2 ^ topExp ℓ K ts) :: [false] :: acc)
    have sa := Runs.then cl1 (Runs.then s3 s4)
    have st := Runs.cond_false (c := .seq (clear mF1) (.seq (geqReg mB mH mF2 (by decide) (by decide) (by decide))
        (.cond mF2 (.seq (clear mF2) (.seq hadPre twSlot)) (.seq (clear mF2) (.seq hadChF twSlot)))))
      (d := .seq (clear mF1) (.seq hadTop twTop)) (i := mF1)
      (by rw [hσ₁, Function.update_self]; intro hs; have := (startsOne_mk _ _ _ _).mp hs; simp at this; omega) sa
    refine (Runs.then s1 st).mono (fun σ' e => ?_) ?_
    · rw [e, hht, hadWords_top p d w ts hℓ]
      congr 2
      simp [twistWords]
    · unfold bodyCost
      simp only [clen, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
        List.length_nil]
      omega

set_option maxHeartbeats 32000000 in
/-- `runs_bodyO`: an opposite slot appends its twist and Hadamard words; a chunk-group slot reads its
header under the head of the header tape. -/
theorem runs_bodyO (p d w : ℕ) {ℓ K : ℕ} {ts : List ℕ} (hL : LayoutOK (2 ^ ℓ) ts ℓ K) {h : ℕ} (hh : h < ℓ)
    (tt : WTape) (acc : List (List Bool)) (hd hd' : WTape) (hdLen : ℕ)
    (hHD : if (ℓ - 1) % K ≤ h ∧ h < ℓ - 1 then ∃ L R, hd = ⟨L, chunkHdr p d (2 ^ ℓ) w (Nat.log 2 ts.prod) ts ℓ K h :: R⟩ ∧
      hd' = ⟨chunkHdr p d (2 ^ ℓ) w (Nat.log 2 ts.prod) ts ℓ K h :: L, R⟩ ∧
      (chunkHdr p d (2 ^ ℓ) w (Nat.log 2 ts.prod) ts ℓ K h).length ≤ hdLen else hd' = hd) :
    Runs bodyO (mst ℓ K ts hd ⟨acc, []⟩ tt h)
      (· = mst ℓ K ts hd' ⟨(twistWords (paperPerm hL) (2 ^ ℓ) ts h ++
        hadWords p d (2 ^ ℓ) w (Nat.log 2 ts.prod) ts ℓ K h).reverse ++ acc, []⟩ tt h) (bodyCost ℓ K ts h hdLen) := by
  have hℓ : 1 ≤ ℓ := hL.2.2.2
  have hmod := Nat.mod_le (ℓ - 1) K
  set σ := mst ℓ K ts hd ⟨acc, []⟩ tt h with hσ
  have s1 := runs_geqReg (show mM1 ≠ mH by decide) (show mM1 ≠ mF1 by decide) (show mH ≠ mF1 by decide) σ
    (x := ℓ - 1) (y := h) (by tsimp [hσ, mst, mconst]) (by tsimp [hσ, mst, mconst]) (by tsimp [hσ, mst, mconst])
  set σ₁ := Function.update σ mF1 (reg [decide (h < ℓ - 1)]) with hσ₁
  have hF1 : σ mF1 = emp := by tsimp [hσ, mst, mconst]
  have hF2 : σ mF2 = emp := by tsimp [hσ, mst, mconst]
  have cl1 : Runs (a := 0) (clear mF1) σ₁ (· = σ) (2 * clen [[decide (h < ℓ - 1)]] + 2) :=
    (runs_clear' (a := 0) mF1 σ₁ (T := reg [decide (h < ℓ - 1)]) (by tsimp [hσ₁])).mono
      (fun σ' e => by rw [e, hσ₁, update_back σ mF1 _ hF1]) le_rfl
  by_cases htop : h < ℓ - 1
  · -- below the top
    have s2 := runs_geqReg (show mB ≠ mH by decide) (show mB ≠ mF2 by decide) (show mH ≠ mF2 by decide) σ
      (x := (ℓ - 1) % K) (y := h) (by tsimp [hσ, mst, mconst]) (by tsimp [hσ, mst, mconst]) hF2
    set σ₂ := Function.update σ mF2 (reg [decide (h < (ℓ - 1) % K)]) with hσ₂
    have cl2 : Runs (a := 0) (clear mF2) σ₂ (· = σ) (2 * clen [[decide (h < (ℓ - 1) % K)]] + 2) :=
      (runs_clear' (a := 0) mF2 σ₂ (T := reg [decide (h < (ℓ - 1) % K)]) (by tsimp [hσ₂])).mono
        (fun σ' e => by rw [e, hσ₂, update_back σ mF2 _ hF2]) le_rfl
    by_cases hpre : h < (ℓ - 1) % K
    · have hn : ¬ ((ℓ - 1) % K ≤ h ∧ h < ℓ - 1) := fun ⟨a, _⟩ => by omega
      simp only [hn, if_false] at hHD
      rw [hHD]
      have s3 := runs_twSlot hL htop hd tt acc
      have s4 := runs_hadPre ℓ K ts hd tt h ((twistWords (paperPerm hL) (2 ^ ℓ) ts h).reverse ++ acc)
      have sb := Runs.then cl2 (Runs.then s3 s4)
      have sc := Runs.cond_true (c := .seq (clear mF2) (.seq twSlot hadPre))
        (d := .seq (clear mF2) (.seq twSlot hadChO)) (i := mF2)
        (by rw [hσ₂, Function.update_self]; exact (startsOne_mk _ _ _ _).mpr (by simpa using hpre)) sb
      have sa := Runs.then cl1 (Runs.then s2 sc)
      have st := Runs.cond_true (c := .seq (clear mF1) (.seq (geqReg mB mH mF2 (by decide) (by decide) (by decide))
          (.cond mF2 (.seq (clear mF2) (.seq twSlot hadPre)) (.seq (clear mF2) (.seq twSlot hadChO)))))
        (d := .seq (clear mF1) (.seq twTop hadTop)) (i := mF1)
        (by rw [hσ₁, Function.update_self]; exact (startsOne_mk _ _ _ _).mpr (by simpa using htop)) sa
      refine (Runs.then s1 st).mono (fun σ' e => ?_) ?_
      · rw [e, hadWords_pre p d w ts hpre]
        congr 2
        simp
      · unfold bodyCost
        rw [Nat.min_eq_left hpre.le]
        simp only [clen, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
          List.length_nil]
        omega
    · have hc : (ℓ - 1) % K ≤ h ∧ h < ℓ - 1 := ⟨by omega, htop⟩
      simp only [hc, and_self, if_true] at hHD
      obtain ⟨L, R, rfl, rfl, hlen⟩ := hHD
      have s3 := runs_twSlot hL htop ⟨L, chunkHdr p d (2 ^ ℓ) w (Nat.log 2 ts.prod) ts ℓ K h :: R⟩ tt acc
      have s4 := runs_hadChO ℓ K ts tt h ((twistWords (paperPerm hL) (2 ^ ℓ) ts h).reverse ++ acc) L R
        (chunkHdr p d (2 ^ ℓ) w (Nat.log 2 ts.prod) ts ℓ K h)
      have sb := Runs.then cl2 (Runs.then s3 s4)
      have sc := Runs.cond_false (c := .seq (clear mF2) (.seq twSlot hadPre))
        (d := .seq (clear mF2) (.seq twSlot hadChO)) (i := mF2)
        (by rw [hσ₂, Function.update_self]; intro hs; have := (startsOne_mk _ _ _ _).mp hs; simp at this; omega) sb
      have sa := Runs.then cl1 (Runs.then s2 sc)
      have st := Runs.cond_true (c := .seq (clear mF1) (.seq (geqReg mB mH mF2 (by decide) (by decide) (by decide))
          (.cond mF2 (.seq (clear mF2) (.seq twSlot hadPre)) (.seq (clear mF2) (.seq twSlot hadChO)))))
        (d := .seq (clear mF1) (.seq twTop hadTop)) (i := mF1)
        (by rw [hσ₁, Function.update_self]; exact (startsOne_mk _ _ _ _).mpr (by simpa using htop)) sa
      refine (Runs.then s1 st).mono (fun σ' e => ?_) ?_
      · rw [e, hadWords_ch p d w ts hc.1 hc.2]
        congr 2
        simp
      · unfold bodyCost
        simp only [clen, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
          List.length_nil]
        omega
  · -- the top slot
    have hht : h = ℓ - 1 := by omega
    have hn : ¬ ((ℓ - 1) % K ≤ h ∧ h < ℓ - 1) := fun ⟨_, b⟩ => htop b
    simp only [hn, if_false] at hHD
    rw [hHD]
    have s3 := runs_twTop hL hd tt h acc
    have s4 := runs_hadTop ℓ K ts hd tt h ((twistWords (paperPerm hL) (2 ^ ℓ) ts (ℓ - 1)).reverse ++ acc)
    have sa := Runs.then cl1 (Runs.then s3 s4)
    have st := Runs.cond_false (c := .seq (clear mF1) (.seq (geqReg mB mH mF2 (by decide) (by decide) (by decide))
        (.cond mF2 (.seq (clear mF2) (.seq twSlot hadPre)) (.seq (clear mF2) (.seq twSlot hadChO)))))
      (d := .seq (clear mF1) (.seq twTop hadTop)) (i := mF1)
      (by rw [hσ₁, Function.update_self]; intro hs; have := (startsOne_mk _ _ _ _).mp hs; simp at this; omega) sa
    refine (Runs.then s1 st).mono (fun σ' e => ?_) ?_
    · rw [e, hht, hadWords_top p d w ts hℓ]
      congr 2
      simp
    · unfold bodyCost
      simp only [clen, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
        List.length_nil]
      omega

/-! ### The slot loops -/

/-- The chunk-group layer headers in slot order. -/
def chunkHdrs (p d w ℓ K : ℕ) (ts : List ℕ) : List (List Bool) :=
  ((List.range (ℓ - 1)).drop ((ℓ - 1) % K)).map fun h => chunkHdr p d (2 ^ ℓ) w (Nat.log 2 ts.prod) ts ℓ K h

/-- The header tape when the slots below `m` (forward: still to come; opposite: done) split the
headers. -/
def hdAt (p d w ℓ K : ℕ) (ts : List ℕ) (m : ℕ) : WTape :=
  ⟨((chunkHdrs p d w ℓ K ts).take (m - (ℓ - 1) % K)).reverse, (chunkHdrs p d w ℓ K ts).drop (m - (ℓ - 1) % K)⟩

theorem length_chunkHdrs (p d w ℓ K : ℕ) (ts : List ℕ) :
    (chunkHdrs p d w ℓ K ts).length = ℓ - 1 - (ℓ - 1) % K := by
  simp [chunkHdrs]

theorem chunkHdrs_get (p d w ℓ K : ℕ) (ts : List ℕ) {m : ℕ} (hb : (ℓ - 1) % K ≤ m) (ht : m < ℓ - 1) :
    (chunkHdrs p d w ℓ K ts)[m - (ℓ - 1) % K]'(by rw [length_chunkHdrs]; omega) =
      chunkHdr p d (2 ^ ℓ) w (Nat.log 2 ts.prod) ts ℓ K m := by
  simp only [chunkHdrs, List.getElem_map, List.getElem_drop, List.getElem_range]
  congr 1; omega

/-- The header step of a slot: a chunk-group slot moves its header across the head. -/
theorem hdAt_step (p d w ℓ K : ℕ) (ts : List ℕ) {m : ℕ} (hm : m < ℓ) :
    if (ℓ - 1) % K ≤ m ∧ m < ℓ - 1 then ∃ L R,
      hdAt p d w ℓ K ts (m + 1) = ⟨chunkHdr p d (2 ^ ℓ) w (Nat.log 2 ts.prod) ts ℓ K m :: L, R⟩ ∧
      hdAt p d w ℓ K ts m = ⟨L, chunkHdr p d (2 ^ ℓ) w (Nat.log 2 ts.prod) ts ℓ K m :: R⟩
    else hdAt p d w ℓ K ts m = hdAt p d w ℓ K ts (m + 1) := by
  split_ifs with hc
  · obtain ⟨hb, ht⟩ := hc
    set l := chunkHdrs p d w ℓ K ts
    have hlt : m - (ℓ - 1) % K < l.length := by rw [length_chunkHdrs]; omega
    refine ⟨(l.take (m - (ℓ - 1) % K)).reverse, l.drop (m + 1 - (ℓ - 1) % K), ?_, ?_⟩
    · simp only [hdAt]
      rw [show m + 1 - (ℓ - 1) % K = m - (ℓ - 1) % K + 1 by omega, List.take_succ,
        List.getElem?_eq_getElem hlt, chunkHdrs_get p d w ℓ K ts hb ht]
      simp [l]
    · simp only [hdAt]
      rw [List.drop_eq_getElem_cons hlt, chunkHdrs_get p d w ℓ K ts hb ht,
        show m - (ℓ - 1) % K + 1 = m + 1 - (ℓ - 1) % K by omega]
  · simp only [hdAt]
    by_cases hb : m < (ℓ - 1) % K
    · rw [show m - (ℓ - 1) % K = 0 by omega, show m + 1 - (ℓ - 1) % K = 0 by omega]
    · have ht : m = ℓ - 1 := by omega
      have h1 : (chunkHdrs p d w ℓ K ts).length ≤ m - (ℓ - 1) % K := by rw [length_chunkHdrs]; omega
      have h2 : (chunkHdrs p d w ℓ K ts).length ≤ m + 1 - (ℓ - 1) % K := by rw [length_chunkHdrs]; omega
      rw [List.take_of_length_le h1, List.take_of_length_le h2, List.drop_of_length_le h1,
        List.drop_of_length_le h2]

/-- The forward words of slot `h`. -/
noncomputable def slotF (p d w ℓ K : ℕ) (ts : List ℕ) (hL : LayoutOK (2 ^ ℓ) ts ℓ K) (h : ℕ) : List (List Bool) :=
  hadWords p d (2 ^ ℓ) w (Nat.log 2 ts.prod) ts ℓ K h ++ twistWords (paperPerm hL) (2 ^ ℓ) ts h

/-- The opposite words of slot `h`. -/
noncomputable def slotO (p d w ℓ K : ℕ) (ts : List ℕ) (hL : LayoutOK (2 ^ ℓ) ts ℓ K) (h : ℕ) : List (List Bool) :=
  twistWords (paperPerm hL) (2 ^ ℓ) ts h ++ hadWords p d (2 ^ ℓ) w (Nat.log 2 ts.prod) ts ℓ K h

@[simp] theorem rep_headD (n : ℕ) : (List.replicate n ([] : List Bool)).headD [] = [] := by
  cases n <;> rfl

@[simp] theorem rep_head_getD (n : ℕ) : (List.replicate n ([] : List Bool)).head?.getD [] = [] := by
  cases n <;> rfl

theorem decCost_mono (D h : ℕ) : decCost D h ≤ decCost D (h + 1) := by
  unfold decCost
  have : h * D ≤ (h + 1) * D := Nat.mul_le_mul_right D (by omega)
  omega

/-- One forward loop step. -/
noncomputable def stepF : Cmd 0 37 := .seq bodyF (.seq decF (skp mT mJ (by decide)))

/-- One opposite loop step. -/
noncomputable def stepO : Cmd 0 37 := .seq bodyO (.seq incO (skp mT mJ (by decide)))

/-- The forward slot loop. -/
noncomputable def loopF : Cmd 0 37 := .loop mT stepF

/-- The opposite slot loop. -/
noncomputable def loopO : Cmd 0 37 := .loop mT stepO

/-- The forward state with `m` slots left. -/
noncomputable def stF (p d w ℓ K : ℕ) (ts : List ℕ) (hL : LayoutOK (2 ^ ℓ) ts ℓ K) (m : ℕ) : Fin 37 → WTape :=
  mst ℓ K ts (hdAt p d w ℓ K ts m)
    ⟨(((List.range ℓ).reverse.take (ℓ - m)).flatMap (slotF p d w ℓ K ts hL)).reverse, []⟩
    ⟨List.replicate (ℓ - m) [], List.replicate m []⟩ (m - 1)

/-- The opposite state with `k` slots done. -/
noncomputable def stO (p d w ℓ K : ℕ) (ts : List ℕ) (hL : LayoutOK (2 ^ ℓ) ts ℓ K) (k : ℕ) : Fin 37 → WTape :=
  mst ℓ K ts (hdAt p d w ℓ K ts k) ⟨((List.range k).flatMap (slotO p d w ℓ K ts hL)).reverse, []⟩
    ⟨List.replicate k [], List.replicate (ℓ - k) []⟩ k

/-- The cost of one loop step at slot `h`. -/
def stepCost (p d w ℓ K : ℕ) (ts : List ℕ) (h : ℕ) : ℕ :=
  bodyCost ℓ K ts h (chunkHdr p d (2 ^ ℓ) w (Nat.log 2 ts.prod) ts ℓ K h).length + 1 +
    (decCost ts.length (h + 1) + 1 + 5)

theorem take_range_reverse {ℓ m : ℕ} (hm : m < ℓ) :
    (List.range ℓ).reverse.take (ℓ - m) = (List.range ℓ).reverse.take (ℓ - (m + 1)) ++ [m] := by
  have hlt : ℓ - (m + 1) < (List.range ℓ).reverse.length := by simp; omega
  rw [show ℓ - m = ℓ - (m + 1) + 1 by omega, List.take_succ, List.getElem?_eq_getElem hlt]
  simp only [List.getElem_reverse, List.getElem_range, List.length_range, Option.toList_some]
  congr 2; omega

set_option maxHeartbeats 16000000 in
theorem runs_stepF (p d w : ℕ) {ℓ K : ℕ} {ts : List ℕ} (hL : LayoutOK (2 ^ ℓ) ts ℓ K) {m : ℕ} (hm : m < ℓ) :
    Runs stepF (stF p d w ℓ K ts hL (m + 1)) (· = stF p d w ℓ K ts hL m) (stepCost p d w ℓ K ts m) := by
  have hstep := hdAt_step p d w ℓ K ts hm
  have s1 := runs_bodyF p d w hL hm ⟨List.replicate (ℓ - (m + 1)) [], List.replicate (m + 1) []⟩
    (((List.range ℓ).reverse.take (ℓ - (m + 1))).flatMap (slotF p d w ℓ K ts hL)).reverse
    (hdAt p d w ℓ K ts (m + 1)) (hdAt p d w ℓ K ts m)
    (chunkHdr p d (2 ^ ℓ) w (Nat.log 2 ts.prod) ts ℓ K m).length (by
      split_ifs at hstep ⊢ with hc
      · obtain ⟨L, R, e1, e2⟩ := hstep
        exact ⟨L, R, e1, e2, le_rfl⟩
      · exact hstep)
  have s2 := runs_decF ℓ K ts (hdAt p d w ℓ K ts m)
    ⟨(slotF p d w ℓ K ts hL m).reverse ++
      (((List.range ℓ).reverse.take (ℓ - (m + 1))).flatMap (slotF p d w ℓ K ts hL)).reverse, []⟩
    ⟨List.replicate (ℓ - (m + 1)) [], List.replicate (m + 1) []⟩ m
  set σ₂ := mst ℓ K ts (hdAt p d w ℓ K ts m)
    ⟨(slotF p d w ℓ K ts hL m).reverse ++
      (((List.range ℓ).reverse.take (ℓ - (m + 1))).flatMap (slotF p d w ℓ K ts hL)).reverse, []⟩
    ⟨List.replicate (ℓ - (m + 1)) [], List.replicate (m + 1) []⟩ (m - 1) with hσ₂
  have s3 := runs_skp (a := 0) (show mT ≠ mJ by decide) σ₂ (by simp [hσ₂, List.replicate_succ])
    (by tsimp [hσ₂, mst, mconst])
  have hm1 : (m + 1) - 1 = m := by omega
  have hc : (σ₂ mT).cur.length = 0 := by simp [hσ₂]
  refine (Runs.then (by rw [stF, hm1]; exact s1) (Runs.then s2 s3)).mono (fun σ' e => ?_) ?_
  · rw [e, hσ₂, mst_T, mst_update_T, stF, take_range_reverse hm, List.flatMap_append]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.reverse_append]
    congr 2
    · rw [show ℓ - m = ℓ - (m + 1) + 1 by omega]
      simp [List.replicate_succ]
  · rw [hc]
    have := decCost_mono ts.length m
    unfold stepCost
    omega

/-- The forward loop's cost with `m` slots left. -/
def loopCostF (p d w ℓ K : ℕ) (ts : List ℕ) : ℕ → ℕ
  | 0 => 0
  | m + 1 => stepCost p d w ℓ K ts m + 2 + loopCostF p d w ℓ K ts m

theorem runs_loopF (p d w : ℕ) {ℓ K : ℕ} {ts : List ℕ} (hL : LayoutOK (2 ^ ℓ) ts ℓ K) :
    ∀ m, m ≤ ℓ → Runs loopF (stF p d w ℓ K ts hL m) (· = stF p d w ℓ K ts hL 0) (loopCostF p d w ℓ K ts m)
  | 0, _ => Runs.loop_done (by simp [stF]) rfl
  | m + 1, hm => by
    have ih := runs_loopF p d w hL m (by omega)
    have := Runs.loop_step (i := mT) (b := stepF) (by simp [stF, List.replicate_succ])
      ((runs_stepF p d w hL (show m < ℓ by omega)).mono (fun σ e => by rw [e]; exact ih) le_rfl)
    exact this

set_option maxHeartbeats 16000000 in
theorem runs_stepO (p d w : ℕ) {ℓ K : ℕ} {ts : List ℕ} (hL : LayoutOK (2 ^ ℓ) ts ℓ K) {k : ℕ} (hk : k < ℓ) :
    Runs stepO (stO p d w ℓ K ts hL k) (· = stO p d w ℓ K ts hL (k + 1)) (stepCost p d w ℓ K ts k) := by
  have hstep := hdAt_step p d w ℓ K ts hk
  have s1 := runs_bodyO p d w hL hk ⟨List.replicate k [], List.replicate (ℓ - k) []⟩
    ((List.range k).flatMap (slotO p d w ℓ K ts hL)).reverse
    (hdAt p d w ℓ K ts k) (hdAt p d w ℓ K ts (k + 1))
    (chunkHdr p d (2 ^ ℓ) w (Nat.log 2 ts.prod) ts ℓ K k).length (by
      split_ifs at hstep ⊢ with hc
      · obtain ⟨L, R, e1, e2⟩ := hstep
        exact ⟨L, R, e2, e1, le_rfl⟩
      · exact hstep.symm)
  have s2 := runs_incO ℓ K ts (hdAt p d w ℓ K ts (k + 1))
    ⟨(slotO p d w ℓ K ts hL k).reverse ++ ((List.range k).flatMap (slotO p d w ℓ K ts hL)).reverse, []⟩
    ⟨List.replicate k [], List.replicate (ℓ - k) []⟩ k
  set σ₂ := mst ℓ K ts (hdAt p d w ℓ K ts (k + 1))
    ⟨(slotO p d w ℓ K ts hL k).reverse ++ ((List.range k).flatMap (slotO p d w ℓ K ts hL)).reverse, []⟩
    ⟨List.replicate k [], List.replicate (ℓ - k) []⟩ (k + 1) with hσ₂
  have hlk : ℓ - k = ℓ - (k + 1) + 1 := by omega
  have s3 := runs_skp (a := 0) (show mT ≠ mJ by decide) σ₂
    (by simp [hσ₂, hlk, List.replicate_succ])
    (by tsimp [hσ₂, mst, mconst])
  have hc : (σ₂ mT).cur.length = 0 := by simp [hσ₂]
  refine (Runs.then s1 (Runs.then s2 s3)).mono (fun σ' e => ?_) ?_
  · rw [e, hσ₂, mst_T, mst_update_T, stO, List.range_succ, List.flatMap_append]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.reverse_append]
    congr 2
    · rw [hlk]
      simp [List.replicate_succ]
  · rw [hc]
    unfold stepCost
    omega

/-- The opposite loop's cost with `r` slots left, from slot `ℓ - r`. -/
def loopCostO (p d w ℓ K : ℕ) (ts : List ℕ) : ℕ → ℕ
  | 0 => 0
  | r + 1 => stepCost p d w ℓ K ts (ℓ - (r + 1)) + 2 + loopCostO p d w ℓ K ts r

theorem runs_loopO (p d w : ℕ) {ℓ K : ℕ} {ts : List ℕ} (hL : LayoutOK (2 ^ ℓ) ts ℓ K) :
    ∀ r, r ≤ ℓ → Runs loopO (stO p d w ℓ K ts hL (ℓ - r)) (· = stO p d w ℓ K ts hL ℓ) (loopCostO p d w ℓ K ts r)
  | 0, _ => Runs.loop_done (by simp [stO]) (by rw [Nat.sub_zero])
  | r + 1, hr => by
    have ih := runs_loopO p d w hL r (by omega)
    have hk : ℓ - (r + 1) + 1 = ℓ - r := by omega
    have := Runs.loop_step (i := mT) (b := stepO)
      (by simp [stO, show ℓ - (ℓ - (r + 1)) = r + 1 by omega, List.replicate_succ])
      ((runs_stepO p d w hL (show ℓ - (r + 1) < ℓ by omega)).mono (fun σ e => by rw [e, hk]; exact ih) le_rfl)
    exact this

/-! ### The whole slot program -/

/-- `c := c + k·|u|` over the `k` ticks of `k`: append the register `u` once per tick. -/
noncomputable def mulLoop {t : ℕ} (k c u j : Fin t) (h1 : k ≠ j) (h2 : u ≠ c) : Cmd 0 t :=
  .loop k (.seq (appendReg u c h2) (skp k j h1))

theorem runs_mulLoop {t : ℕ} {k c u j : Fin t} (h1 : k ≠ j) (h2 : u ≠ c) (hkc : k ≠ c) (hku : k ≠ u)
    (hcj : c ≠ j) (huj : u ≠ j) (D : ℕ) :
    ∀ (e n : ℕ) (σ : Fin t → WTape) (L : List (List Bool)), σ k = ⟨L, List.replicate e []⟩ →
      σ c = ⟨[ones n], []⟩ → σ u = reg (ones D) → (σ j).right = [] →
      Runs (mulLoop k c u j h1 h2) σ
        (· = Function.update (Function.update σ k ⟨List.replicate e [] ++ L, []⟩) c ⟨[ones (n + e * D)], []⟩)
        (e * (2 * D + 20))
  | 0, n, σ, L, hk, hc, hu, hj => by
    show Runs (Cmd.loop k _) _ _ _
    refine (Runs.loop_done (by simp [hk]) rfl).mono (fun σ' e => ?_) (by simp)
    subst e
    funext x
    by_cases hxc : x = c
    · subst hxc; simp [hc]
    · by_cases hxk : x = k
      · subst hxk; simp [hxc, hk]
      · simp [hxc, hxk]
  | e + 1, n, σ, L, hk, hc, hu, hj => by
    show Runs (Cmd.loop k _) _ _ _
    have s1 := runs_appendReg (a := 0) h2 σ (u := ones D) (v := ones n) (M := []) hu hc
    set σ₁ := Function.update σ c ⟨[ones (n + D)], []⟩ with hσ₁
    have e1 : Function.update σ c ⟨(ones n ++ ones D) :: [], []⟩ = σ₁ := by rw [hσ₁, ones_append_ones]
    rw [e1] at s1
    have hk₁ : σ₁ k = ⟨L, [] :: List.replicate e []⟩ := by simp [hσ₁, hkc, hk, List.replicate_succ]
    have s2 := runs_skp (a := 0) h1 σ₁ (by simp [hk₁]) (by simp [hσ₁, hcj.symm, hj])
    set σ₂ := Function.update σ₁ k ⟨[] :: L, List.replicate e []⟩ with hσ₂
    have e2 : Function.update σ₁ k (σ₁ k).next = σ₂ := by simp [hσ₂, hk₁]
    rw [e2] at s2
    have ih := runs_mulLoop h1 h2 hkc hku hcj huj D e (n + D) σ₂ ([] :: L) (by simp [hσ₂])
      (by simp [hσ₂, hσ₁, hkc.symm]) (by simp [hσ₂, hσ₁, hku.symm, h2, hu]) (by simp [hσ₂, hσ₁, h1.symm, hcj.symm, hj])
    refine (Runs.loop_step (by simp [hk]) ((Runs.then s1 s2).mono (fun σ' e' => by rw [e']; exact ih)
      le_rfl)).mono (fun σ' e' => ?_) ?_
    · rw [e']
      have e3 : n + D + e * D = n + (e + 1) * D := by ring
      have e4 : List.replicate e [] ++ [] :: L = List.replicate (e + 1) ([] : List Bool) ++ L := by
        simp [List.replicate_succ']
      funext x
      by_cases hxc : x = c
      · subst hxc; simp [e3]
      · by_cases hxk : x = k
        · subst hxk; simp [hxc, e4]
        · simp [hσ₂, hσ₁, hxc, hxk]
    · have hc0 : (σ₁ k).cur.length = 0 := by simp [hk₁]
      rw [hc0]
      simp only [length_ones]
      nlinarith

/-- The headers' tape after the header pass: every header, the head after them. -/
noncomputable def hdFull (p d w ℓ K : ℕ) (ts : List ℕ) : WTape := ⟨(chunkHdrs p d w ℓ K ts).reverse, []⟩

/-- The slot bank before the slot loop. -/
noncomputable def mIn (p d w ℓ K : ℕ) (ts : List ℕ) : Fin 37 → WTape :=
  Function.update (mconst ℓ K ts) mHD (hdFull p d w ℓ K ts)

/-- The forward slot program: ticks, `h = ℓ - 1`, `h·D`, the loop, then clearing. -/
noncomputable def mainF : Cmd 0 37 :=
  .seq (dropReg mP1 mKC mTmp (by decide) (by decide) (by decide)) <| .seq (ticksReg mTmp mT (by decide)) <|
  .seq (clear mTmp) <| .seq (regDup mM1 mH (by decide)) <| .seq (ticksReg mM1 mPK (by decide)) <|
  .seq (emit [[]] mHDD) <| .seq (mulLoop mPK mHDD mN mJ (by decide) (by decide)) <| .seq (clear mPK) <|
  .seq (rewind mHDD) <| .seq loopF <| .seq (clear mHD) <| .seq (clear mH) <| .seq (clear mHDD) (clear mT)

/-- The opposite slot program: ticks, `h = 0`, the headers rewound, the loop, then clearing. -/
noncomputable def mainO : Cmd 0 37 :=
  .seq (dropReg mP1 mKC mTmp (by decide) (by decide) (by decide)) <| .seq (ticksReg mTmp mT (by decide)) <|
  .seq (clear mTmp) <| .seq (emit [[]] mH) <| .seq (rewind mH) <| .seq (emit [[]] mHDD) <| .seq (rewind mHDD) <|
  .seq (rewind mHD) <| .seq loopO <| .seq (clear mHD) <| .seq (clear mH) <| .seq (clear mHDD) (clear mT)

theorem hdAt_full (p d w ℓ K : ℕ) (ts : List ℕ) : hdAt p d w ℓ K ts ℓ = hdFull p d w ℓ K ts := by
  have h1 : (chunkHdrs p d w ℓ K ts).length ≤ ℓ - (ℓ - 1) % K := by rw [length_chunkHdrs]; omega
  simp [hdAt, hdFull, List.take_of_length_le h1, List.drop_of_length_le h1]

theorem hdAt_zero (p d w ℓ K : ℕ) (ts : List ℕ) : hdAt p d w ℓ K ts 0 = ⟨[], chunkHdrs p d w ℓ K ts⟩ := by
  simp [hdAt]

/-- A bound on the clearing and setup around the loops. -/
def mainExtra (p d w ℓ K : ℕ) (ts : List ℕ) : ℕ :=
  20 * (ℓ + 1) + 20 * (ℓ * ts.length + ts.length) + 20 * ℓ * (2 * ts.length + 20) +
    4 * clen (chunkHdrs p d w ℓ K ts) + 1000

set_option maxHeartbeats 32000000 in
/-- `runs_mainF`: the forward slot program writes `fwdScript` and restores every other tape. -/
theorem runs_mainF (p d w : ℕ) {ℓ K : ℕ} {ts : List ℕ} (hL : LayoutOK (2 ^ ℓ) ts ℓ K) :
    Runs mainF (mIn p d w ℓ K ts)
      (· = Function.update (mconst ℓ K ts) mO
        ⟨(fwdScript p d (2 ^ ℓ) w (paperPerm hL) ts ℓ K).reverse, []⟩)
      (mainExtra p d w ℓ K ts + loopCostF p d w ℓ K ts ℓ) := by
  have hℓ : 1 ≤ ℓ := hL.2.2.2
  set σ := mIn p d w ℓ K ts with hσ
  have s1 := runs_dropReg (a := 0) (show mP1 ≠ mKC by decide) (show mP1 ≠ mTmp by decide)
    (show mKC ≠ mTmp by decide) σ (u := ones (ℓ + 1)) (v := [true]) (by tsimp [hσ, mIn, mconst])
    (by tsimp [hσ, mIn, mconst]) (by tsimp [hσ, mIn, mconst])
  set σ₁ := Function.update σ mTmp (reg (ones ℓ)) with hσ₁
  have e1 : Function.update σ mTmp (reg ((ones (ℓ + 1)).drop [true].length)) = σ₁ := by
    rw [hσ₁, List.length_singleton, drop_ones]; rfl
  rw [e1] at s1
  have s2 := runs_ticksReg (a := 0) (show mTmp ≠ mT by decide) σ₁ (u := ones ℓ) (by tsimp [hσ₁])
    (by tsimp [hσ₁, hσ, mIn, mconst])
  set σ₂ := Function.update σ₁ mT ⟨[], List.replicate ℓ []⟩ with hσ₂
  have e2 : Function.update σ₁ mT ⟨[], List.replicate (ones ℓ).length []⟩ = σ₂ := by rw [hσ₂, length_ones]
  rw [e2] at s2
  have s3 := runs_clear' (a := 0) mTmp σ₂ (T := reg (ones ℓ)) (by tsimp [hσ₂, hσ₁])
  set σ₃ := Function.update σ₂ mTmp emp with hσ₃
  have s4 := runs_regDup (a := 0) (show mM1 ≠ mH by decide) σ₃ (w := ones (ℓ - 1))
    (by tsimp [hσ₃, hσ₂, hσ₁, hσ, mIn, mconst]) (by tsimp [hσ₃, hσ₂, hσ₁, hσ, mIn, mconst])
  set σ₄ := Function.update σ₃ mH (reg (ones (ℓ - 1))) with hσ₄
  have s5 := runs_ticksReg (a := 0) (show mM1 ≠ mPK by decide) σ₄ (u := ones (ℓ - 1))
    (by tsimp [hσ₄, hσ₃, hσ₂, hσ₁, hσ, mIn, mconst]) (by tsimp [hσ₄, hσ₃, hσ₂, hσ₁, hσ, mIn, mconst])
  set σ₅ := Function.update σ₄ mPK ⟨[], List.replicate (ℓ - 1) []⟩ with hσ₅
  have e5 : Function.update σ₄ mPK ⟨[], List.replicate (ones (ℓ - 1)).length []⟩ = σ₅ := by rw [hσ₅, length_ones]
  rw [e5] at s5
  have s6 := runs_emit (a := 0) [[]] mHDD σ₅ (by tsimp [hσ₅, hσ₄, hσ₃, hσ₂, hσ₁, hσ, mIn, mconst])
  set σ₆ := Function.update σ₅ mHDD ⟨[ones 0], []⟩ with hσ₆
  have e6 : Function.update σ₅ mHDD ⟨[[]].reverse ++ (σ₅ mHDD).left, []⟩ = σ₆ := by
    tsimp [hσ₆, hσ₅, hσ₄, hσ₃, hσ₂, hσ₁, hσ, mIn, mconst, ones]
  rw [e6] at s6
  have s7 := runs_mulLoop (show mPK ≠ mJ by decide) (show mN ≠ mHDD by decide) (by decide) (by decide)
    (by decide) (by decide) ts.length (ℓ - 1) 0 σ₆ [] (by tsimp [hσ₆, hσ₅]) (by tsimp [hσ₆])
    (by tsimp [hσ₆, hσ₅, hσ₄, hσ₃, hσ₂, hσ₁, hσ, mIn, mconst])
    (by tsimp [hσ₆, hσ₅, hσ₄, hσ₃, hσ₂, hσ₁, hσ, mIn, mconst])
  set σ₇ := Function.update (Function.update σ₆ mPK ⟨List.replicate (ℓ - 1) [] ++ [], []⟩) mHDD
    ⟨[ones (0 + (ℓ - 1) * ts.length)], []⟩ with hσ₇
  have s8 := runs_clear' (a := 0) mPK σ₇ (T := ⟨List.replicate (ℓ - 1) [] ++ [], []⟩) (by tsimp [hσ₇])
  set σ₈ := Function.update σ₇ mPK emp with hσ₈
  have s9 := runs_rewind' (a := 0) mHDD σ₈ (L := [ones (0 + (ℓ - 1) * ts.length)]) (R := []) (by tsimp [hσ₈, hσ₇])
  have e9 : Function.update σ₈ mHDD ⟨[], [ones (0 + (ℓ - 1) * ts.length)].reverse ++ []⟩ =
      stF p d w ℓ K ts hL ℓ := by
    funext i; fin_cases i <;> tsimp [hσ₈, hσ₇, hσ₆, hσ₅, hσ₄, hσ₃, hσ₂, hσ₁, hσ, mIn, mconst, stF, mst, hdAt_full,
      emp, reg]
  rw [e9] at s9
  have s10 := runs_loopF p d w hL ℓ le_rfl
  set σ₁₀ := stF p d w ℓ K ts hL 0 with hσ₁₀
  have s11 := runs_clear' (a := 0) mHD σ₁₀ (T := ⟨[], chunkHdrs p d w ℓ K ts⟩) (by rw [hσ₁₀, stF, mst_HD, hdAt_zero])
  set σ₁₁ := Function.update σ₁₀ mHD emp with hσ₁₁
  have s12 := runs_clear' (a := 0) mH σ₁₁ (T := reg (ones (0 - 1))) (by tsimp [hσ₁₁, hσ₁₀, stF, mst])
  set σ₁₂ := Function.update σ₁₁ mH emp with hσ₁₂
  have s13 := runs_clear' (a := 0) mHDD σ₁₂ (T := reg (ones ((0 - 1) * ts.length)))
    (by tsimp [hσ₁₂, hσ₁₁, hσ₁₀, stF, mst])
  set σ₁₃ := Function.update σ₁₂ mHDD emp with hσ₁₃
  have s14 := runs_clear' (a := 0) mT σ₁₃ (T := ⟨List.replicate ℓ [], []⟩)
    (by tsimp [hσ₁₃, hσ₁₂, hσ₁₁, hσ₁₀, stF, mst])
  refine (Runs.then s1 (Runs.then s2 (Runs.then s3 (Runs.then s4 (Runs.then s5 (Runs.then s6 (Runs.then s7
    (Runs.then s8 (Runs.then s9 (Runs.then s10 (Runs.then s11 (Runs.then s12 (Runs.then s13
    s14))))))))))))).mono (fun σ' e => ?_) ?_
  · rw [e]
    have hs : fwdScript p d (2 ^ ℓ) w (paperPerm hL) ts ℓ K =
        ((List.range ℓ).reverse.take (ℓ - 0)).flatMap (slotF p d w ℓ K ts hL) := by
      rw [Nat.sub_zero, List.take_of_length_le (by simp)]; rfl
    rw [hs]
    funext i; fin_cases i <;> tsimp [hσ₁₃, hσ₁₂, hσ₁₁, hσ₁₀, stF, mst, mconst, emp]
  · have hm : (ℓ - 1) * ts.length ≤ ℓ * ts.length := Nat.mul_le_mul_right _ (by omega)
    simp only [mainExtra, clen, WTape.words, reg, emp, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      length_ones, List.length_cons, List.length_nil, List.reverse_nil, List.nil_append, List.append_nil,
      List.map_replicate, List.sum_replicate, List.length_replicate, smul_eq_mul, List.reverse_reverse,
      List.length_singleton, Nat.zero_add, Nat.zero_sub, Nat.zero_mul]
    simp only [List.reverse_replicate, List.map_replicate, List.sum_replicate, List.length_nil, smul_eq_mul]
    have h2 : (ℓ - 1) * (2 * ts.length + 20) ≤ ℓ * (2 * ts.length + 20) := Nat.mul_le_mul_right _ (by omega)
    have h3 : 20 * ℓ * (2 * ts.length + 20) = 20 * (ℓ * (2 * ts.length + 20)) := by ring
    omega

set_option maxHeartbeats 32000000 in
/-- `runs_mainO`: the opposite slot program writes `oppScript` and restores every other tape. -/
theorem runs_mainO (p d w : ℕ) {ℓ K : ℕ} {ts : List ℕ} (hL : LayoutOK (2 ^ ℓ) ts ℓ K) :
    Runs mainO (mIn p d w ℓ K ts)
      (· = Function.update (mconst ℓ K ts) mO
        ⟨(oppScript p d (2 ^ ℓ) w (paperPerm hL) ts ℓ K).reverse, []⟩)
      (mainExtra p d w ℓ K ts + loopCostO p d w ℓ K ts ℓ) := by
  have hℓ : 1 ≤ ℓ := hL.2.2.2
  set σ := mIn p d w ℓ K ts with hσ
  have s1 := runs_dropReg (a := 0) (show mP1 ≠ mKC by decide) (show mP1 ≠ mTmp by decide)
    (show mKC ≠ mTmp by decide) σ (u := ones (ℓ + 1)) (v := [true]) (by tsimp [hσ, mIn, mconst])
    (by tsimp [hσ, mIn, mconst]) (by tsimp [hσ, mIn, mconst])
  set σ₁ := Function.update σ mTmp (reg (ones ℓ)) with hσ₁
  have e1 : Function.update σ mTmp (reg ((ones (ℓ + 1)).drop [true].length)) = σ₁ := by
    rw [hσ₁, List.length_singleton, drop_ones]; rfl
  rw [e1] at s1
  have s2 := runs_ticksReg (a := 0) (show mTmp ≠ mT by decide) σ₁ (u := ones ℓ) (by tsimp [hσ₁])
    (by tsimp [hσ₁, hσ, mIn, mconst])
  set σ₂ := Function.update σ₁ mT ⟨[], List.replicate ℓ []⟩ with hσ₂
  have e2 : Function.update σ₁ mT ⟨[], List.replicate (ones ℓ).length []⟩ = σ₂ := by rw [hσ₂, length_ones]
  rw [e2] at s2
  have s3 := runs_clear' (a := 0) mTmp σ₂ (T := reg (ones ℓ)) (by tsimp [hσ₂, hσ₁])
  set σ₃ := Function.update σ₂ mTmp emp with hσ₃
  have s4 := runs_emit (a := 0) [[]] mH σ₃ (by tsimp [hσ₃, hσ₂, hσ₁, hσ, mIn, mconst])
  set σ₄ := Function.update σ₃ mH ⟨[[]], []⟩ with hσ₄
  have e4 : Function.update σ₃ mH ⟨[[]].reverse ++ (σ₃ mH).left, []⟩ = σ₄ := by
    tsimp [hσ₄, hσ₃, hσ₂, hσ₁, hσ, mIn, mconst]
  rw [e4] at s4
  have s5 := runs_rewind' (a := 0) mH σ₄ (L := [[]]) (R := []) (by tsimp [hσ₄])
  set σ₅ := Function.update σ₄ mH ⟨[], [[]].reverse ++ []⟩ with hσ₅
  have s6 := runs_emit (a := 0) [[]] mHDD σ₅ (by tsimp [hσ₅, hσ₄, hσ₃, hσ₂, hσ₁, hσ, mIn, mconst])
  set σ₆ := Function.update σ₅ mHDD ⟨[[]], []⟩ with hσ₆
  have e6 : Function.update σ₅ mHDD ⟨[[]].reverse ++ (σ₅ mHDD).left, []⟩ = σ₆ := by
    tsimp [hσ₆, hσ₅, hσ₄, hσ₃, hσ₂, hσ₁, hσ, mIn, mconst]
  rw [e6] at s6
  have s7 := runs_rewind' (a := 0) mHDD σ₆ (L := [[]]) (R := []) (by tsimp [hσ₆])
  set σ₇ := Function.update σ₆ mHDD ⟨[], [[]].reverse ++ []⟩ with hσ₇
  have s8 := runs_rewind' (a := 0) mHD σ₇ (L := (chunkHdrs p d w ℓ K ts).reverse) (R := [])
    (by tsimp [hσ₇, hσ₆, hσ₅, hσ₄, hσ₃, hσ₂, hσ₁, hσ, mIn, mconst, hdFull])
  have e8 : Function.update σ₇ mHD ⟨[], (chunkHdrs p d w ℓ K ts).reverse.reverse ++ []⟩ = stO p d w ℓ K ts hL 0 := by
    funext i; fin_cases i <;> tsimp [hσ₇, hσ₆, hσ₅, hσ₄, hσ₃, hσ₂, hσ₁, hσ, mIn, mconst, stO, mst, hdAt_zero,
      emp, reg, ones]
  rw [e8] at s8
  have s9 := runs_loopO p d w hL ℓ le_rfl
  rw [Nat.sub_self] at s9
  set σ₉ := stO p d w ℓ K ts hL ℓ with hσ₉
  have s10 := runs_clear' (a := 0) mHD σ₉ (T := hdFull p d w ℓ K ts) (by rw [hσ₉, stO, mst_HD, hdAt_full])
  set σ₁₀ := Function.update σ₉ mHD emp with hσ₁₀
  have s11 := runs_clear' (a := 0) mH σ₁₀ (T := reg (ones ℓ)) (by tsimp [hσ₁₀, hσ₉, stO, mst])
  set σ₁₁ := Function.update σ₁₀ mH emp with hσ₁₁
  have s12 := runs_clear' (a := 0) mHDD σ₁₁ (T := reg (ones (ℓ * ts.length)))
    (by tsimp [hσ₁₁, hσ₁₀, hσ₉, stO, mst])
  set σ₁₂ := Function.update σ₁₁ mHDD emp with hσ₁₂
  have s13 := runs_clear' (a := 0) mT σ₁₂ (T := ⟨List.replicate ℓ [], List.replicate (ℓ - ℓ) []⟩)
    (by tsimp [hσ₁₂, hσ₁₁, hσ₁₀, hσ₉, stO, mst])
  refine (Runs.then s1 (Runs.then s2 (Runs.then s3 (Runs.then s4 (Runs.then s5 (Runs.then s6 (Runs.then s7
    (Runs.then s8 (Runs.then s9 (Runs.then s10 (Runs.then s11 (Runs.then s12 s13)))))))))))).mono
    (fun σ' e => ?_) ?_
  · rw [e]
    have hs : oppScript p d (2 ^ ℓ) w (paperPerm hL) ts ℓ K = (List.range ℓ).flatMap (slotO p d w ℓ K ts hL) := rfl
    rw [hs]
    funext i; fin_cases i <;> tsimp [hσ₁₂, hσ₁₁, hσ₁₀, hσ₉, stO, mst, mconst, emp]
  · simp only [mainExtra, clen, WTape.words, reg, emp, hdFull, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, length_ones, List.length_cons, List.length_nil, List.reverse_nil, List.nil_append,
      List.append_nil, List.map_replicate, List.sum_replicate, List.length_replicate, smul_eq_mul,
      List.reverse_reverse, List.length_singleton, Nat.sub_self, List.replicate_zero, List.map_reverse,
      List.sum_reverse]
    omega

end ScriptMain

end IntegerMultBounds.Schoenhage
