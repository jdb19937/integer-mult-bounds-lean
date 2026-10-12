module

public import IntegerMultBounds.Resampling.AxisPrims
public import IntegerMultBounds.Resampling.LineValue
public import IntegerMultBounds.Schoenhage.FloorWords
public import IntegerMultBounds.Schoenhage.Relabel
public import IntegerMultBounds.Schoenhage.PrimLift
public import IntegerMultBounds.Schoenhage.RingPointwise

/-! One axis of the tensor driver on word tapes. The array is one word in the
paper's layout (components most significant bit first), lines of `t` entries.
`expandStep` keeps the first `s` entries of every line (`refit`), cuts the
array into words, runs the `Ã` line loop, cuts its output into `W`-bit words,
floors each by one bit to `w` bits and joins them back (`runs_expandStep`). -/

@[expose] public section

set_option maxRecDepth 10000

namespace IntegerMultBounds.Resampling.AxisStep

open Machine Schoenhage

variable {a : ℕ}

/-- A relabelled program whose run is an exact bank, as an exact bank. -/
theorem clen_uniform (k : ℕ) : ∀ l : List (List Bool), (∀ x ∈ l, x.length = k) → clen l = l.length * (k + 1)
  | [], _ => by simp [clen]
  | x :: l, h => by
    rw [clen_cons, clen_uniform k l (fun y hy => h y (by simp [hy])), h x (by simp)]; simp; ring

theorem runs_map_upd {t t' : ℕ} (f : Fin t → Fin t') (hf : Function.Injective f) {c : Cmd a t}
    (τ : Fin t' → WTape) {σ' : Fin t → WTape} {B : ℕ} (h : Runs c (τ ∘ f) (· = σ') B)
    (G : Fin t' → WTape) (hG1 : ∀ y, G (f y) = σ' y) (hG2 : ∀ x, (∀ y, f y ≠ x) → G x = τ x) :
    Runs (c.map f hf) τ (· = G) B := by
  refine (h.map f hf τ rfl).mono (fun τ' ⟨hq, ho⟩ => ?_) le_rfl
  funext x
  by_cases hx : ∃ y, f y = x
  · obtain ⟨y, rfl⟩ := hx
    rw [hG1, ← hq]; rfl
  · push Not at hx
    rw [ho x hx, hG2 x hx]

theorem cut_msbArray {W : ℕ} (hW : 1 ≤ W) (ws : List (List Bool)) (h : ∀ x ∈ ws, x.length = W) :
    (cut W (msbArray ws)).map List.reverse = ws := by
  rw [msbArray, cut_flatten_words hW _ (fun c hc => by
    simp only [List.mem_map] at hc; obtain ⟨x, hx, rfl⟩ := hc; simp [h x hx])]
  simp

/-! ### The expansion bank -/

/-- Tapes `0 … 121`: the `Ã` primitive; then the array, the two line widths, two scratch
tapes, the word list, the word `[true]` and the floored list. -/
abbrev EB := 130

abbrev tX : Fin EB := 122
abbrev tU : Fin EB := 123
abbrev tV : Fin EB := 124
abbrev tS1 : Fin EB := 125
abbrev tS2 : Fin EB := 126
abbrev tY : Fin EB := 127
abbrev tOne : Fin EB := 128
abbrev tZ : Fin EB := 129

/-- The `Ã` primitive's tapes. -/
def aSlot : Fin (31 + 91) → Fin EB := Fin.castLE (by norm_num)
theorem aSlot_inj : Function.Injective aSlot := Fin.castLE_injective _

def fRefit : Fin 5 → Fin EB := ![tX, tU, tV, tS1, tS2]
def fIn : Fin 4 → Fin EB := ![tX, 9, 22, tS1]
def fOut : Fin 4 → Fin EB := ![29, 17, tY, tS1]
def fFloor : Fin 5 → Fin EB := ![tY, tOne, 9, tS1, tZ]
def fJoin : Fin 4 → Fin EB := ![tX, tS2, tZ, tS1]

theorem fRefit_inj : Function.Injective fRefit := by decide
theorem fIn_inj : Function.Injective fIn := by decide
theorem fOut_inj : Function.Injective fOut := by decide
theorem fFloor_inj : Function.Injective fFloor := by decide
theorem fJoin_inj : Function.Injective fJoin := by decide

/-- Trim the lines, apply `Ã` line by line, floor the outputs and join them. -/
noncomputable def expandStep : Cmd a EB :=
  .seq (refit.map fRefit fRefit_inj) <| .seq (toWords.map fIn fIn_inj) <| .seq (clear tX) <|
  .seq (.prim (Prim.lift AxisPrims.aPrim) aSlot aSlot_inj) <| .seq (toWords.map fOut fOut_inj) <|
  .seq (clear 29) <| .seq (floorLoop.map fFloor fFloor_inj) <| .seq (clear tY) <| .seq (rewind tZ) <|
  (fromWords.map fJoin fJoin_inj)

/-- The array handed to the `Ã` loop: the trimmed lines cut into words, least significant bit first. -/
def expandArr (A : List Bool) (s t w : ℕ) : List (List Bool) :=
  (cut w ((cut (2 * t * w) A).map (Rules.fit (2 * s * w))).flatten).map List.reverse

/-- The cost of one expansion axis: the `Ã` loop plus linear plumbing. -/
noncomputable def expandBound (A : List Bool) (wt : List (List Bool)) (s t m p w W L : ℕ) (sW tW : List Bool) : ℕ :=
  LineAPrim.progBound wt (expandArr A s t w) s t m p w W L sW tW + 400 * (t * L * (W + 1)) + 400

/-- The array after the step. -/
noncomputable def expandOut (A : List Bool) (wt : List (List Bool)) (s t m p w W L : ℕ) : List Bool :=
  msbArray ((LineApply.outs wt ((cut w ((cut (2 * t * w) A).map (Rules.fit (2 * s * w))).flatten).map List.reverse)
    s t m p w W L).map (floorWord w))

theorem sigIn_arr (wt arr : List (List Bool)) (s t m p w W L : ℕ) (sW tW : List Bool) (i : Fin (31 + 91))
    (hi : i ≠ Fin.castAdd 91 22) :
    LineAPrim.sigIn wt arr s t m p w W L sW tW i = LineAPrim.sigIn wt [] s t m p w W L sW tW i := by
  induction i using Fin.addCases with
  | left j =>
    have hj : j ≠ 22 := fun e => hi (by rw [e])
    simp only [LineAPrim.sigIn, Fin.addCases_left]
    fin_cases j <;> simp at hj ⊢
  | right j => simp [LineAPrim.sigIn]

theorem sigOut_eq (wt arr : List (List Bool)) (s t m p w W L : ℕ) (sW tW : List Bool) (i : Fin (31 + 91))
    (h0 : i ≠ Fin.castAdd 91 0) (h22 : i ≠ Fin.castAdd 91 22) (h29 : i ≠ Fin.castAdd 91 29) :
    LineAPrim.sigOut wt arr s t m p w W L sW tW i = LineAPrim.sigIn wt [] s t m p w W L sW tW i := by
  induction i using Fin.addCases with
  | left j =>
    have hj0 : j ≠ 0 := fun e => h0 (by rw [e])
    have hj22 : j ≠ 22 := fun e => h22 (by rw [e])
    have hj29 : j ≠ 29 := fun e => h29 (by rw [e])
    simp only [LineAPrim.sigOut, LineAPrim.sigIn, Fin.addCases_left]
    fin_cases j <;> simp at hj0 hj22 hj29 ⊢
  | right j => simp [LineAPrim.sigOut, LineAPrim.sigIn]

theorem aSlot_val (i : Fin (31 + 91)) : (aSlot i).val = i.val := rfl

theorem aSlot_ne {x : Fin EB} (hx : 122 ≤ x.val) (i : Fin (31 + 91)) : aSlot i ≠ x := by
  intro e; have := congrArg Fin.val e; rw [aSlot_val] at this; have := i.isLt; omega


set_option maxHeartbeats 1000000 in
theorem runs_expandStep (σ : Fin EB → WTape) (A : List Bool) (wt : List (List Bool)) (s t m p w W L : ℕ)
    (sW tW : List Bool)
    (hw : 1 ≤ w) (hpw : p ≤ w) (hwW : w ≤ W) (hwt : ∀ x ∈ wt, x.length = w) (hwtl : wt.length = t * (2 * m + 1))
    (hms : m + 1 ≤ s) (hst : s ≤ t) (hs : 0 < s) (hsv : Counter.value sW = s) (htv : Counter.value tW = t)
    (hsl : sW.length ≤ tW.length + 1) (hAl : A.length = L * (2 * t * w))
    (hA : ∀ i, σ (aSlot i) = LineAPrim.sigIn wt [] s t m p w W L sW tW i)
    (hX : σ tX = reg A) (hU : σ tU = reg (ones (2 * t * w))) (hV : σ tV = reg (ones (2 * s * w)))
    (hS1 : σ tS1 = emp) (hS2 : σ tS2 = emp) (hY : σ tY = emp) (hOne : σ tOne = reg [true]) (hZ : σ tZ = emp) :
    Runs (a := a) expandStep σ (· = Function.update (Function.update σ 0 emp) tX
      (reg (expandOut A wt s t m p w W L))) (expandBound A wt s t m p w W L sW tW) := by
  -- sizes
  set u := 2 * t * w with hu_def
  set v := 2 * s * w with hv_def
  have hu : 1 ≤ u := by simp only [hu_def]; nlinarith
  have hdA : u ∣ A.length := ⟨L, by rw [hAl]; ring⟩
  have hcutA : ∀ x ∈ cut u A, x.length = u := cut_lengths hu A hdA
  have hLA : (cut u A).length = L := by
    rw [length_cut hu A hdA, hAl, Nat.mul_div_cancel _ (by omega)]
  set R := ((cut u A).map (Rules.fit v)).flatten with hR_def
  have hR : R.length = L * v := by
    have h1 := clen_eq ((cut u A).map (Rules.fit v))
    rw [clen_map_fit, hLA] at h1
    simp only [List.length_map, hLA] at h1
    rw [hR_def]; nlinarith
  have hdR : w ∣ R.length := ⟨L * 2 * s, by rw [hR, hv_def]; ring⟩
  have hcR : ∀ x ∈ cut w R, x.length = w := cut_lengths hw R hdR
  have hlcR : (cut w R).length = 2 * s * L := by
    rw [length_cut hw R hdR, hR, hv_def, show L * (2 * s * w) = (2 * s * L) * w by ring,
      Nat.mul_div_cancel _ (by omega)]
  set arr := (cut w R).map List.reverse with harr_def
  have harr : arr.length = 2 * s * L := by simp [arr, hlcR]
  have harrw : ∀ x ∈ arr, x.length = w := by
    intro x hx; simp only [arr, List.mem_map] at hx; obtain ⟨y, hy, rfl⟩ := hx; simp [hcR y hy]
  -- tapes of the primitive block
  have hAt : ∀ j : Fin 31, σ ⟨j.val, by have := j.isLt; simp [EB]; omega⟩ =
      LineAPrim.sigIn wt [] s t m p w W L sW tW (Fin.castAdd 91 j) := fun j => hA (Fin.castAdd 91 j)
  have h9 : σ 9 = reg (ones w) := by
    have := hA (Fin.castAdd 91 9); simp only [LineAPrim.sigIn, Fin.addCases_left] at this; exact this
  have h17 : σ 17 = reg (ones W) := by
    have := hA (Fin.castAdd 91 17); simp only [LineAPrim.sigIn, Fin.addCases_left] at this; exact this
  have h22 : σ 22 = emp := by
    have := hA (Fin.castAdd 91 22); simp only [LineAPrim.sigIn, Fin.addCases_left] at this; exact this
  have h29 : σ 29 = emp := by
    have := hA (Fin.castAdd 91 29); simp only [LineAPrim.sigIn, Fin.addCases_left] at this; exact this
  -- 1. refit
  set σ1 := Function.update σ tX (reg R)
  have s1 : Runs (a := a) (refit.map fRefit fRefit_inj) σ (· = σ1) _ := (runs_map_upd fRefit fRefit_inj σ
    (runs_refitW (a := a) (v := v) (W := u) hu A (fun x hx => (hcutA x hx).le) (σ ∘ fRefit) (by simp [fRefit, hX])
      (by simp [fRefit, hU]) (by simp [fRefit, hV]) (by simp [fRefit, hS1]) (by simp [fRefit, hS2]))
    σ1 (fun y => by fin_cases y <;> (simp (config := {decide := true}) [σ1, fRefit]; try rfl))
    (fun x hx => Function.update_of_ne (fun e => hx 0 (by rw [e]; rfl)) _ _))
  -- 2. cut into words onto the primitive's array tape
  set σ2 := Function.update σ1 22 ⟨[], arr⟩
  have s2 : Runs (a := a) (toWords.map fIn fIn_inj) σ1 (· = σ2) _ := (runs_map_upd fIn fIn_inj σ1
    (runs_toWordsW (a := a) (W := w) hw R (fun x hx => (hcR x hx).le) (σ1 ∘ fIn)
      (by simp (config := {decide := true}) [fIn, σ1]) (by simp (config := {decide := true}) [fIn, σ1, h9])
      (by simp (config := {decide := true}) [fIn, σ1, h22]) (by simp (config := {decide := true}) [fIn, σ1, hS1]))
    σ2 (fun y => by fin_cases y <;> (simp (config := {decide := true}) [σ2, σ1, fIn]; try rfl))
    (fun x hx => Function.update_of_ne (fun e => hx 2 (by rw [e]; rfl)) _ _))
  -- 3. clear the array tape
  set σ3 := Function.update σ2 tX ⟨[], []⟩
  have s3 := runs_clear (a := a) tX σ2
  -- 4. the line loop
  have hpre : σ3 ∘ aSlot = LineAPrim.sigIn wt arr s t m p w W L sW tW := by
    funext i
    have hne : aSlot i ≠ tX := aSlot_ne (by decide) i
    simp only [Function.comp_apply, σ3, σ2, σ1, Function.update_of_ne hne]
    by_cases h : i = Fin.castAdd 91 22
    · subst h; simp [LineAPrim.sigIn]; rfl
    · have hne' : aSlot i ≠ 22 := fun e => h (Fin.ext (by have := congrArg Fin.val e; rw [aSlot_val] at this; simp [this]))
      rw [Function.update_of_ne hne', Function.update_of_ne hne, hA]
      exact (sigIn_arr _ _ _ _ _ _ _ _ _ _ _ _ h).symm
  set O := LineApply.outs wt arr s t m p w W L with hO_def
  set σ4 := upd σ3 aSlot (LineAPrim.sigOut wt arr s t m p w W L sW tW)
  have s4 : Runs (a := a) (.prim (Prim.lift AxisPrims.aPrim) aSlot aSlot_inj) σ3 (· = σ4)
      (AxisPrims.aCost (σ3 ∘ aSlot)) := by
    have hp : AxisPrims.APre (σ3 ∘ aSlot) :=
      ⟨wt, arr, s, t, m, p, w, W, L, sW, tW, hpre, hw, hpw, hwW, hwt, hwtl, harr, harrw, hms, hst, hs, hsv, htv, hsl⟩
    refine ⟨_, _, Exec.prim (P := Prim.lift AxisPrims.aPrim) hp, ?_, le_rfl⟩
    show upd σ3 aSlot (AxisPrims.aSem (σ3 ∘ aSlot)) = σ4
    rw [hpre, (AxisPrims.aSem_sigIn wt arr s t m p w W L sW tW htv).1]
  have hσ4a : ∀ j : Fin 31, σ4 (aSlot (Fin.castAdd 91 j)) = LineAPrim.sigOut wt arr s t m p w W L sW tW
      (Fin.castAdd 91 j) := fun j => upd_slot σ3 aSlot_inj _ _
  have hσ4b : ∀ x : Fin EB, 122 ≤ x.val → σ4 x = σ3 x := fun x hx => upd_other _ _ _ _ (aSlot_ne hx)
  have g29 : σ4 29 = reg (msbArray O) := by
    have := hσ4a 29; simp only [LineAPrim.sigOut, Fin.addCases_left] at this; exact this
  have g17 : σ4 17 = reg (ones W) := by
    have := hσ4a 17; simp only [LineAPrim.sigOut, Fin.addCases_left] at this; exact this
  have g9 : σ4 9 = reg (ones w) := by
    have := hσ4a 9; simp only [LineAPrim.sigOut, Fin.addCases_left] at this; exact this
  have hW1 : 1 ≤ W := by omega
  have hOl : O.length = 2 * t * L := LineApply.outs_length _ _ _ _ _ _ _ _ _
  have hOw : ∀ x ∈ O, x.length = W := LineAPrim.outs_width _ _ _ _ _ _ _ _ hwW _
  have hMl : (msbArray O).length = O.length * W := by
    rw [msbArray, List.length_flatten, List.map_map]
    rw [List.map_congr_left (g := fun _ => W) (fun x hx => by simp [hOw x hx])]
    simp
  have hdM : W ∣ (msbArray O).length := ⟨O.length, by rw [hMl]; ring⟩
  -- 5. cut the output into words
  set σ5 := Function.update σ4 tY ⟨[], O⟩
  have s5 : Runs (a := a) (toWords.map fOut fOut_inj) σ4 (· = σ5) _ := (runs_map_upd fOut fOut_inj σ4
    (runs_toWordsW (a := a) (W := W) hW1 (msbArray O) (fun x hx => (cut_lengths hW1 _ hdM x hx).le) (σ4 ∘ fOut)
      (by simp [fOut, g29]) (by simp [fOut, g17])
      (by simp only [Function.comp_apply, fOut]; rw [hσ4b _ (by decide)]; simp (config := {decide := true}) [σ3, σ2, σ1, hY])
      (by simp only [Function.comp_apply, fOut]; rw [hσ4b _ (by decide)]; simp (config := {decide := true}) [σ3, σ2, σ1, hS1]))
    σ5 (fun y => by
      fin_cases y <;> simp (config := {decide := true}) [σ5, fOut, cut_msbArray hW1 O hOw])
    (fun x hx => Function.update_of_ne (fun e => hx 2 (by rw [e]; rfl)) _ _))
  -- 6. clear the output tape
  set σ6 := Function.update σ5 29 ⟨[], []⟩
  have s6 := runs_clear (a := a) 29 σ5
  -- 7. floor every word
  set F := O.map (floorWord w) with hF_def
  set σ7 := Function.update (Function.update σ6 tY ⟨O.reverse ++ [], []⟩) tZ ⟨F.reverse ++ [], []⟩
  have s7 : Runs (a := a) (floorLoop.map fFloor fFloor_inj) σ6 (· = σ7) _ := (runs_map_upd fFloor fFloor_inj σ6
    (runs_floorLoop (a := a) (w := w) (W := W) O (σ6 ∘ fFloor) [] [] (fun x hx => (hOw x hx).le)
      (by simp only [Function.comp_apply, fFloor]; simp (config := {decide := true}) [σ6, σ5];
          rw [hσ4b _ (by decide)]; simp (config := {decide := true}) [σ3, σ2, σ1, hOne])
      (by simp only [Function.comp_apply, fFloor]; simp (config := {decide := true}) [σ6, σ5, g9])
      (by simp only [Function.comp_apply, fFloor]; simp (config := {decide := true}) [σ6, σ5];
          rw [hσ4b _ (by decide)]; simp (config := {decide := true}) [σ3, σ2, σ1, hS1])
      (by simp (config := {decide := true}) [fFloor, σ6, σ5])
      (by simp only [Function.comp_apply, fFloor]; simp (config := {decide := true}) [σ6, σ5];
          rw [hσ4b _ (by decide)]; simp (config := {decide := true}) [σ3, σ2, σ1, hZ]; rfl))
    σ7 (fun y => by fin_cases y <;> simp (config := {decide := true}) [σ7, fFloor, hF_def])
    (fun x hx => by
      simp only [σ7]
      rw [Function.update_of_ne (fun e => hx 4 (by rw [e]; rfl)), Function.update_of_ne (fun e => hx 0 (by rw [e]; rfl))]))
  -- 8, 9. clear the word list, rewind the floored list
  set σ8 := Function.update σ7 tY ⟨[], []⟩
  have s8 := runs_clear (a := a) tY σ7
  set σ9 := Function.update σ8 tZ ⟨[], (σ8 tZ).left.reverse ++ (σ8 tZ).right⟩
  have s9 := runs_rewind (a := a) tZ σ8
  have g9Z : σ9 tZ = ⟨[], F⟩ := by simp (config := {decide := true}) [σ9, σ8, σ7]
  -- 10. join the floored words
  have hFw : ∀ x ∈ F, x.length ≤ w := by
    intro x hx; simp only [F, List.mem_map] at hx; obtain ⟨y, -, rfl⟩ := hx; simp [floorWord]
  set σ10 := Function.update (Function.update σ9 tX (reg (F.map List.reverse).flatten)) tZ emp
  have s10 : Runs (a := a) (fromWords.map fJoin fJoin_inj) σ9 (· = σ10) _ := (runs_map_upd fJoin fJoin_inj σ9
    (runs_fromWords (a := a) (W := w) F hFw (σ9 ∘ fJoin)
      (by simp only [Function.comp_apply, fJoin]; simp (config := {decide := true}) [σ9, σ8, σ7, σ6, σ5];
          rw [hσ4b _ (by decide)]; simp (config := {decide := true}) [σ3]; rfl)
      (by simp only [Function.comp_apply, fJoin]; exact g9Z)
      (by simp only [Function.comp_apply, fJoin]; simp (config := {decide := true}) [σ9, σ8, σ7, σ6, σ5];
          rw [hσ4b _ (by decide)]; simp (config := {decide := true}) [σ3, σ2, σ1, hS1]))
    σ10 (fun y => by fin_cases y <;> simp (config := {decide := true}) [σ10, fJoin])
    (fun x hx => by
      simp only [σ10]
      rw [Function.update_of_ne (fun e => hx 2 (by rw [e]; rfl)), Function.update_of_ne (fun e => hx 0 (by rw [e]; rfl))]))
  refine (Runs.then s1 (Runs.then s2 (Runs.then s3 (Runs.then s4 (Runs.then s5 (Runs.then s6
    (Runs.then s7 (Runs.then s8 (Runs.then s9 s10))))))))).mono (fun σ' e => ?_) ?_
  swap
  · have c4 : AxisPrims.aCost (σ3 ∘ aSlot) = LineAPrim.progBound wt arr s t m p w W L sW tW := by
      rw [hpre]; exact (AxisPrims.aSem_sigIn wt arr s t m p w W L sW tW htv).2
    rw [c4]
    simp (config := {decide := true}) only [σ8, σ7, σ6, σ5, σ2, σ1, Function.update_self,
      Function.update_of_ne, ne_eq, WTape.words, List.append_nil]
    have hFl : F.length = O.length := by simp [F]
    have hFw' : ∀ x ∈ F, x.length = w := by
      intro x hx; simp only [F, List.mem_map] at hx; obtain ⟨y, -, rfl⟩ := hx; simp [floorWord]
    have hcM : (cut W (msbArray O)).length = O.length := by
      rw [length_cut hW1 _ hdM, hMl, Nat.mul_div_cancel _ (by omega)]
    simp only [clen_reverse]
    rw [g29, hLA, hlcR, hR, hcM, hMl, clen_uniform W O hOw,
      clen_uniform w F hFw', hFl, hOl, hAl]
    simp only [reg, List.reverse_nil, List.nil_append, clen_cons, clen_nil, expandBound, expandArr]
    have hsw : s * w ≤ t * W := Nat.mul_le_mul hst hwW
    have htw : t * w ≤ t * W := Nat.mul_le_mul_left _ hwW
    have ht1 : 1 ≤ t := by omega
    have e1 : L * (s * w) ≤ L * (t * W) := Nat.mul_le_mul_left _ hsw
    have e2 : L * (t * w) ≤ L * (t * W) := Nat.mul_le_mul_left _ htw
    have e3 : L * s ≤ L * t := Nat.mul_le_mul_left _ hst
    have e4 : L ≤ L * t := Nat.le_mul_of_pos_right _ ht1
    simp only [hu_def, hv_def]
    nlinarith
  rw [e]
  funext x
  by_cases e1 : x = tX
  · subst e1; simp (config := {decide := true}) [σ10, expandOut, msbArray, hF_def, hO_def, harr_def, hR_def]; rfl
  by_cases e2 : x = tZ
  · subst e2; simp (config := {decide := true}) [σ10, hZ]
  have q10 : σ10 x = σ9 x := by simp only [σ10]; rw [Function.update_of_ne e2, Function.update_of_ne e1]
  by_cases e3 : x = tY
  · subst e3; rw [q10]; simp (config := {decide := true}) [σ9, σ8, hY]; rfl
  by_cases e4 : x = 29
  · subst e4; rw [q10]; simp (config := {decide := true}) [σ9, σ8, σ7, σ6, h29]; rfl
  have q4 : σ10 x = σ4 x := by
    rw [q10]; simp only [σ9, σ8, σ7, σ6, σ5]
    rw [Function.update_of_ne e2, Function.update_of_ne e3, Function.update_of_ne e2, Function.update_of_ne e3,
      Function.update_of_ne e4, Function.update_of_ne e3]
  rw [q4, Function.update_of_ne e1]
  by_cases hx : x.val < 122
  · have hxi : x = aSlot ⟨x.val, hx⟩ := Fin.ext rfl
    rw [hxi]; simp only [σ4]; rw [upd_slot σ3 aSlot_inj]
    by_cases e0 : (⟨x.val, hx⟩ : Fin (31 + 91)) = Fin.castAdd 91 0
    · rw [e0, show aSlot (Fin.castAdd 91 0) = 0 from rfl, Function.update_self]
      simp only [LineAPrim.sigOut, Fin.addCases_left]; rfl
    · have hx0 : aSlot ⟨x.val, hx⟩ ≠ 0 := fun e => e0 (Fin.ext (by have := congrArg Fin.val e; rw [aSlot_val] at this; simpa using this))
      rw [Function.update_of_ne hx0, hA]
      by_cases e22 : (⟨x.val, hx⟩ : Fin (31 + 91)) = Fin.castAdd 91 22
      · rw [e22]; simp only [LineAPrim.sigOut, LineAPrim.sigIn, Fin.addCases_left]; simp; rfl
      · exact sigOut_eq _ _ _ _ _ _ _ _ _ _ _ _ e0 e22 (fun e => e4 (Fin.ext (by have := congrArg Fin.val e; simp at this; rw [this]; rfl)))
  · push Not at hx
    have hx0 : x ≠ 0 := fun e => by rw [e] at hx; exact absurd hx (by decide)
    rw [Function.update_of_ne hx0, hσ4b x hx]
    have hx22 : x ≠ 22 := fun e => by rw [e] at hx; exact absurd hx (by decide)
    simp only [σ3, σ2, σ1]
    rw [Function.update_of_ne e1, Function.update_of_ne hx22, Function.update_of_ne e1]

/-! ### The compression bank -/

/-- Tapes `0 … 139`: the `B̃₀` primitive; then the array, the two line widths and two scratch tapes. -/
abbrev CB := 145

abbrev cX : Fin CB := 140
abbrev cU : Fin CB := 141
abbrev cV : Fin CB := 142
abbrev cS1 : Fin CB := 143
abbrev cS2 : Fin CB := 144

def bSlot : Fin (49 + 91) → Fin CB := Fin.castLE (by norm_num)
theorem bSlot_inj : Function.Injective bSlot := Fin.castLE_injective _
theorem bSlot_val (i : Fin (49 + 91)) : (bSlot i).val = i.val := rfl
theorem bSlot_ne {x : Fin CB} (hx : 140 ≤ x.val) (i : Fin (49 + 91)) : bSlot i ≠ x := by
  intro e; have := congrArg Fin.val e; rw [bSlot_val] at this; have := i.isLt; omega

def gIn : Fin 4 → Fin CB := ![cX, 9, 42, cS1]
def gPad : Fin 5 → Fin CB := ![47, cU, cV, cS1, cS2]
theorem gIn_inj : Function.Injective gIn := by decide
theorem gPad_inj : Function.Injective gPad := by decide

/-- Cut into words, apply `B̃₀` line by line, pad every line back to `t` entries. -/
noncomputable def compressStep : Cmd a CB :=
  .seq (toWords.map gIn gIn_inj) <| .seq (clear cX) <|
  .seq (.prim (Prim.lift AxisPrims.bPrim) bSlot bSlot_inj) <| .seq (refit.map gPad gPad_inj) (regMove 47 cX (by decide))

/-- The array handed to the `B̃₀` loop. -/
def compressArr (A : List Bool) (w : ℕ) : List (List Bool) := (cut w A).map List.reverse

/-- The array after the step. -/
noncomputable def compressOut (A : List Bool) (wtE wtH wtD zeros : List (List Bool)) (s t m p w W L : ℕ) : List Bool :=
  ((cut (2 * s * w) (msbArray (B0Line.b0Outs (compressArr A w) wtE wtH wtD zeros s t m p w W L))).map
    (Rules.fit (2 * t * w))).flatten

/-- The cost of one compression axis. -/
noncomputable def compressBound (A : List Bool) (wtE wtH wtD zeros : List (List Bool)) (s t m p w W L : ℕ)
    (sW tW : List Bool) : ℕ :=
  B0Prim.progBound (compressArr A w) wtE wtH wtD zeros s t m p w W L sW tW + 400 * (t * L * (W + 1)) + 400

theorem bSigIn_arr (arr wtE wtH wtD zeros : List (List Bool)) (s t m p w W L : ℕ) (sW tW : List Bool)
    (i : Fin (49 + 91)) (hi : i ≠ Fin.castAdd 91 42) :
    B0Prim.sigIn arr wtE wtH wtD zeros s t m p w W L sW tW i =
      B0Prim.sigIn [] wtE wtH wtD zeros s t m p w W L sW tW i := by
  induction i using Fin.addCases with
  | left j =>
    have hj : j ≠ 42 := fun e => hi (by rw [e])
    simp only [B0Prim.sigIn, Fin.addCases_left]
    fin_cases j <;> simp at hj ⊢
  | right j => simp [B0Prim.sigIn]

/-- Outside the consumed inputs and the output, `sigOut` agrees with `sigIn`. -/
theorem bSigOut_eq (arr wtE wtH wtD zeros : List (List Bool)) (s t m p w W L : ℕ) (sW tW : List Bool)
    (i : Fin (49 + 91)) (h0 : i ≠ Fin.castAdd 91 0) (h27 : i ≠ Fin.castAdd 91 27) (h28 : i ≠ Fin.castAdd 91 28)
    (h33 : i ≠ Fin.castAdd 91 33) (h42 : i ≠ Fin.castAdd 91 42) (h47 : i ≠ Fin.castAdd 91 47) :
    B0Prim.sigOut arr wtE wtH wtD zeros s t m p w W L sW tW i =
      B0Prim.sigIn [] wtE wtH wtD zeros s t m p w W L sW tW i := by
  induction i using Fin.addCases with
  | left j =>
    have hj0 : j ≠ 0 := fun e => h0 (by rw [e])
    have hj27 : j ≠ 27 := fun e => h27 (by rw [e])
    have hj28 : j ≠ 28 := fun e => h28 (by rw [e])
    have hj33 : j ≠ 33 := fun e => h33 (by rw [e])
    have hj42 : j ≠ 42 := fun e => h42 (by rw [e])
    have hj47 : j ≠ 47 := fun e => h47 (by rw [e])
    simp only [B0Prim.sigOut, B0Prim.sigIn, Fin.addCases_left]
    fin_cases j <;> simp at hj0 hj27 hj28 hj33 hj42 hj47 ⊢
  | right j => simp [B0Prim.sigOut, B0Prim.sigIn]

theorem b0Outs_length (arr wtE wtH wtD zeros : List (List Bool)) (s t m p w W : ℕ) (hz : zeros.length = 2 * s) :
    ∀ L, (B0Line.b0Outs arr wtE wtH wtD zeros s t m p w W L).length = 2 * s * L
  | 0 => rfl
  | L + 1 => by
    rw [B0Line.b0Outs, List.length_append, b0Outs_length arr wtE wtH wtD zeros s t m p w W hz L]
    simp [B0Line.b0Out, B0Words.oneStep, NeumannWords.nextWords_length, hz]; ring

set_option maxHeartbeats 1000000 in
theorem runs_compressStep (σ : Fin CB → WTape) (A : List Bool) (wtE wtH wtD zeros : List (List Bool))
    (s t m p w W L : ℕ) (sW tW : List Bool)
    (hw : 1 ≤ w) (hpw : p ≤ w) (hwW : w ≤ W) (hp2 : 2 ≤ p)
    (hwtE : ∀ x ∈ wtE, x.length = w) (hwtEl : wtE.length = s * (2 * m + 1)) (hwtH : ∀ x ∈ wtH, x.length = w)
    (hwtHl : wtH.length = s * (2 * 0 + 1)) (hwtD : ∀ x ∈ wtD, x.length = w) (hwtDl : wtD.length = s * (2 * 0 + 1))
    (hz : zeros.length = 2 * s) (hzw : ∀ x ∈ zeros, x.length = w) (hms : m + 1 ≤ s) (hs : 0 < s) (hst : s < t)
    (hsv : Counter.value sW = s) (htv : Counter.value tW = s) (hsl : sW.length ≤ tW.length + 1)
    (hAl : A.length = L * (2 * t * w))
    (hB : ∀ i, σ (bSlot i) = B0Prim.sigIn [] wtE wtH wtD zeros s t m p w W L sW tW i)
    (hX : σ cX = reg A) (hU : σ cU = reg (ones (2 * s * w))) (hV : σ cV = reg (ones (2 * t * w)))
    (hS1 : σ cS1 = emp) (hS2 : σ cS2 = emp) :
    Runs (a := a) compressStep σ (· = Function.update (Function.update (Function.update (Function.update
      (Function.update σ 0 emp) 27 emp) 28 emp) 33 emp) cX (reg (compressOut A wtE wtH wtD zeros s t m p w W L)))
      (compressBound A wtE wtH wtD zeros s t m p w W L sW tW) := by
  have hdA : w ∣ A.length := ⟨L * 2 * t, by rw [hAl]; ring⟩
  have hcA : ∀ x ∈ cut w A, x.length = w := cut_lengths hw A hdA
  have hlcA : (cut w A).length = 2 * t * L := by
    rw [length_cut hw A hdA, hAl, show L * (2 * t * w) = (2 * t * L) * w by ring, Nat.mul_div_cancel _ (by omega)]
  set arr := compressArr A w with harr_def
  have harr : arr.length = 2 * t * L := by simp [arr, compressArr, hlcA]
  have harrw : ∀ x ∈ arr, x.length = w := by
    intro x hx; simp only [arr, compressArr, List.mem_map] at hx; obtain ⟨y, hy, rfl⟩ := hx; simp [hcA y hy]
  have h9 : σ 9 = reg (ones w) := by
    have := hB (Fin.castAdd 91 9); simp only [B0Prim.sigIn, Fin.addCases_left] at this; exact this
  have h42 : σ 42 = emp := by
    have := hB (Fin.castAdd 91 42); simp only [B0Prim.sigIn, Fin.addCases_left] at this; exact this
  have h47 : σ 47 = emp := by
    have := hB (Fin.castAdd 91 47); simp only [B0Prim.sigIn, Fin.addCases_left] at this; exact this
  -- 1. cut into words
  set σ1 := Function.update σ 42 ⟨[], arr⟩
  have s1 : Runs (a := a) (toWords.map gIn gIn_inj) σ (· = σ1) _ := (runs_map_upd gIn gIn_inj σ
    (runs_toWordsW (a := a) (W := w) hw A (fun x hx => (hcA x hx).le) (σ ∘ gIn)
      (by simp [gIn, hX]) (by simp [gIn, h9]) (by simp [gIn, h42]) (by simp [gIn, hS1]))
    σ1 (fun y => by fin_cases y <;> (simp (config := {decide := true}) [σ1, gIn]; try rfl))
    (fun x hx => Function.update_of_ne (fun e => hx 2 (by rw [e]; rfl)) _ _))
  -- 2. clear the array tape
  set σ2 := Function.update σ1 cX ⟨[], []⟩
  have s2 := runs_clear (a := a) cX σ1
  -- 3. the line loop
  have hpre : σ2 ∘ bSlot = B0Prim.sigIn arr wtE wtH wtD zeros s t m p w W L sW tW := by
    funext i
    have hne : bSlot i ≠ cX := bSlot_ne (by decide) i
    simp only [Function.comp_apply, σ2, σ1, Function.update_of_ne hne]
    by_cases h : i = Fin.castAdd 91 42
    · subst h; simp [B0Prim.sigIn]; rfl
    · have hne' : bSlot i ≠ 42 := fun e => h (Fin.ext (by have := congrArg Fin.val e; rw [bSlot_val] at this; simp [this]))
      rw [Function.update_of_ne hne', hB]
      exact (bSigIn_arr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h).symm
  set Ob := B0Line.b0Outs arr wtE wtH wtD zeros s t m p w W L with hOb_def
  set σ3 := upd σ2 bSlot (B0Prim.sigOut arr wtE wtH wtD zeros s t m p w W L sW tW)
  have s3 : Runs (a := a) (.prim (Prim.lift AxisPrims.bPrim) bSlot bSlot_inj) σ2 (· = σ3)
      (AxisPrims.bCost (σ2 ∘ bSlot)) := by
    have hp : AxisPrims.BPre (σ2 ∘ bSlot) :=
      ⟨arr, wtE, wtH, wtD, zeros, s, t, m, p, w, W, L, sW, tW, hpre, hw, hpw, hwW, harr, harrw, hp2, hwtE, hwtEl,
        hwtH, hwtHl, hwtD, hwtDl, hz, hzw, hms, hs, hst, hsv, htv, hsl⟩
    refine ⟨_, _, Exec.prim (P := Prim.lift AxisPrims.bPrim) hp, ?_, le_rfl⟩
    show upd σ2 bSlot (AxisPrims.bSem (σ2 ∘ bSlot)) = σ3
    rw [hpre, (AxisPrims.bSem_sigIn arr wtE wtH wtD zeros s t m p w W L sW tW).1]
  have hσ3a : ∀ j : Fin 49, σ3 (bSlot (Fin.castAdd 91 j)) = B0Prim.sigOut arr wtE wtH wtD zeros s t m p w W L sW tW
      (Fin.castAdd 91 j) := fun j => upd_slot σ2 bSlot_inj _ _
  have hσ3b : ∀ x : Fin CB, 140 ≤ x.val → σ3 x = σ2 x := fun x hx => upd_other _ _ _ _ (bSlot_ne hx)
  have g47 : σ3 47 = reg (msbArray Ob) := by
    have := hσ3a 47; simp only [B0Prim.sigOut, Fin.addCases_left] at this; exact this
  have hOl : Ob.length = 2 * s * L := b0Outs_length _ _ _ _ _ _ _ _ _ _ _ hz L
  have hOw : ∀ x ∈ Ob, x.length = w := B0Prim.b0Outs_width _ _ _ _ _ _ _ _ _ _ _ hzw L
  have hMl : (msbArray Ob).length = L * (2 * s * w) := by
    rw [msbArray, List.length_flatten, List.map_map]
    rw [List.map_congr_left (g := fun _ => w) (fun x hx => by simp [hOw x hx])]
    simp [hOl]; ring
  have hsw : 1 ≤ 2 * s * w := by nlinarith
  have hdM : 2 * s * w ∣ (msbArray Ob).length := ⟨L, by rw [hMl]; ring⟩
  have hcM : ∀ x ∈ cut (2 * s * w) (msbArray Ob), x.length = 2 * s * w := cut_lengths hsw _ hdM
  have hlcM : (cut (2 * s * w) (msbArray Ob)).length = L := by
    rw [length_cut hsw _ hdM, hMl, Nat.mul_div_cancel _ (by omega)]
  -- 4. pad every line
  set P := ((cut (2 * s * w) (msbArray Ob)).map (Rules.fit (2 * t * w))).flatten with hP_def
  set σ4 := Function.update σ3 47 (reg P)
  have s4 : Runs (a := a) (refit.map gPad gPad_inj) σ3 (· = σ4) _ := (runs_map_upd gPad gPad_inj σ3
    (runs_refitW (a := a) (v := 2 * t * w) (W := 2 * s * w) hsw (msbArray Ob) (fun x hx => (hcM x hx).le) (σ3 ∘ gPad)
      (by simp [gPad, g47])
      (by simp only [Function.comp_apply, gPad]; rw [hσ3b _ (by decide)]; simp (config := {decide := true}) [σ2, σ1, hU])
      (by simp only [Function.comp_apply, gPad]; rw [hσ3b _ (by decide)]; simp (config := {decide := true}) [σ2, σ1, hV])
      (by simp only [Function.comp_apply, gPad]; rw [hσ3b _ (by decide)]; simp (config := {decide := true}) [σ2, σ1, hS1])
      (by simp only [Function.comp_apply, gPad]; rw [hσ3b _ (by decide)]; simp (config := {decide := true}) [σ2, σ1, hS2]))
    σ4 (fun y => by fin_cases y <;> (simp (config := {decide := true}) [σ4, gPad]; try rfl))
    (fun x hx => Function.update_of_ne (fun e => hx 0 (by rw [e]; rfl)) _ _))
  -- 5. move the result to the array tape
  have s5 := runs_regMove (a := a) (show (47 : Fin CB) ≠ cX by decide) σ4 (w := P) (by simp [σ4])
    (by simp only [σ4]; rw [Function.update_of_ne (by decide), hσ3b _ (by decide)]; simp [σ2]; rfl)
  refine (Runs.then s1 (Runs.then s2 (Runs.then s3 (Runs.then s4 s5)))).mono (fun σ' e => ?_) ?_
  swap
  · have c3 : AxisPrims.bCost (σ2 ∘ bSlot) = B0Prim.progBound arr wtE wtH wtD zeros s t m p w W L sW tW := by
      rw [hpre]; exact (AxisPrims.bSem_sigIn arr wtE wtH wtD zeros s t m p w W L sW tW).2
    rw [c3]
    have hPl : P.length = L * (2 * t * w) := by
      have h1 := clen_eq ((cut (2 * s * w) (msbArray Ob)).map (Rules.fit (2 * t * w)))
      rw [clen_map_fit, hlcM] at h1
      simp only [List.length_map, hlcM] at h1
      rw [hP_def]; nlinarith
    simp (config := {decide := true}) only [σ1, Function.update_of_ne, ne_eq, WTape.words]
    rw [hlcA, hlcM, hMl, hPl, hAl, hX]
    simp only [reg, List.reverse_nil, List.nil_append, clen_cons, clen_nil, compressBound, hAl]
    have hsw' : s * w ≤ t * W := Nat.mul_le_mul hst.le hwW
    have htw : t * w ≤ t * W := Nat.mul_le_mul_left _ hwW
    have e1 : L * (s * w) ≤ L * (t * W) := Nat.mul_le_mul_left _ hsw'
    have e2 : L * (t * w) ≤ L * (t * W) := Nat.mul_le_mul_left _ htw
    have e4 : L ≤ L * t := Nat.le_mul_of_pos_right _ (by omega)
    nlinarith
  rw [e]
  funext x
  by_cases e1 : x = cX
  · subst e1; simp (config := {decide := true}) [compressOut, hP_def, hOb_def, harr_def]
  by_cases e47 : x = 47
  · subst e47; simp (config := {decide := true}) [h47]
  rw [Function.update_of_ne e1, Function.update_of_ne e47, Function.update_of_ne e1]
  simp only [σ4]; rw [Function.update_of_ne e47]
  by_cases hx : x.val < 140
  · have hxi : x = bSlot ⟨x.val, hx⟩ := Fin.ext rfl
    rw [hxi]; simp only [σ3]; rw [upd_slot σ2 bSlot_inj]
    by_cases e0 : (⟨x.val, hx⟩ : Fin (49 + 91)) = Fin.castAdd 91 0
    · rw [e0]; simp only [B0Prim.sigOut, Fin.addCases_left]
      rw [show bSlot (Fin.castAdd 91 0) = 0 from rfl]; simp (config := {decide := true})
    by_cases e27 : (⟨x.val, hx⟩ : Fin (49 + 91)) = Fin.castAdd 91 27
    · rw [e27]; simp only [B0Prim.sigOut, Fin.addCases_left]
      rw [show bSlot (Fin.castAdd 91 27) = 27 from rfl]; simp (config := {decide := true})
    by_cases e28 : (⟨x.val, hx⟩ : Fin (49 + 91)) = Fin.castAdd 91 28
    · rw [e28]; simp only [B0Prim.sigOut, Fin.addCases_left]
      rw [show bSlot (Fin.castAdd 91 28) = 28 from rfl]; simp (config := {decide := true})
    by_cases e33 : (⟨x.val, hx⟩ : Fin (49 + 91)) = Fin.castAdd 91 33
    · rw [e33]; simp only [B0Prim.sigOut, Fin.addCases_left]
      rw [show bSlot (Fin.castAdd 91 33) = 33 from rfl]; simp (config := {decide := true})
    have n0 : bSlot ⟨x.val, hx⟩ ≠ 0 := fun e => e0 (Fin.ext (by have := congrArg Fin.val e; rw [bSlot_val] at this; simpa using this))
    have n27 : bSlot ⟨x.val, hx⟩ ≠ 27 := fun e => e27 (Fin.ext (by have := congrArg Fin.val e; rw [bSlot_val] at this; simp at this ⊢; omega))
    have n28 : bSlot ⟨x.val, hx⟩ ≠ 28 := fun e => e28 (Fin.ext (by have := congrArg Fin.val e; rw [bSlot_val] at this; simp at this ⊢; omega))
    have n33 : bSlot ⟨x.val, hx⟩ ≠ 33 := fun e => e33 (Fin.ext (by have := congrArg Fin.val e; rw [bSlot_val] at this; simp at this ⊢; omega))
    rw [Function.update_of_ne n33, Function.update_of_ne n28, Function.update_of_ne n27, Function.update_of_ne n0, hB]
    by_cases e42 : (⟨x.val, hx⟩ : Fin (49 + 91)) = Fin.castAdd 91 42
    · rw [e42]; simp only [B0Prim.sigOut, B0Prim.sigIn, Fin.addCases_left]; simp; rfl
    · exact bSigOut_eq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ e0 e27 e28 e33 e42
        (fun e => e47 (Fin.ext (by have := congrArg Fin.val e; simp at this; rw [this]; rfl)))
  · push Not at hx
    have nk : ∀ k : Fin CB, k.val < 140 → x ≠ k := fun k hk e => by rw [e] at hx; omega
    rw [hσ3b x hx]
    simp only [σ2, σ1]
    rw [Function.update_of_ne e1, Function.update_of_ne (nk 42 (by decide)), Function.update_of_ne (nk 33 (by decide)),
      Function.update_of_ne (nk 28 (by decide)), Function.update_of_ne (nk 27 (by decide)),
      Function.update_of_ne (nk 0 (by decide))]

end IntegerMultBounds.Resampling.AxisStep
