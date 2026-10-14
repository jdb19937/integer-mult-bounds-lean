module

public import IntegerMultBounds.Schoenhage.SigmaRows

/-! The axis rows of the §6 exponent tables, written on tapes. Values are
unary words; the bottom slots of an axis add `D` per slot, the slots of a
chunk group add one per slot, the next chunk group starts `DK` higher, and the
next axis starts one lower at the bottom and `K` lower in the chunks. One word
program with four tick tapes (axes, bottom slots, chunk groups, slots of a
group) writes every row, axis after axis (`runs_rowsGen`). -/

@[expose] public section

set_option maxRecDepth 100000

namespace IntegerMultBounds.Schoenhage

open Machine Strm

namespace SigmaRowsTape

/-! ### The bank -/

/-- One tick per axis. -/
abbrev gAx : Fin 15 := 0
/-- One tick per bottom slot. -/
abbrev gBt : Fin 15 := 1
/-- One tick per chunk group. -/
abbrev gQt : Fin 15 := 2
/-- One tick per slot of a chunk group. -/
abbrev gKt : Fin 15 := 3
/-- `ones D`. -/
abbrev gD : Fin 15 := 4
/-- `ones (D K)`. -/
abbrev gDK : Fin 15 := 5
/-- `ones K`. -/
abbrev gK : Fin 15 := 6
/-- `ones 1`. -/
abbrev gOne : Fin 15 := 7
/-- The axis's bottom start. -/
abbrev gA : Fin 15 := 8
/-- The axis's chunk start. -/
abbrev gB : Fin 15 := 9
/-- The current value. -/
abbrev gV : Fin 15 := 10
/-- The current chunk group's start. -/
abbrev gU : Fin 15 := 11
/-- The rows. -/
abbrev gO : Fin 15 := 12
/-- Scratch. -/
abbrev gS : Fin 15 := 13
/-- The junk tape. -/
abbrev gJ : Fin 15 := 14

/-- A unary value with the head past it. -/
def endv (x : ℕ) : WTape := ⟨[ones x], []⟩

/-- Ticks, the head at the first. -/
def ticks (n : ℕ) : WTape := ⟨[], List.replicate n []⟩

/-! ### The program -/

/-- Write the current value as a row word. -/
noncomputable def emitV : Cmd 0 15 := .seq (rewind gV) (cpy gV gO (by decide))

/-- Add the constant on `s` to the value on `d`. -/
noncomputable def addTo (s d : Fin 15) (h : s ≠ d) : Cmd 0 15 := .seq (op0 Rules.copy true s d h) (rewind s)

/-- Load the value on `s` into `gV`. -/
noncomputable def loadV (s : Fin 15) (h : s ≠ gV) : Cmd 0 15 :=
  .seq (clear gV) <| .seq (rewind s) (cpy s gV h)

/-- Subtract the constant on `k` from the value on `d`. -/
noncomputable def subFrom (d k : Fin 15) (h1 : d ≠ k) (h2 : d ≠ gS) (h3 : k ≠ gS) (h4 : gS ≠ d) : Cmd 0 15 :=
  .seq (rewind d) <| .seq (op1 Rules.drop false d k gS h1 h2 h3) <| .seq (rewind k) <|
  .seq (clear d) <| .seq (rewind gS) <| .seq (cpy gS d h4) (clear gS)

/-- One bottom slot: write the value, add `D`. -/
noncomputable def bottomStep : Cmd 0 15 :=
  .seq emitV <| .seq (addTo gD gV (by decide)) (skp gBt gJ (by decide))

/-- One slot of a chunk group: write the value, add one. -/
noncomputable def runStep : Cmd 0 15 :=
  .seq emitV <| .seq (addTo gOne gV (by decide)) (skp gKt gJ (by decide))

/-- One chunk group: its `K` slots from its start, then the next start `DK` higher. -/
noncomputable def groupStep : Cmd 0 15 :=
  .seq (loadV gU (by decide)) <| .seq (.loop gKt runStep) <| .seq (rewind gKt) <| .seq (clear gV) <|
  .seq (addTo gDK gU (by decide)) (skp gQt gJ (by decide))

/-- Load the chunk start of the axis. -/
noncomputable def loadU : Cmd 0 15 := .seq (clear gU) <| .seq (rewind gB) (cpy gB gU (by decide))

/-- One axis: its bottom slots, its chunk groups, then the next axis's starts. -/
noncomputable def axisStep : Cmd 0 15 :=
  .seq (loadV gA (by decide)) <| .seq (.loop gBt bottomStep) <| .seq (rewind gBt) <| .seq (clear gV) <|
  .seq loadU <| .seq (.loop gQt groupStep) <| .seq (rewind gQt) <| .seq (clear gU) <|
  .seq (subFrom gA gOne (by decide) (by decide) (by decide) (by decide)) <|
  .seq (subFrom gB gK (by decide) (by decide) (by decide) (by decide)) (skp gAx gJ (by decide))

/-- Every axis row. -/
noncomputable def rowsGen : Cmd 0 15 := .loop gAx axisStep

/-! ### Steps -/

set_option maxHeartbeats 4000000 in
theorem runs_emitV {v : ℕ} (σ : Fin 15 → WTape) (hV : σ gV = endv v) {O : List (List Bool)}
    (hO : σ gO = ⟨O, []⟩) :
    Runs emitV σ (· = Function.update σ gO ⟨ones v :: O, []⟩) (2 * v + 10) := by
  apply Runs.of_wp
  simp only [emitV, cpy, WP, wp_op0, wp_rewind]
  tsimp [hV, hO, endv, Rules.output_copy]
  refine ⟨?_, ?_⟩
  · funext i; fin_cases i <;> first | rfl | tsimp [hV, hO, endv]
  · simp [time_copy]; omega

set_option maxHeartbeats 4000000 in
theorem runs_addTo {s d : Fin 15} (h : s ≠ d) {c v : ℕ} (σ : Fin 15 → WTape) (hs : σ s = reg (ones c))
    (hd : σ d = endv v) :
    Runs (addTo s d h) σ (· = Function.update σ d (endv (v + c))) (2 * c + 10) := by
  apply Runs.of_wp
  simp only [addTo, WP, wp_op0, wp_rewind]
  simp only [Function.update_apply, hs, hd, h, ↓reduceIte, endv, reg, WTape.next_mk,
    WTape.cur_mk, List.headD_cons, List.tail_cons, Rules.output_copy, ↓parse_syms]
  refine ⟨⟨by simp, by simp, by simp, fun _ => ⟨by simp, by simp⟩⟩, ?_, ?_⟩
  · funext i
    simp only [Function.update_apply]
    split_ifs <;> subst_vars <;> simp_all [TwistDescriptors.ones_append, WTape.put, reg, endv]
  · simp [time_copy]; omega

set_option maxHeartbeats 4000000 in
theorem runs_loadV {s : Fin 15} (h : s ≠ gV) {x : ℕ} (σ : Fin 15 → WTape) (hs : σ s = endv x)
    (hV : σ gV = emp) :
    Runs (loadV s h) σ (· = Function.update σ gV (endv x)) (2 * x + 15) := by
  apply Runs.of_wp
  simp only [loadV, cpy, WP, wp_op0, wp_rewind, wp_clear]
  simp only [Function.update_apply, hs, hV, h, h.symm, ↓reduceIte, endv, emp, WTape.next_mk, WTape.cur_mk,
    List.headD_cons, List.tail_cons, Rules.output_copy, ↓parse_syms, List.reverse_cons, List.reverse_nil,
    List.nil_append, List.append_nil]
  refine ⟨⟨by simp, by simp, by simp, by simp⟩, ?_, ?_⟩
  · funext i
    simp only [Function.update_apply]
    split_ifs <;> subst_vars <;> simp_all [WTape.put, endv, emp]
  · simp [time_copy, clen, WTape.words]; omega

set_option maxHeartbeats 4000000 in
theorem runs_subFrom {d k : Fin 15} (h1 : d ≠ k) (h2 : d ≠ gS) (h3 : k ≠ gS) (h4 : gS ≠ d) {x c : ℕ}
    (σ : Fin 15 → WTape) (hd : σ d = endv x) (hk : σ k = reg (ones c)) (hS : σ gS = emp) :
    Runs (subFrom d k h1 h2 h3 h4) σ (· = Function.update σ d (endv (x - c))) (8 * x + 4 * c + 50) := by
  have t1 : time Rules.drop (ones x) (fun _ => ones c) ≤ x + c + 6 :=
    (time_le Rules.drop (ones x) (fun _ => ones c) c (fun _ => by simp)).trans (by simp)
  apply Runs.of_wp
  simp only [subFrom, cpy, WP, wp_op0, wp_op1, wp_rewind, wp_clear]
  simp only [Function.update_apply, hd, hk, hS, h1, h2, h3, h4, h1.symm, h3.symm,
    ↓reduceIte, endv, reg, emp, WTape.next_mk, WTape.cur_mk, List.headD_cons, List.tail_cons,
    Rules.output_copy, Rules.output_drop, ↓parse_syms, List.reverse_cons, List.reverse_nil,
    List.nil_append, List.append_nil, ne_eq, List.cons_ne_nil, not_false_eq_true, true_and]
  refine ⟨by simp, by simp [WTape.put], ?_, ?_⟩
  · funext i
    simp only [Function.update_apply]
    split_ifs <;> subst_vars <;> simp_all [WTape.put, ones, List.drop_replicate, endv, emp, reg]
  · simp only [time_copy, clen, length_ones, List.length_drop, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, WTape.words, WTape.put_false, List.reverse_cons, List.reverse_nil, List.nil_append,
      List.append_nil, List.headD_cons, List.tail_cons, List.length_drop]
    omega

set_option maxHeartbeats 4000000 in
theorem runs_bottomStep {v D : ℕ} (σ : Fin 15 → WTape) (hV : σ gV = endv v) (hD : σ gD = reg (ones D))
    {O L R : List (List Bool)} (hO : σ gO = ⟨O, []⟩) (hBt : σ gBt = ⟨L, [] :: R⟩) (hJ : σ gJ = emp) :
    Runs bottomStep σ (· = Function.update (Function.update (Function.update σ gO ⟨ones v :: O, []⟩)
      gV (endv (v + D))) gBt ⟨[] :: L, R⟩) (2 * v + 2 * D + 30) := by
  have s1 := runs_emitV σ hV hO
  set σ₁ := Function.update σ gO ⟨ones v :: O, []⟩ with hσ₁
  have s2 := runs_addTo (c := D) (v := v) (show gD ≠ gV by decide) σ₁ (by tsimp [hσ₁, hD]) (by tsimp [hσ₁, hV])
  set σ₂ := Function.update σ₁ gV (endv (v + D)) with hσ₂
  have s3 := runs_skp (a := 0) (show gBt ≠ gJ by decide) σ₂ (by tsimp [hσ₂, hσ₁, hBt]) (by tsimp [hσ₂, hσ₁, hJ, emp])
  refine (Runs.then s1 (Runs.then s2 s3)).mono (fun τ e => ?_) ?_
  · rw [e]; funext i; fin_cases i <;> first | rfl | tsimp [hσ₂, hσ₁, hBt]
  · tsimp [hσ₂, hσ₁, hBt]; omega

set_option maxHeartbeats 4000000 in
theorem runs_runStep {v : ℕ} (σ : Fin 15 → WTape) (hV : σ gV = endv v) (hOne : σ gOne = reg (ones 1))
    {O L R : List (List Bool)} (hO : σ gO = ⟨O, []⟩) (hKt : σ gKt = ⟨L, [] :: R⟩) (hJ : σ gJ = emp) :
    Runs runStep σ (· = Function.update (Function.update (Function.update σ gO ⟨ones v :: O, []⟩)
      gV (endv (v + 1))) gKt ⟨[] :: L, R⟩) (2 * v + 32) := by
  have s1 := runs_emitV σ hV hO
  set σ₁ := Function.update σ gO ⟨ones v :: O, []⟩ with hσ₁
  have s2 := runs_addTo (c := 1) (v := v) (show gOne ≠ gV by decide) σ₁ (by tsimp [hσ₁, hOne]) (by tsimp [hσ₁, hV])
  set σ₂ := Function.update σ₁ gV (endv (v + 1)) with hσ₂
  have s3 := runs_skp (a := 0) (show gKt ≠ gJ by decide) σ₂ (by tsimp [hσ₂, hσ₁, hKt]) (by tsimp [hσ₂, hσ₁, hJ, emp])
  refine (Runs.then s1 (Runs.then s2 s3)).mono (fun τ e => ?_) ?_
  · rw [e]; funext i; fin_cases i <;> first | rfl | tsimp [hσ₂, hσ₁, hKt]
  · tsimp [hσ₂, hσ₁, hKt]

/-! ### Loops -/

theorem map_range_succ_rev {α : Type*} (f : ℕ → α) (n : ℕ) (O : List α) :
    ((List.range n).map fun j => f (j + 1)).reverse ++ f 0 :: O = ((List.range (n + 1)).map f).reverse ++ O := by
  rw [List.range_succ_eq_map]; simp

theorem flatMap_range_succ_rev {α : Type*} (g : ℕ → List α) (n : ℕ) (O : List α) :
    ((List.range n).flatMap fun j => g (j + 1)).reverse ++ ((g 0).reverse ++ O) =
      ((List.range (n + 1)).flatMap g).reverse ++ O := by
  rw [List.range_succ_eq_map]; simp [List.flatMap_map]

theorem replicate_cons (n : ℕ) (L : List (List Bool)) :
    List.replicate n [] ++ [] :: L = List.replicate (n + 1) [] ++ L := by
  rw [List.replicate_succ']; simp

set_option maxHeartbeats 8000000 in
/-- The bottom loop writes `v, v + D, …, v + (n-1)D` and leaves the value `v + nD`. -/
theorem runs_bottomLoop {D : ℕ} : ∀ (n v : ℕ) (σ : Fin 15 → WTape) (O L : List (List Bool)),
    σ gBt = ⟨L, List.replicate n []⟩ → σ gV = endv v → σ gD = reg (ones D) → σ gO = ⟨O, []⟩ →
    σ gJ = emp →
    Runs (.loop gBt bottomStep) σ (· = Function.update (Function.update (Function.update σ gO
        ⟨((List.range n).map fun j => ones (v + j * D)).reverse ++ O, []⟩) gV (endv (v + n * D)))
        gBt ⟨List.replicate n [] ++ L, []⟩) (n * (2 * (v + n * D) + 2 * D + 32))
  | 0, v, σ, O, L, hBt, hV, hD, hO, hJ => by
    refine (Runs.loop_done (by simp [hBt]) rfl).mono (fun τ e => ?_) (by simp)
    subst e
    funext i; fin_cases i <;> first | rfl | tsimp [hBt, hV, hO, endv]
  | n + 1, v, σ, O, L, hBt, hV, hD, hO, hJ => by
    have s1 := runs_bottomStep (D := D) σ hV hD hO (show σ gBt = ⟨L, [] :: List.replicate n []⟩ by
      rw [hBt]; rfl) hJ
    set σ₁ := Function.update (Function.update (Function.update σ gO ⟨ones v :: O, []⟩)
      gV (endv (v + D))) gBt ⟨[] :: L, List.replicate n []⟩ with hσ₁
    have ih := runs_bottomLoop (D := D) n (v + D) σ₁ (ones v :: O) ([] :: L) (by tsimp [hσ₁]) (by tsimp [hσ₁])
      (by tsimp [hσ₁, hD]) (by tsimp [hσ₁]) (by tsimp [hσ₁, hJ])
    refine (Runs.loop_step (by simp [hBt]) (s1.mono (fun τ h => by rw [h]; exact ih) le_rfl)).mono
      (fun τ h => ?_) ?_
    · rw [h]
      have e1 := map_range_succ_rev (fun j => ones (v + j * D)) n O
      simp only [zero_mul, add_zero] at e1
      have e2 : (fun j => ones (v + D + j * D)) = fun j => ones (v + (j + 1) * D) := by
        funext j; congr 1; ring
      funext i; fin_cases i <;> first | rfl | tsimp [hσ₁, replicate_cons, e2, e1] <;> ring_nf
    · have : 2 * v + 2 * D + 30 + 2 + n * (2 * (v + D + n * D) + 2 * D + 32) ≤
          (n + 1) * (2 * (v + (n + 1) * D) + 2 * D + 32) := by nlinarith
      omega

set_option maxHeartbeats 8000000 in
/-- The slots of a chunk group: `u, u + 1, …, u + n - 1`, leaving the value `u + n`. -/
theorem runs_runLoop : ∀ (n u : ℕ) (σ : Fin 15 → WTape) (O L : List (List Bool)),
    σ gKt = ⟨L, List.replicate n []⟩ → σ gV = endv u → σ gOne = reg (ones 1) → σ gO = ⟨O, []⟩ →
    σ gJ = emp →
    Runs (.loop gKt runStep) σ (· = Function.update (Function.update (Function.update σ gO
        ⟨((List.range n).map fun j => ones (u + j)).reverse ++ O, []⟩) gV (endv (u + n)))
        gKt ⟨List.replicate n [] ++ L, []⟩) (n * (2 * (u + n) + 34))
  | 0, u, σ, O, L, hKt, hV, hOne, hO, hJ => by
    refine (Runs.loop_done (by simp [hKt]) rfl).mono (fun τ e => ?_) (by simp)
    subst e
    funext i; fin_cases i <;> first | rfl | tsimp [hKt, hV, hO, endv]
  | n + 1, u, σ, O, L, hKt, hV, hOne, hO, hJ => by
    have s1 := runs_runStep σ hV hOne hO (show σ gKt = ⟨L, [] :: List.replicate n []⟩ by
      rw [hKt]; rfl) hJ
    set σ₁ := Function.update (Function.update (Function.update σ gO ⟨ones u :: O, []⟩)
      gV (endv (u + 1))) gKt ⟨[] :: L, List.replicate n []⟩ with hσ₁
    have ih := runs_runLoop n (u + 1) σ₁ (ones u :: O) ([] :: L) (by tsimp [hσ₁]) (by tsimp [hσ₁])
      (by tsimp [hσ₁, hOne]) (by tsimp [hσ₁]) (by tsimp [hσ₁, hJ])
    refine (Runs.loop_step (by simp [hKt]) (s1.mono (fun τ h => by rw [h]; exact ih) le_rfl)).mono
      (fun τ h => ?_) ?_
    · rw [h]
      have e1 := map_range_succ_rev (fun j => ones (u + j)) n O
      simp only [add_zero] at e1
      have e2 : (fun j => ones (u + 1 + j)) = fun j => ones (u + (j + 1)) := by
        funext j; congr 1; ring
      funext i; fin_cases i <;> first | rfl | tsimp [hσ₁, replicate_cons, e2, e1] <;> ring_nf
    · have : 2 * u + 32 + 2 + n * (2 * (u + 1 + n) + 34) ≤ (n + 1) * (2 * (u + (n + 1)) + 34) := by
        nlinarith
      omega

/-- The cost bound of one chunk group from start `u`. -/
def groupCost (K DK u : ℕ) : ℕ := (K + 3) * (2 * u + 2 * K + 2 * DK + 60)

set_option maxHeartbeats 8000000 in
/-- One chunk group writes `u, …, u + K - 1` and moves its start `DK` higher. -/
theorem runs_groupStep {K DK u : ℕ} (σ : Fin 15 → WTape) (hU : σ gU = endv u) (hV : σ gV = emp)
    (hKt : σ gKt = ticks K) (hOne : σ gOne = reg (ones 1)) (hDK : σ gDK = reg (ones DK))
    {O L R : List (List Bool)} (hO : σ gO = ⟨O, []⟩) (hQt : σ gQt = ⟨L, [] :: R⟩) (hJ : σ gJ = emp) :
    Runs groupStep σ (· = Function.update (Function.update (Function.update σ gO
        ⟨((List.range K).map fun j => ones (u + j)).reverse ++ O, []⟩) gU (endv (u + DK)))
        gQt ⟨[] :: L, R⟩) (groupCost K DK u) := by
  have s1 := runs_loadV (show gU ≠ gV by decide) σ hU hV
  set σ₁ := Function.update σ gV (endv u) with hσ₁
  have s2 := runs_runLoop K u σ₁ O [] (by tsimp [hσ₁, hKt, ticks]) (by tsimp [hσ₁]) (by tsimp [hσ₁, hOne])
    (by tsimp [hσ₁, hO]) (by tsimp [hσ₁, hJ])
  set σ₂ := Function.update (Function.update (Function.update σ₁ gO
    ⟨((List.range K).map fun j => ones (u + j)).reverse ++ O, []⟩) gV (endv (u + K)))
    gKt ⟨List.replicate K [] ++ [], []⟩ with hσ₂
  have s3 := runs_rewind (a := 0) gKt σ₂
  set σ₃ := Function.update σ₂ gKt ⟨[], (σ₂ gKt).left.reverse ++ (σ₂ gKt).right⟩ with hσ₃
  have s4 := runs_clear (a := 0) gV σ₃
  set σ₄ := Function.update σ₃ gV ⟨[], []⟩ with hσ₄
  have s5 := runs_addTo (c := DK) (v := u) (show gDK ≠ gU by decide) σ₄ (by tsimp [hσ₄, hσ₃, hσ₂, hσ₁, hDK])
    (by tsimp [hσ₄, hσ₃, hσ₂, hσ₁, hU])
  set σ₅ := Function.update σ₄ gU (endv (u + DK)) with hσ₅
  have s6 := runs_skp (a := 0) (show gQt ≠ gJ by decide) σ₅ (by tsimp [hσ₅, hσ₄, hσ₃, hσ₂, hσ₁, hQt])
    (by tsimp [hσ₅, hσ₄, hσ₃, hσ₂, hσ₁, hJ, emp])
  refine (Runs.then s1 (Runs.then s2 (Runs.then s3 (Runs.then s4 (Runs.then s5 s6))))).mono
    (fun τ e => ?_) ?_
  · rw [e]; funext i; fin_cases i <;> first | rfl |
      tsimp [hσ₅, hσ₄, hσ₃, hσ₂, hσ₁, hQt, hV, hKt, ticks, emp]
  · tsimp [hσ₅, hσ₄, hσ₃, hσ₂, hσ₁, hQt, groupCost, endv, clen, WTape.words]
    nlinarith

theorem groupCost_mono {K DK u u' : ℕ} (h : u ≤ u') : groupCost K DK u ≤ groupCost K DK u' := by
  unfold groupCost; gcongr

set_option maxHeartbeats 8000000 in
/-- The chunk groups: group `c` writes `u + c·DK, …, u + c·DK + K - 1`. -/
theorem runs_groupLoop {K DK : ℕ} : ∀ (n u : ℕ) (σ : Fin 15 → WTape) (O L : List (List Bool)),
    σ gQt = ⟨L, List.replicate n []⟩ → σ gU = endv u → σ gV = emp → σ gKt = ticks K →
    σ gOne = reg (ones 1) → σ gDK = reg (ones DK) → σ gO = ⟨O, []⟩ → σ gJ = emp →
    Runs (.loop gQt groupStep) σ (· = Function.update (Function.update (Function.update σ gO
        ⟨((List.range n).flatMap fun c => (List.range K).map fun j => ones (u + c * DK + j)).reverse ++ O, []⟩)
        gU (endv (u + n * DK))) gQt ⟨List.replicate n [] ++ L, []⟩)
      (n * (groupCost K DK (u + n * DK) + 2))
  | 0, u, σ, O, L, hQt, hU, hV, hKt, hOne, hDK, hO, hJ => by
    refine (Runs.loop_done (by simp [hQt]) rfl).mono (fun τ e => ?_) (by simp)
    subst e
    funext i; fin_cases i <;> first | rfl | tsimp [hQt, hU, hO, endv]
  | n + 1, u, σ, O, L, hQt, hU, hV, hKt, hOne, hDK, hO, hJ => by
    have s1 := runs_groupStep (K := K) (DK := DK) σ hU hV hKt hOne hDK hO
      (show σ gQt = ⟨L, [] :: List.replicate n []⟩ by rw [hQt]; rfl) hJ
    set σ₁ := Function.update (Function.update (Function.update σ gO
      ⟨((List.range K).map fun j => ones (u + j)).reverse ++ O, []⟩) gU (endv (u + DK)))
      gQt ⟨[] :: L, List.replicate n []⟩ with hσ₁
    have ih := runs_groupLoop (K := K) (DK := DK) n (u + DK) σ₁
      (((List.range K).map fun j => ones (u + j)).reverse ++ O) ([] :: L) (by tsimp [hσ₁]) (by tsimp [hσ₁])
      (by tsimp [hσ₁, hV]) (by tsimp [hσ₁, hKt]) (by tsimp [hσ₁, hOne]) (by tsimp [hσ₁, hDK]) (by tsimp [hσ₁])
      (by tsimp [hσ₁, hJ])
    refine (Runs.loop_step (by simp [hQt]) (s1.mono (fun τ h => by rw [h]; exact ih) le_rfl)).mono
      (fun τ h => ?_) ?_
    · rw [h]
      have e1 := flatMap_range_succ_rev (fun c => (List.range K).map fun j => ones (u + c * DK + j)) n O
      simp only [zero_mul, add_zero] at e1
      have e2 : (fun c => (List.range K).map fun j => ones (u + DK + c * DK + j)) =
          fun c => (List.range K).map fun j => ones (u + (c + 1) * DK + j) := by
        funext c; congr 1; funext j; congr 1; ring
      funext i; fin_cases i <;> first | rfl | tsimp [hσ₁, replicate_cons, e2, e1] <;> ring_nf
    · have hm : groupCost K DK u ≤ groupCost K DK (u + (n + 1) * DK) := groupCost_mono (by nlinarith)
      have hm' : groupCost K DK (u + DK + n * DK) = groupCost K DK (u + (n + 1) * DK) := by
        congr 1; ring
      rw [hm']
      nlinarith

set_option maxHeartbeats 4000000 in
theorem runs_loadU {x : ℕ} (σ : Fin 15 → WTape) (hB : σ gB = endv x) (hU : σ gU = emp) :
    Runs loadU σ (· = Function.update σ gU (endv x)) (2 * x + 15) := by
  apply Runs.of_wp
  simp only [loadU, cpy, WP, wp_op0, wp_rewind, wp_clear]
  tsimp [hB, hU, endv, emp, Rules.output_copy]
  refine ⟨?_, ?_⟩
  · funext i; fin_cases i <;> first | rfl | tsimp [hB, hU, endv, emp]
  · simp [time_copy, clen, WTape.words]; omega

/-- The cost bound of one axis from starts `a` and `bb`. -/
def axisCost (D DK K b q a bb : ℕ) : ℕ :=
  2 * a + 15 + b * (2 * (a + b * D) + 2 * D + 32) + (b + 2) + (2 * (a + b * D + 1) + 2) + (2 * bb + 17) +
    q * (groupCost K DK (bb + q * DK) + 2) + (q + 2) + (2 * (bb + q * DK + 1) + 2) + (8 * a + 54) +
    (8 * bb + 4 * K + 50) + 5 + 11

theorem axisCost_mono {D DK K b q a bb a' bb' : ℕ} (ha : a' ≤ a) (hb : bb' ≤ bb) :
    axisCost D DK K b q a' bb' ≤ axisCost D DK K b q a bb := by
  unfold axisCost
  have := groupCost_mono (K := K) (DK := DK) (show bb' + q * DK ≤ bb + q * DK by omega)
  gcongr

set_option maxHeartbeats 16000000 in
/-- One axis writes its row and lowers both starts. -/
theorem runs_axisStep {D DK K b q a bb : ℕ} (σ : Fin 15 → WTape) (hA : σ gA = endv a) (hB : σ gB = endv bb)
    (hV : σ gV = emp) (hU : σ gU = emp) (hBt : σ gBt = ticks b) (hQt : σ gQt = ticks q) (hKt : σ gKt = ticks K)
    (hD : σ gD = reg (ones D)) (hDK : σ gDK = reg (ones DK)) (hK : σ gK = reg (ones K))
    (hOne : σ gOne = reg (ones 1)) {O L R : List (List Bool)} (hO : σ gO = ⟨O, []⟩)
    (hAx : σ gAx = ⟨L, [] :: R⟩) (hS : σ gS = emp) (hJ : σ gJ = emp) :
    Runs axisStep σ (· = Function.update (Function.update (Function.update (Function.update σ gO
        ⟨((axisRow D DK K b q a bb).map ones).reverse ++ O, []⟩) gA (endv (a - 1))) gB (endv (bb - K)))
        gAx ⟨[] :: L, R⟩) (axisCost D DK K b q a bb) := by
  have s1 := runs_loadV (show gA ≠ gV by decide) σ hA hV
  set σ₁ := Function.update σ gV (endv a) with hσ₁
  have s2 := runs_bottomLoop (D := D) b a σ₁ O [] (by tsimp [hσ₁, hBt, ticks]) (by tsimp [hσ₁])
    (by tsimp [hσ₁, hD]) (by tsimp [hσ₁, hO]) (by tsimp [hσ₁, hJ])
  set O₁ := ((List.range b).map fun j => ones (a + j * D)).reverse ++ O with hO₁
  set σ₂ := Function.update (Function.update (Function.update σ₁ gO ⟨O₁, []⟩) gV (endv (a + b * D)))
    gBt ⟨List.replicate b [] ++ [], []⟩ with hσ₂
  have s3 := runs_rewind (a := 0) gBt σ₂
  set σ₃ := Function.update σ₂ gBt ⟨[], (σ₂ gBt).left.reverse ++ (σ₂ gBt).right⟩ with hσ₃
  have s4 := runs_clear (a := 0) gV σ₃
  set σ₄ := Function.update σ₃ gV ⟨[], []⟩ with hσ₄
  have s5 := runs_loadU (x := bb) σ₄ (by tsimp [hσ₄, hσ₃, hσ₂, hσ₁, hB]) (by tsimp [hσ₄, hσ₃, hσ₂, hσ₁, hU])
  set σ₅ := Function.update σ₄ gU (endv bb) with hσ₅
  have s6 := runs_groupLoop (K := K) (DK := DK) q bb σ₅ O₁ [] (by tsimp [hσ₅, hσ₄, hσ₃, hσ₂, hσ₁, hQt, ticks])
    (by tsimp [hσ₅]) (by tsimp [hσ₅, hσ₄, emp]) (by tsimp [hσ₅, hσ₄, hσ₃, hσ₂, hσ₁, hKt])
    (by tsimp [hσ₅, hσ₄, hσ₃, hσ₂, hσ₁, hOne]) (by tsimp [hσ₅, hσ₄, hσ₃, hσ₂, hσ₁, hDK])
    (by tsimp [hσ₅, hσ₄, hσ₃, hσ₂]) (by tsimp [hσ₅, hσ₄, hσ₃, hσ₂, hσ₁, hJ])
  set O₂ := ((List.range q).flatMap fun c => (List.range K).map fun j => ones (bb + c * DK + j)).reverse ++ O₁
    with hO₂
  set σ₆ := Function.update (Function.update (Function.update σ₅ gO ⟨O₂, []⟩) gU (endv (bb + q * DK)))
    gQt ⟨List.replicate q [] ++ [], []⟩ with hσ₆
  have s7 := runs_rewind (a := 0) gQt σ₆
  set σ₇ := Function.update σ₆ gQt ⟨[], (σ₆ gQt).left.reverse ++ (σ₆ gQt).right⟩ with hσ₇
  have s8 := runs_clear (a := 0) gU σ₇
  set σ₈ := Function.update σ₇ gU ⟨[], []⟩ with hσ₈
  have s9 := runs_subFrom (x := a) (c := 1) (show gA ≠ gOne by decide) (by decide) (by decide) (by decide) σ₈
    (by tsimp [hσ₈, hσ₇, hσ₆, hσ₅, hσ₄, hσ₃, hσ₂, hσ₁, hA])
    (by tsimp [hσ₈, hσ₇, hσ₆, hσ₅, hσ₄, hσ₃, hσ₂, hσ₁, hOne])
    (by tsimp [hσ₈, hσ₇, hσ₆, hσ₅, hσ₄, hσ₃, hσ₂, hσ₁, hS])
  set σ₉ := Function.update σ₈ gA (endv (a - 1)) with hσ₉
  have s10 := runs_subFrom (x := bb) (c := K) (show gB ≠ gK by decide) (by decide) (by decide) (by decide) σ₉
    (by tsimp [hσ₉, hσ₈, hσ₇, hσ₆, hσ₅, hσ₄, hσ₃, hσ₂, hσ₁, hB])
    (by tsimp [hσ₉, hσ₈, hσ₇, hσ₆, hσ₅, hσ₄, hσ₃, hσ₂, hσ₁, hK])
    (by tsimp [hσ₉, hσ₈, hσ₇, hσ₆, hσ₅, hσ₄, hσ₃, hσ₂, hσ₁, hS])
  set σ₁₀ := Function.update σ₉ gB (endv (bb - K)) with hσ₁₀
  have s11 := runs_skp (a := 0) (show gAx ≠ gJ by decide) σ₁₀
    (by tsimp [hσ₁₀, hσ₉, hσ₈, hσ₇, hσ₆, hσ₅, hσ₄, hσ₃, hσ₂, hσ₁, hAx])
    (by tsimp [hσ₁₀, hσ₉, hσ₈, hσ₇, hσ₆, hσ₅, hσ₄, hσ₃, hσ₂, hσ₁, hJ, emp])
  have hrow : ((axisRow D DK K b q a bb).map ones).reverse ++ O = O₂ := by
    rw [hO₂, hO₁, ← List.append_assoc, ← List.reverse_append]
    unfold axisRow bottomRow chunkRow chunkRun
    simp [List.map_flatMap, List.map_map, Function.comp_def, Nat.add_assoc]
  refine (Runs.then s1 (Runs.then s2 (Runs.then s3 (Runs.then s4 (Runs.then s5 (Runs.then s6
    (Runs.then s7 (Runs.then s8 (Runs.then s9 (Runs.then s10 s11)))))))))).mono (fun τ e => ?_) ?_
  · rw [e, hrow]; funext i; fin_cases i <;> first | rfl |
      tsimp [hσ₁₀, hσ₉, hσ₈, hσ₇, hσ₆, hσ₅, hσ₄, hσ₃, hσ₂, hσ₁, hAx, hV, hU, hBt, hQt, ticks, emp]
  · tsimp [hσ₁₀, hσ₉, hσ₈, hσ₇, hσ₆, hσ₅, hσ₄, hσ₃, hσ₂, hσ₁, hAx, axisCost, endv, clen, WTape.words]
    omega

set_option maxHeartbeats 8000000 in
/-- The axis loop: axis `i` writes its row from starts `a - i` and `bb - iK`. -/
theorem runs_axisLoop {D DK K b q : ℕ} : ∀ (n a bb : ℕ) (σ : Fin 15 → WTape) (O L : List (List Bool)),
    σ gAx = ⟨L, List.replicate n []⟩ → σ gA = endv a → σ gB = endv bb → σ gV = emp → σ gU = emp →
    σ gBt = ticks b → σ gQt = ticks q → σ gKt = ticks K → σ gD = reg (ones D) → σ gDK = reg (ones DK) →
    σ gK = reg (ones K) → σ gOne = reg (ones 1) → σ gO = ⟨O, []⟩ → σ gS = emp → σ gJ = emp →
    Runs rowsGen σ (· = Function.update (Function.update (Function.update (Function.update σ gO
        ⟨((List.range n).flatMap fun i => (axisRow D DK K b q (a - i) (bb - i * K)).map ones).reverse ++ O, []⟩)
        gA (endv (a - n))) gB (endv (bb - n * K))) gAx ⟨List.replicate n [] ++ L, []⟩)
      (n * (axisCost D DK K b q a bb + 2))
  | 0, a, bb, σ, O, L, hAx, hA, hB, hV, hU, hBt, hQt, hKt, hD, hDK, hK, hOne, hO, hS, hJ => by
    refine (Runs.loop_done (by simp [hAx]) rfl).mono (fun τ e => ?_) (by simp)
    subst e
    funext i; fin_cases i <;> first | rfl | tsimp [hAx, hA, hB, hO, endv]
  | n + 1, a, bb, σ, O, L, hAx, hA, hB, hV, hU, hBt, hQt, hKt, hD, hDK, hK, hOne, hO, hS, hJ => by
    have s1 := runs_axisStep (D := D) (DK := DK) (K := K) (b := b) (q := q) σ hA hB hV hU hBt hQt hKt hD
      hDK hK hOne hO (show σ gAx = ⟨L, [] :: List.replicate n []⟩ by rw [hAx]; rfl) hS hJ
    set σ₁ := Function.update (Function.update (Function.update (Function.update σ gO
      ⟨((axisRow D DK K b q a bb).map ones).reverse ++ O, []⟩) gA (endv (a - 1))) gB (endv (bb - K)))
      gAx ⟨[] :: L, List.replicate n []⟩ with hσ₁
    have ih := runs_axisLoop (D := D) (DK := DK) (K := K) (b := b) (q := q) n (a - 1) (bb - K) σ₁
      (((axisRow D DK K b q a bb).map ones).reverse ++ O) ([] :: L) (by tsimp [hσ₁]) (by tsimp [hσ₁])
      (by tsimp [hσ₁]) (by tsimp [hσ₁, hV]) (by tsimp [hσ₁, hU]) (by tsimp [hσ₁, hBt]) (by tsimp [hσ₁, hQt])
      (by tsimp [hσ₁, hKt]) (by tsimp [hσ₁, hD]) (by tsimp [hσ₁, hDK]) (by tsimp [hσ₁, hK])
      (by tsimp [hσ₁, hOne]) (by tsimp [hσ₁]) (by tsimp [hσ₁, hS]) (by tsimp [hσ₁, hJ])
    refine (Runs.loop_step (by simp [hAx]) (s1.mono (fun τ h => by rw [h]; exact ih) le_rfl)).mono
      (fun τ h => ?_) ?_
    · rw [h]
      have e1 := flatMap_range_succ_rev (fun i => (axisRow D DK K b q (a - i) (bb - i * K)).map ones) n O
      simp only [zero_mul, Nat.sub_zero] at e1
      have e2 : (fun i => (axisRow D DK K b q (a - 1 - i) (bb - K - i * K)).map ones) =
          fun i => (axisRow D DK K b q (a - (i + 1)) (bb - (i + 1) * K)).map ones := by
        funext i; congr 2
        · omega
        · rw [Nat.sub_sub, Nat.add_mul, one_mul, Nat.add_comm K]
      have e3 : a - 1 - n = a - (n + 1) := by omega
      have e4 : bb - K - n * K = bb - (n + 1) * K := by rw [Nat.sub_sub, Nat.add_mul, one_mul, Nat.add_comm K]
      funext i; fin_cases i <;> first | rfl | tsimp [hσ₁, replicate_cons, e2, e1, e3, e4]
    · have hm := axisCost_mono (D := D) (DK := DK) (K := K) (b := b) (q := q)
        (show a - 1 ≤ a by omega) (show bb - K ≤ bb by omega)
      nlinarith

/-- `runs_rowsGen`: with `D` axis ticks, starts `a` and `bb`, the constants and empty work tapes, the
program writes every axis row of `axisRows D DK K b q a bb`, one unary word per slot. -/
theorem runs_rowsGen {D DK K b q a bb : ℕ} (σ : Fin 15 → WTape) (hAx : σ gAx = ticks D) (hA : σ gA = endv a)
    (hB : σ gB = endv bb) (hV : σ gV = emp) (hU : σ gU = emp) (hBt : σ gBt = ticks b) (hQt : σ gQt = ticks q)
    (hKt : σ gKt = ticks K) (hD : σ gD = reg (ones D)) (hDK : σ gDK = reg (ones DK)) (hK : σ gK = reg (ones K))
    (hOne : σ gOne = reg (ones 1)) (hO : σ gO = emp) (hS : σ gS = emp) (hJ : σ gJ = emp) :
    Runs rowsGen σ (fun σ' => σ' gO = ⟨((axisRows D DK K b q a bb).flatMap fun row => row.map ones).reverse, []⟩)
      (D * (axisCost D DK K b q a bb + 2)) := by
  refine (runs_axisLoop D a bb σ [] [] (by rw [hAx]; rfl) hA hB hV hU hBt hQt hKt hD hDK hK hOne
    (by rw [hO]; rfl) hS hJ).mono (fun τ e => ?_) le_rfl
  rw [e]
  tsimp [axisRows, List.flatMap_map]

/-- `runs_rowsGen_paper`: started from the paper's parameters, the program writes, axis after axis, the
physical bits of slots `0, …, ℓ - 2` in the paper's layout. -/
theorem runs_rowsGen_paper {r : ℕ} {ts : List ℕ} {ℓ K : ℕ} (hL : LayoutOK r ts ℓ K) (σ : Fin 15 → WTape)
    (hAx : σ gAx = ticks ts.length)
    (hA : σ gA = endv (ts.length * ((ℓ - 1) / K) * K + (ts.length - 1)))
    (hB : σ gB = endv ((ts.length - 1) * K)) (hV : σ gV = emp) (hU : σ gU = emp)
    (hBt : σ gBt = ticks ((ℓ - 1) % K)) (hQt : σ gQt = ticks ((ℓ - 1) / K)) (hKt : σ gKt = ticks K)
    (hD : σ gD = reg (ones ts.length)) (hDK : σ gDK = reg (ones (ts.length * K))) (hK : σ gK = reg (ones K))
    (hOne : σ gOne = reg (ones 1)) (hO : σ gO = emp) (hS : σ gS = emp) (hJ : σ gJ = emp) :
    Runs rowsGen σ (fun σ' => σ' gO = ⟨((List.range ts.length).flatMap fun i =>
        (List.range (ℓ - 1)).map fun h => ones (paperSigma ts ℓ K i h)).reverse, []⟩)
      (ts.length * (axisCost ts.length (ts.length * K) K ((ℓ - 1) % K) ((ℓ - 1) / K)
        (ts.length * ((ℓ - 1) / K) * K + (ts.length - 1)) ((ts.length - 1) * K) + 2)) := by
  refine (runs_rowsGen σ hAx hA hB hV hU hBt hQt hKt hD hDK hK hOne hO hS hJ).mono (fun τ e => ?_) le_rfl
  rw [e, axisRows_paper hL]
  simp [List.flatMap_map, List.map_map, Function.comp_def]

end SigmaRowsTape

end IntegerMultBounds.Schoenhage
