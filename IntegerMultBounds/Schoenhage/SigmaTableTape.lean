module

public import IntegerMultBounds.Schoenhage.SigmaRowsTape

/-! A slot round's exponent table, read off the axis rows on tapes. For a
round at slot `h` below the top, every axis takes part: the program copies the
first `h` words of the axis's row, takes word `h` as the slot bit, skips the
rest of the row, and writes one entry per copied word with weights
`W, 2W, 4W, …` (`runs_tableGen`). This is the table `tableWords (slotTableP …)`
of the round (`runs_tableGen_paper`). -/

@[expose] public section

set_option maxRecDepth 100000

namespace IntegerMultBounds.Schoenhage

open Machine Strm TwistDescriptors SigmaRowsTape

namespace SigmaTableTape

/-! ### The bank -/

/-- One tick per axis. -/
abbrev tAx : Fin 14 := 0
/-- `h` ticks. -/
abbrev tH : Fin 14 := 1
/-- `m - 1 - h` ticks, `m` the row length. -/
abbrev tRest : Fin 14 := 2
/-- `m` ticks. -/
abbrev tFull : Fin 14 := 3
/-- The long-axis flags. -/
abbrev tF : Fin 14 := 4
/-- The axis rows. -/
abbrev tR : Fin 14 := 5
/-- The top-slot bits of the long axes. -/
abbrev tTop : Fin 14 := 6
/-- The copied lower bits of the current axis. -/
abbrev tS : Fin 14 := 7
/-- The current axis's slot bit. -/
abbrev tX : Fin 14 := 8
/-- The first weight. -/
abbrev tW0 : Fin 14 := 9
/-- The current weight. -/
abbrev tW : Fin 14 := 10
/-- Scratch. -/
abbrev tT : Fin 14 := 11
/-- The table. -/
abbrev tTab : Fin 14 := 12
/-- The junk tape. -/
abbrev tJ : Fin 14 := 13

/-! ### The program -/

/-- Copy `h` words of the rows to `tS`. -/
noncomputable def copyH : Cmd 0 14 := .loop tH (.seq (cpy tR tS (by decide)) (skp tH tJ (by decide)))

/-- Skip the rest of the row. -/
noncomputable def skipRest : Cmd 0 14 := .loop tRest (.seq (skp tR tJ (by decide)) (skp tRest tJ (by decide)))

/-- Double the weight. -/
noncomputable def dblW : Cmd 0 14 :=
  .seq (rewind tW) <| .seq (cpy tW tT (by decide)) <| .seq (rewind tT) <|
  .seq (op0 Rules.copy true tT tW (by decide)) (clear tT)

/-- Write the slot bit, the lower bit and the weight. -/
noncomputable def emitParts : Cmd 0 14 :=
  .seq (rewind tX) <| .seq (cpy tX tTab (by decide)) <| .seq (cpy tS tTab (by decide)) <|
  .seq (rewind tW) (cpy tW tTab (by decide))

/-- One entry: the slot bit, the lower bit and the weight, then the weight doubles. -/
noncomputable def emitEntry : Cmd 0 14 := .seq emitParts dblW

/-- Load the first weight. -/
noncomputable def loadW : Cmd 0 14 := .seq (rewind tW0) (cpy tW0 tW (by decide))

/-- Rewind the ticks and the copied bits, and load the first weight. -/
noncomputable def prepEntries : Cmd 0 14 := .seq (rewind tH) <| .seq (rewind tRest) <| .seq (rewind tS) loadW

/-- Clear the work tapes and step to the next axis. -/
noncomputable def finishAxis : Cmd 0 14 :=
  .seq (clear tS) <| .seq (clear tX) <| .seq (clear tW) (skp tAx tJ (by decide))

/-- One axis of a round below the top. -/
noncomputable def roundAxis : Cmd 0 14 :=
  .seq copyH <| .seq (cpy tR tX (by decide)) <| .seq skipRest <| .seq prepEntries <|
  .seq (.loop tS emitEntry) finishAxis

/-- The table of a round below the top. -/
noncomputable def tableGen : Cmd 0 14 := .loop tAx roundAxis

/-! ### Steps -/

/-- Words of an axis's entries. -/
theorem tableWords_axisEntries_cons (X W v : ℕ) (vs : List ℕ) :
    tableWords (axisEntries X W (v :: vs)) = ones X :: ones v :: ones W :: tableWords (axisEntries X (2 * W) vs) := by
  simp [axisEntries, tableWords]

set_option maxHeartbeats 8000000 in
theorem runs_dblW {w : ℕ} (σ : Fin 14 → WTape) (hW : σ tW = endv w) (hT : σ tT = emp) :
    Runs dblW σ (· = Function.update σ tW (endv (2 * w))) (8 * w + 30) := by
  apply Runs.of_wp
  simp only [dblW, cpy, WP, wp_op0, wp_rewind, wp_clear]
  tsimp [hW, hT, endv, emp, Rules.output_copy]
  refine ⟨?_, ?_⟩
  · funext i; fin_cases i <;> first | rfl | tsimp [hW, hT, endv, emp, ones_append, two_mul]
  · simp [time_copy, clen, WTape.words]; omega

set_option maxHeartbeats 8000000 in
theorem runs_emitEntry {X v w : ℕ} (σ : Fin 14 → WTape) (hX : σ tX = endv X) {LS RS : List (List Bool)}
    (hS : σ tS = ⟨LS, ones v :: RS⟩) (hW : σ tW = endv w) (hT : σ tT = emp) {O : List (List Bool)}
    (hTab : σ tTab = ⟨O, []⟩) :
    Runs emitEntry σ (· = Function.update (Function.update (Function.update σ tTab
        ⟨ones w :: ones v :: ones X :: O, []⟩) tS ⟨ones v :: LS, RS⟩) tW (endv (2 * w)))
      (4 * X + 2 * v + 12 * w + 80) := by
  have s1 : Runs emitParts σ
      (· = Function.update (Function.update σ tTab ⟨ones w :: ones v :: ones X :: O, []⟩) tS ⟨ones v :: LS, RS⟩)
      (2 * X + v + 2 * w + 40) := by
    apply Runs.of_wp
    simp only [emitParts, cpy, WP, wp_op0, wp_rewind]
    tsimp [hX, hS, hW, hTab, endv, Rules.output_copy]
    refine ⟨?_, ?_⟩
    · funext i; fin_cases i <;> first | rfl | tsimp [hX, hS, hW, hTab, endv]
    · simp [time_copy]; omega
  set σ₁ := Function.update (Function.update σ tTab ⟨ones w :: ones v :: ones X :: O, []⟩) tS
    ⟨ones v :: LS, RS⟩ with hσ₁
  have s2 := runs_dblW (w := w) σ₁ (by tsimp [hσ₁, hW]) (by tsimp [hσ₁, hT])
  exact (Runs.then s1 s2).mono (fun τ e => e) (by omega)

/-! ### Loops -/

set_option maxHeartbeats 8000000 in
/-- The entries of one axis, from the copied lower bits. -/
theorem runs_entriesLoop {X Vm : ℕ} : ∀ (vs : List ℕ) (w : ℕ) (σ : Fin 14 → WTape) (LS O : List (List Bool)),
    (∀ v ∈ vs, v ≤ Vm) → σ tS = ⟨LS, vs.map ones⟩ → σ tX = endv X → σ tW = endv w → σ tT = emp →
    σ tTab = ⟨O, []⟩ →
    Runs (.loop tS emitEntry) σ (· = Function.update (Function.update (Function.update σ tTab
        ⟨(tableWords (axisEntries X w vs)).reverse ++ O, []⟩) tS ⟨(vs.map ones).reverse ++ LS, []⟩)
        tW (endv (w * 2 ^ vs.length))) (vs.length * (4 * X + 2 * Vm + 12 * (w * 2 ^ vs.length) + 82))
  | [], w, σ, LS, O, _, hS, hX, hW, hT, hTab => by
    refine (Runs.loop_done (by simp [hS]) rfl).mono (fun τ e => ?_) (by simp)
    subst e
    funext i; fin_cases i <;> first | rfl | tsimp [hS, hW, hTab, endv, axisEntries, tableWords]
  | v :: vs, w, σ, LS, O, hvs, hS, hX, hW, hT, hTab => by
    have s1 := runs_emitEntry (X := X) (v := v) (w := w) σ hX (by rw [hS]; rfl) hW hT hTab
    set σ₁ := Function.update (Function.update (Function.update σ tTab ⟨ones w :: ones v :: ones X :: O, []⟩)
      tS ⟨ones v :: LS, vs.map ones⟩) tW (endv (2 * w)) with hσ₁
    have ih := runs_entriesLoop (X := X) (Vm := Vm) vs (2 * w) σ₁ (ones v :: LS) (ones w :: ones v :: ones X :: O)
      (fun u hu => hvs u (by simp [hu])) (by tsimp [hσ₁]) (by tsimp [hσ₁, hX]) (by tsimp [hσ₁])
      (by tsimp [hσ₁, hT]) (by tsimp [hσ₁])
    refine (Runs.loop_step (by simp [hS]) (s1.mono (fun τ h => by rw [h]; exact ih) le_rfl)).mono
      (fun τ h => ?_) ?_
    · rw [h]
      have e1 : (tableWords (axisEntries X (2 * w) vs)).reverse ++ ones w :: ones v :: ones X :: O =
          (tableWords (axisEntries X w (v :: vs))).reverse ++ O := by
        rw [tableWords_axisEntries_cons]; simp
      have e2 : 2 * w * 2 ^ vs.length = w * 2 ^ (v :: vs).length := by simp [pow_succ]; ring
      funext i; fin_cases i <;> first | rfl | tsimp [hσ₁, e1, e2]
    · have hv := hvs v (by simp)
      have hpow : w ≤ w * 2 ^ (vs.length + 1) := Nat.le_mul_of_pos_right _ (by positivity)
      have e2 : 2 * w * 2 ^ vs.length = w * 2 ^ (vs.length + 1) := by rw [pow_succ]; ring
      simp only [List.length_cons]
      rw [e2]
      nlinarith

set_option maxHeartbeats 8000000 in
/-- Copy `k` words of the rows to `tS`. -/
theorem runs_copyH {Wm : ℕ} : ∀ (ws : List (List Bool)) (σ : Fin 14 → WTape) (LR RR LS LH : List (List Bool)),
    (∀ u ∈ ws, u.length ≤ Wm) → σ tH = ⟨LH, List.replicate ws.length []⟩ → σ tR = ⟨LR, ws ++ RR⟩ →
    σ tS = ⟨LS, []⟩ → σ tJ = emp →
    Runs copyH σ (· = Function.update (Function.update (Function.update σ tR ⟨ws.reverse ++ LR, RR⟩)
        tS ⟨ws.reverse ++ LS, []⟩) tH ⟨List.replicate ws.length [] ++ LH, []⟩) (ws.length * (Wm + 17))
  | [], σ, LR, RR, LS, LH, _, hH, hR, hS, hJ => by
    refine (Runs.loop_done (by simp [hH]) rfl).mono (fun τ e => ?_) (by simp)
    subst e
    funext i; fin_cases i <;> first | rfl | tsimp [hH, hR, hS]
  | u :: ws, σ, LR, RR, LS, LH, hW, hH, hR, hS, hJ => by
    have s1 : Runs (.seq (cpy (a := 0) tR tS (by decide)) (skp tH tJ (by decide))) σ
        (· = Function.update (Function.update (Function.update σ tR ⟨u :: LR, ws ++ RR⟩) tS ⟨u :: LS, []⟩)
          tH ⟨[] :: LH, List.replicate ws.length []⟩) (u.length + 15) := by
      apply Runs.of_wp
      simp only [cpy, skp, WP, wp_op0]
      tsimp [hH, hR, hS, hJ, emp, Rules.output_copy, Rules.output_skip]
      refine ⟨?_, ?_⟩
      · funext i; fin_cases i <;> first | rfl | tsimp [hH, hR, hS, hJ, emp]
      · simp [time_copy, time_skip, List.replicate_succ]
    set σ₁ := Function.update (Function.update (Function.update σ tR ⟨u :: LR, ws ++ RR⟩) tS ⟨u :: LS, []⟩)
      tH ⟨[] :: LH, List.replicate ws.length []⟩ with hσ₁
    have ih := runs_copyH (Wm := Wm) ws σ₁ (u :: LR) RR (u :: LS) ([] :: LH)
      (fun x hx => hW x (by simp [hx])) (by tsimp [hσ₁]) (by tsimp [hσ₁]) (by tsimp [hσ₁]) (by tsimp [hσ₁, hJ])
    refine (Runs.loop_step (by simp [hH]) (s1.mono (fun τ h => by rw [h]; exact ih) le_rfl)).mono
      (fun τ h => ?_) ?_
    · rw [h]; funext i; fin_cases i <;> first | rfl | tsimp [hσ₁, replicate_cons]
    · have := hW u (by simp)
      simp only [List.length_cons]; nlinarith

set_option maxHeartbeats 8000000 in
/-- Skip `k` words of the rows. -/
theorem runs_skipRest {Wm : ℕ} : ∀ (ws : List (List Bool)) (σ : Fin 14 → WTape) (LR RR LT : List (List Bool)),
    (∀ u ∈ ws, u.length ≤ Wm) → σ tRest = ⟨LT, List.replicate ws.length []⟩ → σ tR = ⟨LR, ws ++ RR⟩ →
    σ tJ = emp →
    Runs skipRest σ (· = Function.update (Function.update σ tR ⟨ws.reverse ++ LR, RR⟩)
        tRest ⟨List.replicate ws.length [] ++ LT, []⟩) (ws.length * (Wm + 17))
  | [], σ, LR, RR, LT, _, hT, hR, hJ => by
    refine (Runs.loop_done (by simp [hT]) rfl).mono (fun τ e => ?_) (by simp)
    subst e
    funext i; fin_cases i <;> first | rfl | tsimp [hT, hR]
  | u :: ws, σ, LR, RR, LT, hW, hT, hR, hJ => by
    have s1 : Runs (.seq (skp (a := 0) tR tJ (by decide)) (skp tRest tJ (by decide))) σ
        (· = Function.update (Function.update σ tR ⟨u :: LR, ws ++ RR⟩)
          tRest ⟨[] :: LT, List.replicate ws.length []⟩) (u.length + 15) := by
      apply Runs.of_wp
      simp only [skp, WP, wp_op0]
      tsimp [hT, hR, hJ, emp, Rules.output_skip]
      refine ⟨?_, ?_⟩
      · funext i; fin_cases i <;> first | rfl | tsimp [hT, hR, hJ, emp]
      · simp [time_skip, List.replicate_succ]
    set σ₁ := Function.update (Function.update σ tR ⟨u :: LR, ws ++ RR⟩)
      tRest ⟨[] :: LT, List.replicate ws.length []⟩ with hσ₁
    have ih := runs_skipRest (Wm := Wm) ws σ₁ (u :: LR) RR ([] :: LT)
      (fun x hx => hW x (by simp [hx])) (by tsimp [hσ₁]) (by tsimp [hσ₁]) (by tsimp [hσ₁, hJ])
    refine (Runs.loop_step (by simp [hT]) (s1.mono (fun τ h => by rw [h]; exact ih) le_rfl)).mono
      (fun τ h => ?_) ?_
    · rw [h]; funext i; fin_cases i <;> first | rfl | tsimp [hσ₁, replicate_cons]
    · have := hW u (by simp)
      simp only [List.length_cons]; nlinarith

/-! ### One axis and the whole table -/

/-- The cost bound of one axis: row length `m`, slot `h`, values at most `Vm`, first weight `w0`. -/
def roundAxisCost (m h Vm w0 : ℕ) : ℕ :=
  (m + 4) * (Vm + 20) + h * (6 * Vm + 12 * (w0 * 2 ^ h) + 82) + 4 * h * (Vm + 1) + 2 * (w0 * 2 ^ h) +
    4 * w0 + 120

theorem clen_map_ones_le {Vm : ℕ} : ∀ (vs : List ℕ), (∀ v ∈ vs, v ≤ Vm) → clen (vs.map ones) ≤ vs.length * (Vm + 1)
  | [], _ => by simp
  | v :: vs, h => by
    have := h v (by simp)
    have ih := clen_map_ones_le vs (fun u hu => h u (by simp [hu]))
    simp only [List.map_cons, clen_cons, length_ones, List.length_cons]
    nlinarith

theorem clen_reverse (ws : List (List Bool)) : clen ws.reverse = clen ws := by
  simp [clen, List.map_reverse, List.sum_reverse]

@[simp] theorem clen_replicate_nil (k : ℕ) : clen (List.replicate k ([] : List Bool)) = k := by
  simp [clen]

set_option maxHeartbeats 4000000 in
theorem runs_loadW {w0 : ℕ} (σ : Fin 14 → WTape) (hW0 : σ tW0 = endv w0) (hW : σ tW = emp) :
    Runs loadW σ (· = Function.update σ tW (endv w0)) (2 * w0 + 10) := by
  apply Runs.of_wp
  simp only [loadW, cpy, WP, wp_op0, wp_rewind]
  tsimp [hW0, hW, endv, emp, Rules.output_copy]
  refine ⟨?_, ?_⟩
  · funext i; fin_cases i <;> first | rfl | tsimp [hW0, hW, endv, emp]
  · simp [time_copy]; omega

set_option maxHeartbeats 16000000 in
/-- One axis of a round below the top writes the axis's entries. -/
theorem runs_roundAxis {h Vm w0 : ℕ} (row : List ℕ) (hh : h < row.length) (hVm : ∀ v ∈ row, v ≤ Vm)
    (σ : Fin 14 → WTape) (hH : σ tH = ticks h) (hRest : σ tRest = ticks (row.length - 1 - h))
    {LR RR : List (List Bool)} (hR : σ tR = ⟨LR, row.map ones ++ RR⟩) (hS : σ tS = emp) (hX : σ tX = emp)
    (hW : σ tW = emp) (hW0 : σ tW0 = endv w0) (hT : σ tT = emp) {O : List (List Bool)}
    (hTab : σ tTab = ⟨O, []⟩) {LA RA : List (List Bool)} (hAx : σ tAx = ⟨LA, [] :: RA⟩) (hJ : σ tJ = emp) :
    Runs roundAxis σ (· = Function.update (Function.update (Function.update σ tR
        ⟨(row.map ones).reverse ++ LR, RR⟩) tTab
        ⟨(tableWords (axisEntries (row.getD h 0) w0 (row.take h))).reverse ++ O, []⟩) tAx ⟨[] :: LA, RA⟩)
      (roundAxisCost row.length h Vm w0) := by
  set ws := (row.take h).map ones with hws
  set xh := row.getD h 0 with hxh
  set ws2 := (row.drop (h + 1)).map ones with hws2
  have hsplit0 : row.map ones = ws ++ ones xh :: ws2 := by
    have e : row = row.take h ++ row.getD h 0 :: row.drop (h + 1) := by
      rw [List.getD_eq_getElem _ _ hh]
      conv_lhs => rw [← List.take_append_drop h row]
      rw [List.drop_eq_getElem_cons hh]
    conv_lhs => rw [e]
    simp [hws, hxh, hws2]
  have hsplit : row.map ones ++ RR = ws ++ (ones xh :: ws2 ++ RR) := by rw [hsplit0]; simp
  have hwsl : ws.length = h := by simp [hws]; omega
  have hws2l : ws2.length = row.length - 1 - h := by simp [hws2]; omega
  have hwsW : ∀ u ∈ ws, u.length ≤ Vm := by
    intro u hu; simp only [hws, List.mem_map] at hu
    obtain ⟨v, hv, rfl⟩ := hu; simpa using hVm v (List.mem_of_mem_take hv)
  have hws2W : ∀ u ∈ ws2, u.length ≤ Vm := by
    intro u hu; simp only [hws2, List.mem_map] at hu
    obtain ⟨v, hv, rfl⟩ := hu; simpa using hVm v (List.mem_of_mem_drop hv)
  have hxhV : xh ≤ Vm := by rw [hxh, List.getD_eq_getElem _ _ hh]; exact hVm _ (List.getElem_mem hh)
  -- copy the lower bits
  have s1 := runs_copyH (Wm := Vm) ws σ LR (ones xh :: ws2 ++ RR) [] []
    hwsW (by rw [hH, hwsl]; rfl) (by rw [hR, hsplit]) (by rw [hS]; rfl) hJ
  set σ₁ := Function.update (Function.update (Function.update σ tR ⟨ws.reverse ++ LR, ones xh :: ws2 ++ RR⟩)
    tS ⟨ws.reverse ++ [], []⟩) tH ⟨List.replicate ws.length [] ++ [], []⟩ with hσ₁
  -- the slot bit
  have s2 : Runs (cpy (a := 0) tR tX (by decide)) σ₁
      (· = Function.update (Function.update σ₁ tR ⟨ones xh :: ws.reverse ++ LR, ws2 ++ RR⟩) tX (endv xh))
      (xh + 6) := by
    refine (runs_cpy (a := 0) (show tR ≠ tX by decide) σ₁ (by tsimp [hσ₁]) (by tsimp [hσ₁, hX, emp])).mono
      (fun τ e => ?_) (by tsimp [hσ₁])
    rw [e]; funext i; fin_cases i <;> first | rfl | tsimp [hσ₁, hX, emp, endv]
  set σ₂ := Function.update (Function.update σ₁ tR ⟨ones xh :: ws.reverse ++ LR, ws2 ++ RR⟩) tX (endv xh)
    with hσ₂
  -- skip the rest of the row
  have s3 := runs_skipRest (Wm := Vm) ws2 σ₂ (ones xh :: ws.reverse ++ LR) RR [] hws2W
    (by tsimp [hσ₂, hσ₁, hRest, ticks, hws2l]) (by tsimp [hσ₂]) (by tsimp [hσ₂, hσ₁, hJ])
  set σ₃ := Function.update (Function.update σ₂ tR ⟨ws2.reverse ++ (ones xh :: ws.reverse ++ LR), RR⟩)
    tRest ⟨List.replicate ws2.length [] ++ [], []⟩ with hσ₃
  -- rewind the ticks and the copied bits, load the weight
  have s4 : Runs prepEntries σ₃
      (· = Function.update (Function.update (Function.update (Function.update σ₃ tH (ticks h))
        tRest (ticks (row.length - 1 - h))) tS ⟨[], ws⟩) tW (endv w0))
      (3 * row.length + h * (Vm + 1) + 2 * w0 + 30) := by
    have r1 := runs_rewind (a := 0) tH σ₃
    set τ₁ := Function.update σ₃ tH ⟨[], (σ₃ tH).left.reverse ++ (σ₃ tH).right⟩ with hτ₁
    have r2 := runs_rewind (a := 0) tRest τ₁
    set τ₂ := Function.update τ₁ tRest ⟨[], (τ₁ tRest).left.reverse ++ (τ₁ tRest).right⟩ with hτ₂
    have r3 := runs_rewind (a := 0) tS τ₂
    set τ₃ := Function.update τ₂ tS ⟨[], (τ₂ tS).left.reverse ++ (τ₂ tS).right⟩ with hτ₃
    have r4 := runs_loadW (w0 := w0) τ₃ (by tsimp [hτ₃, hτ₂, hτ₁, hσ₃, hσ₂, hσ₁, hW0])
      (by tsimp [hτ₃, hτ₂, hτ₁, hσ₃, hσ₂, hσ₁, hW])
    refine (Runs.then r1 (Runs.then r2 (Runs.then r3 r4))).mono (fun τ e => ?_) ?_
    · rw [e]; funext i; fin_cases i <;> first | rfl |
        tsimp [hτ₃, hτ₂, hτ₁, hσ₃, hσ₂, hσ₁, ticks, hwsl, hws2l]
    · have hc := clen_map_ones_le (Vm := Vm) (row.take h) (fun v hv => hVm v (List.mem_of_mem_take hv))
      rw [List.length_take, Nat.min_eq_left hh.le] at hc
      have hc1 : clen (List.replicate ws.length ([] : List Bool) ++ []) = h := by simp [clen, hwsl]
      have hc2 : clen (List.replicate ws2.length ([] : List Bool) ++ []) = row.length - 1 - h := by
        simp [clen, hws2l]
      rw [← hws] at hc
      tsimp [hτ₃, hτ₂, hτ₁, hσ₃, hσ₂, hσ₁, clen_reverse, hwsl, hws2l]
      omega
  set σ₄ := Function.update (Function.update (Function.update (Function.update σ₃ tH (ticks h))
    tRest (ticks (row.length - 1 - h))) tS ⟨[], ws⟩) tW (endv w0) with hσ₄
  -- the entries
  have s5 := runs_entriesLoop (X := xh) (Vm := Vm) (row.take h) w0 σ₄ [] O
    (fun v hv => hVm v (List.mem_of_mem_take hv)) (by tsimp [hσ₄, hws, List.map_take]) (by tsimp [hσ₄, hσ₃, hσ₂])
    (by tsimp [hσ₄]) (by tsimp [hσ₄, hσ₃, hσ₂, hσ₁, hT]) (by tsimp [hσ₄, hσ₃, hσ₂, hσ₁, hTab])
  set σ₅ := Function.update (Function.update (Function.update σ₄ tTab
    ⟨(tableWords (axisEntries xh w0 (row.take h))).reverse ++ O, []⟩) tS ⟨((row.take h).map ones).reverse ++ [], []⟩)
    tW (endv (w0 * 2 ^ (row.take h).length)) with hσ₅
  -- clear the work tapes and step the axis
  have s6 : Runs finishAxis σ₅
      (· = Function.update (Function.update (Function.update (Function.update σ₅ tS emp) tX emp) tW emp)
        tAx ⟨[] :: LA, RA⟩) (2 * (h * (Vm + 1)) + 2 * (Vm + 1) + 2 * (w0 * 2 ^ h + 1) + 20) := by
    have r1 := runs_clear (a := 0) tS σ₅
    set τ₁ := Function.update σ₅ tS ⟨[], []⟩ with hτ₁
    have r2 := runs_clear (a := 0) tX τ₁
    set τ₂ := Function.update τ₁ tX ⟨[], []⟩ with hτ₂
    have r3 := runs_clear (a := 0) tW τ₂
    set τ₃ := Function.update τ₂ tW ⟨[], []⟩ with hτ₃
    have r4 := runs_skp (a := 0) (show tAx ≠ tJ by decide) τ₃
      (by tsimp [hτ₃, hτ₂, hτ₁, hσ₅, hσ₄, hσ₃, hσ₂, hσ₁, hAx])
      (by tsimp [hτ₃, hτ₂, hτ₁, hσ₅, hσ₄, hσ₃, hσ₂, hσ₁, hJ, emp])
    refine (Runs.then r1 (Runs.then r2 (Runs.then r3 r4))).mono (fun τ e => ?_) ?_
    · rw [e]; funext i; fin_cases i <;> first | rfl |
        tsimp [hτ₃, hτ₂, hτ₁, hσ₅, hσ₄, hσ₃, hσ₂, hσ₁, hAx, emp]
    · have hc := clen_map_ones_le (Vm := Vm) (row.take h) (fun v hv => hVm v (List.mem_of_mem_take hv))
      rw [List.length_take, Nat.min_eq_left hh.le] at hc
      tsimp [hτ₃, hτ₂, hτ₁, hσ₅, hσ₄, hσ₃, hσ₂, hσ₁, hAx, WTape.words, clen_reverse, endv,
        List.length_take, Nat.min_eq_left hh.le, ← List.map_take, hwsl]
      omega
  refine (Runs.then s1 (Runs.then s2 (Runs.then s3 (Runs.then s4 (Runs.then s5 s6))))).mono
    (fun τ e => ?_) ?_
  · rw [e]
    have hrow : ws2.reverse ++ ones xh :: (ws.reverse ++ LR) = (row.map ones).reverse ++ LR := by
      rw [hsplit0]; simp
    funext i; fin_cases i <;> first | rfl |
      tsimp [hσ₅, hσ₄, hσ₃, hσ₂, hσ₁, hS, hX, hW, hH, hRest, hrow, emp, ticks, hwsl, hws2l]
  · unfold roundAxisCost
    simp only [hwsl, hws2l, List.length_take, Nat.min_eq_left hh.le]
    obtain ⟨s, hs⟩ : ∃ s, row.length = h + 1 + s := ⟨row.length - 1 - h, by omega⟩
    have hsub : row.length - 1 - h = s := by omega
    rw [hsub, hs]
    have hB : h * (4 * xh + 2 * Vm + 12 * (w0 * 2 ^ h) + 82) ≤ h * (6 * Vm + 12 * (w0 * 2 ^ h) + 82) :=
      Nat.mul_le_mul_left _ (by omega)
    ring_nf at hB ⊢
    nlinarith [hxhV]

set_option maxHeartbeats 8000000 in
/-- `runs_tableGen`: over rows of length `m`, a round at slot `h < m` writes every row's entries. -/
theorem runs_tableGen {m h Vm w0 : ℕ} (hh : h < m) :
    ∀ (rows : List (List ℕ)) (σ : Fin 14 → WTape) (LR RR O LA : List (List Bool)),
      (∀ row ∈ rows, row.length = m ∧ ∀ v ∈ row, v ≤ Vm) →
      σ tAx = ⟨LA, List.replicate rows.length []⟩ → σ tH = ticks h → σ tRest = ticks (m - 1 - h) →
      σ tR = ⟨LR, rows.flatMap (fun row => row.map ones) ++ RR⟩ → σ tS = emp → σ tX = emp → σ tW = emp →
      σ tW0 = endv w0 → σ tT = emp → σ tTab = ⟨O, []⟩ → σ tJ = emp →
      Runs tableGen σ (· = Function.update (Function.update (Function.update σ tR
          ⟨(rows.flatMap fun row => row.map ones).reverse ++ LR, RR⟩) tTab
          ⟨(rows.flatMap fun row => tableWords (axisEntries (row.getD h 0) w0 (row.take h))).reverse ++ O, []⟩)
          tAx ⟨List.replicate rows.length [] ++ LA, []⟩) (rows.length * (roundAxisCost m h Vm w0 + 2))
  | [], σ, LR, RR, O, LA, _, hAx, hH, hRest, hR, hS, hX, hW, hW0, hT, hTab, hJ => by
    refine (Runs.loop_done (by simp [hAx]) rfl).mono (fun τ e => ?_) (by simp)
    subst e
    funext i; fin_cases i <;> first | rfl | tsimp [hAx, hR, hTab]
  | row :: rows, σ, LR, RR, O, LA, hrows, hAx, hH, hRest, hR, hS, hX, hW, hW0, hT, hTab, hJ => by
    obtain ⟨hlen, hVm⟩ := hrows row (by simp)
    have s1 := runs_roundAxis (h := h) (Vm := Vm) (w0 := w0) row (by omega) hVm σ hH (by rw [hRest, hlen])
      (show σ tR = ⟨LR, row.map ones ++ (rows.flatMap (fun row => row.map ones) ++ RR)⟩ by rw [hR]; simp)
      hS hX hW hW0 hT hTab (show σ tAx = ⟨LA, [] :: List.replicate rows.length []⟩ by rw [hAx]; rfl) hJ
    set σ₁ := Function.update (Function.update (Function.update σ tR
      ⟨(row.map ones).reverse ++ LR, rows.flatMap (fun row => row.map ones) ++ RR⟩) tTab
      ⟨(tableWords (axisEntries (row.getD h 0) w0 (row.take h))).reverse ++ O, []⟩) tAx
      ⟨[] :: LA, List.replicate rows.length []⟩ with hσ₁
    have ih := runs_tableGen (m := m) (h := h) (Vm := Vm) (w0 := w0) hh rows σ₁ ((row.map ones).reverse ++ LR) RR
      ((tableWords (axisEntries (row.getD h 0) w0 (row.take h))).reverse ++ O) ([] :: LA)
      (fun r hr => hrows r (by simp [hr])) (by tsimp [hσ₁]) (by tsimp [hσ₁, hH]) (by tsimp [hσ₁, hRest])
      (by tsimp [hσ₁]) (by tsimp [hσ₁, hS]) (by tsimp [hσ₁, hX]) (by tsimp [hσ₁, hW]) (by tsimp [hσ₁, hW0])
      (by tsimp [hσ₁, hT]) (by tsimp [hσ₁]) (by tsimp [hσ₁, hJ])
    refine (Runs.loop_step (by simp [hAx]) (s1.mono (fun τ h => by rw [h]; exact ih) le_rfl)).mono
      (fun τ h => ?_) ?_
    · rw [h]; funext i; fin_cases i <;> first | rfl | tsimp [hσ₁, replicate_cons]
    · rw [hlen]; simp only [List.length_cons]; ring_nf; omega

/-- The rows' values bound: every physical bit is below the address width. -/
theorem paperSigma_lt {r : ℕ} {ts : List ℕ} {ℓ K : ℕ} (hL : LayoutOK r ts ℓ K) {i h : ℕ} (hi : i < ts.length)
    (hh : h < axLen ts i) : paperSigma ts ℓ K i h < Nat.log 2 ts.prod := by
  rw [← paperPerm_σ_eq hL hi hh]
  exact (paperPerm hL).σ_lt _ (by have := axOff_add_len_le hL.1 hi; omega)

/-- `runs_tableGen_paper`: started on the paper's axis rows, a round at slot `h < ℓ - 1` writes the
round's exponent table `tableWords (slotTable (paperPerm hL) r ts (slotAxes ts h) h)`. -/
theorem runs_tableGen_paper {r : ℕ} {ts : List ℕ} {ℓ K : ℕ} (hL : LayoutOK r ts ℓ K) (r' : ℕ) {h : ℕ}
    (hh : h < ℓ - 1) (σ : Fin 14 → WTape) (hAx : σ tAx = ticks ts.length) (hH : σ tH = ticks h)
    (hRest : σ tRest = ticks (ℓ - 1 - 1 - h))
    (hR : σ tR = ⟨[], (List.range ts.length).flatMap fun i =>
      (List.range (ℓ - 1)).map fun h' => ones (paperSigma ts ℓ K i h')⟩)
    (hS : σ tS = emp) (hX : σ tX = emp) (hW : σ tW = emp)
    (hW0 : σ tW0 = endv (2 * (2 * r' / 2 ^ (h + 1)))) (hT : σ tT = emp) (hTab : σ tTab = emp)
    (hJ : σ tJ = emp) :
    Runs tableGen σ (fun σ' => σ' tTab =
        ⟨(tableWords (slotTable (paperPerm hL) r' ts (slotAxes ts h) h)).reverse, []⟩)
      (ts.length * (roundAxisCost (ℓ - 1) h (Nat.log 2 ts.prod) (2 * (2 * r' / 2 ^ (h + 1))) + 2)) := by
  set rows := (List.range ts.length).map fun i => (List.range (ℓ - 1)).map (paperSigma ts ℓ K i) with hrows
  have hrowsOK : ∀ row ∈ rows, row.length = ℓ - 1 ∧ ∀ v ∈ row, v ≤ Nat.log 2 ts.prod := by
    intro row hrow
    simp only [hrows, List.mem_map, List.mem_range] at hrow
    obtain ⟨i, hi, rfl⟩ := hrow
    refine ⟨by simp, fun v hv => ?_⟩
    simp only [List.mem_map, List.mem_range] at hv
    obtain ⟨h', hh', rfl⟩ := hv
    have := hL.2.1 i hi
    exact (paperSigma_lt hL hi (by omega)).le
  have hRw : σ tR = ⟨[], rows.flatMap (fun row => row.map ones) ++ []⟩ := by
    rw [hR, hrows]; simp [List.flatMap_map, List.map_map, Function.comp_def]
  have hlen : rows.length = ts.length := by simp [hrows]
  have s := runs_tableGen (m := ℓ - 1) (h := h) (Vm := Nat.log 2 ts.prod) (w0 := 2 * (2 * r' / 2 ^ (h + 1)))
    hh rows σ [] [] [] [] hrowsOK (by rw [hAx, hlen]; rfl) hH hRest hRw hS hX hW hW0 hT (by rw [hTab]; rfl) hJ
  rw [hlen] at s
  refine s.mono (fun τ e => ?_) le_rfl
  rw [e]
  have hIs : ∀ i ∈ slotAxes ts h, i < ts.length ∧ h < axLen ts i := slotAxes_valid ts h
  rw [slotTable_paper hL r' hIs, slotAxes_below_top hL hh, slotTableP_rows ts ℓ K r' hh.le]
  tsimp [hrows, tableWords, List.flatMap_map, List.flatMap_assoc, List.getD_eq_getElem, hh]

end SigmaTableTape

end IntegerMultBounds.Schoenhage
