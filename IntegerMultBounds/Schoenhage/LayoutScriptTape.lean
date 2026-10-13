module

public import IntegerMultBounds.Schoenhage.LayoutScript

/-! The §6 layout script on tapes. Every header of a field swap is a power of two
(`bin_two_pow`), possibly times the record length (`bin_two_pow_mul`), so a
stream that writes one `false` per bit of a unary word and closes with a
`true` (`fillOne`) writes it. -/

@[expose] public section

namespace IntegerMultBounds.Schoenhage

open Machine Strm Resampling Script

namespace LayoutScriptTape

/-! ### Binary words of powers of two -/

theorem value_replicate_false_append (x : ℕ) (w : List Bool) :
    Counter.value (List.replicate x false ++ w) = 2 ^ x * Counter.value w := by
  induction x with
  | zero => simp
  | succ x ih => simp [List.replicate_succ, Counter.value, ih, pow_succ]; ring

theorem value_pos_of_canonical {w : List Bool} (h : GrowingCounterData.Canonical w) (hne : w ≠ []) :
    0 < Counter.value w := by
  induction w with
  | nil => exact absurd rfl hne
  | cons b w ih =>
    rcases w with _ | ⟨c, w⟩
    · rcases h with h | h
      · simp at h
      · simp at h; subst h; simp [Counter.value]
    · have hc : GrowingCounterData.Canonical (c :: w) := by
        rcases h with h | h
        · simp at h
        · right; simpa [List.getLast?_cons_cons] using h
      have := ih hc (by simp)
      simp only [Counter.value] at this ⊢; omega

theorem canonical_tail {b : Bool} {w : List Bool} (h : GrowingCounterData.Canonical (b :: w)) :
    GrowingCounterData.Canonical w := by
  rcases w with _ | ⟨c, w⟩
  · left; rfl
  · rcases h with h | h
    · simp at h
    · right; simpa [List.getLast?_cons_cons] using h

/-- Canonical words are determined by their value. -/
theorem canonical_eq : ∀ {a b : List Bool}, GrowingCounterData.Canonical a → GrowingCounterData.Canonical b →
    Counter.value a = Counter.value b → a = b
  | [], [], _, _, _ => rfl
  | [], c :: b, _, hb, h => by
    have := value_pos_of_canonical hb (by simp); rw [← h] at this; simp [Counter.value] at this
  | c :: a, [], ha, _, h => by
    have := value_pos_of_canonical ha (by simp); rw [h] at this; simp [Counter.value] at this
  | x :: a, y :: b, ha, hb, h => by
    simp only [Counter.value] at h
    have hxy : x = y := by
      cases x <;> cases y <;> simp only [Bool.false_eq_true, ite_true, ite_false] at h <;> first | rfl | omega
    subst hxy
    have : Counter.value a = Counter.value b := by
      cases x <;> simp only [Bool.false_eq_true, ite_true, ite_false] at h <;> omega
    rw [canonical_eq (canonical_tail ha) (canonical_tail hb) this]

theorem bin_two_pow_mul (x R : ℕ) (hR : 0 < R) : bin (2 ^ x * R) = List.replicate x false ++ bin R := by
  apply canonical_eq (canonical_bin _)
  · rcases canonical_bin R with h | h
    · have := value_bin R; rw [h] at this; simp [Counter.value] at this; omega
    · right
      rw [List.getLast?_append]
      simp [h]
  · rw [value_bin, value_replicate_false_append, value_bin]

theorem bin_one : bin 1 = [true] := rfl

theorem bin_zero : bin 0 = [] := rfl

theorem bin_two_pow (x : ℕ) : bin (2 ^ x) = List.replicate x false ++ [true] := by
  rw [← mul_one (2 ^ x), bin_two_pow_mul x 1 one_pos, bin_one]

/-! ### Streams -/

/-- One `false` per driver bit, then a closing `true`. -/
abbrev fillOne : Rule 0 where
  Q := Unit
  q0 := ()
  step _ _ _ := ((), some (some false), fun _ => false)
  flush _ := [some true, none]
  B := 2
  hB _ := le_rfl

theorem go_fillOne (w : List Bool) (ws : Fin 0 → List Bool) :
    (go fillOne () w ws).2.1 = (List.replicate w.length false).map some ∧ (go fillOne () w ws).1 = () := by
  induction w generalizing ws with
  | nil => simp [go]
  | cons b w ih => simp [go, ih, List.replicate_succ]

theorem output_fillOne (w : List Bool) (ws : Fin 0 → List Bool) :
    output fillOne w ws = syms [List.replicate w.length false ++ [true]] := by
  simp [output, syms_cons, (go_fillOne w ws).1]

theorem time_fillOne (w : List Bool) (ws : Fin 0 → List Bool) : time fillOne w ws = w.length + 7 := by
  simp [time, rest]

theorem time_fill (c : Bool) (w : List Bool) (ws : Fin 0 → List Bool) : time (Rules.fill c) w ws = w.length + 6 := by
  simp [time, rest]

/-! ### The bank -/

/-- The forward script, accumulated reversed. -/
abbrev gO : Fin 20 := 0
/-- The undo script, each record's words accumulated in reverse. -/
abbrev gU : Fin 20 := 1
/-- The number `k` of moves so far. -/
abbrev gK : Fin 20 := 2
/-- The number `L` of remaining slots. -/
abbrev gL : Fin 20 := 3
/-- The slots `m` in front of the moving slot. -/
abbrev gM : Fin 20 := 4
/-- The slots `ρ` behind it. -/
abbrev gR : Fin 20 := 5
/-- `bin R`, `R` the record length. -/
abbrev gBR : Fin 20 := 6
/-- `bin 0`. -/
abbrev gB0 : Fin 20 := 7
/-- `bin 1`. -/
abbrev gB1 : Fin 20 := 8
/-- Scratch. -/
abbrev gS : Fin 20 := 9
/-- The junk tape. -/
abbrev gJ : Fin 20 := 10
/-- One flag word per axis: long or not. -/
abbrev gFl : Fin 20 := 11
/-- `ones (ℓ - 1)`. -/
abbrev gLm1 : Fin 20 := 12
/-- `ones 1`. -/
abbrev gOne : Fin 20 := 13
/-- One tick per bottom level. -/
abbrev gLev : Fin 20 := 14
/-- One tick per axis. -/
abbrev gAx : Fin 20 := 15
/-- The level's step `ℓ - 1 - b + h`. -/
abbrev gSt : Fin 20 := 16
/-- `ones (ℓ - 1 - b)`. -/
abbrev gC0 : Fin 20 := 17
/-- The exponent `n - m - 1 - ρ` of the move's `P`. -/
abbrev gP : Fin 20 := 18
/-- `ones n`, `n` the address length. -/
abbrev gN : Fin 20 := 19

/-- A unary value with the head past it. -/
def endv (x : ℕ) : WTape := ⟨[ones x], []⟩

/-- Ticks, the head at the first. -/
def ticks (n : ℕ) : WTape := ⟨[], List.replicate n []⟩

/-- A field swap's six words: tag, `P`, `G`, `B`, `h`, `d`, for `P = 2^k`, `G = 2^m`, `B = 2^ρ R`. -/
def swapWords (R k m ρ hh dd : ℕ) : List (List Bool) :=
  [[false], bin (2 ^ k), bin (2 ^ m), bin (2 ^ ρ * R), bin hh, bin dd]

/-! ### One move -/

/-- `ρ = L - m - 1` into `gR`. -/
noncomputable def rhoCalc : Cmd 0 20 :=
  .seq (rewind gL) <| .seq (cpy gL gR (by decide)) <|
  .seq (rewind gR) <| .seq (rewind gM) <| .seq (op1 Rules.drop false gR gM gS (by decide) (by decide) (by decide)) <|
  .seq (clear gR) <| .seq (rewind gS) <| .seq (cpy gS gR (by decide)) <| .seq (clear gS) <|
  .seq (rewind gR) <| .seq (op1 Rules.drop false gR gOne gS (by decide) (by decide) (by decide)) <|
  .seq (rewind gOne) <| .seq (clear gR) <| .seq (rewind gS) <| .seq (cpy gS gR (by decide)) (clear gS)

/-- Subtract the value on `X` from `gP`. -/
noncomputable def subP (X : Fin 20) (h1 : gP ≠ X) (h2 : X ≠ gS) : Cmd 0 20 :=
  .seq (rewind X) <| .seq (rewind gP) <| .seq (op1 Rules.drop false gP X gS h1 (by decide) h2) <|
  .seq (clear gP) <| .seq (rewind gS) <| .seq (cpy gS gP (by decide)) (clear gS)

/-- `P = n - m - 1 - ρ` into `gP`. -/
noncomputable def pCalc : Cmd 0 20 :=
  .seq (cpy gN gP (by decide)) <| .seq (rewind gN) <| .seq (subP gM (by decide) (by decide)) <|
  .seq (subP gOne (by decide) (by decide)) <| .seq (rewind gOne) (subP gR (by decide) (by decide))

/-- The move's forward words onto `gO`. -/
noncomputable def emitFwd : Cmd 0 20 :=
  .seq (emit [[false]] gO) <|
  .seq (rewind gP) <| .seq (op0 fillOne false gP gO (by decide)) <|
  .seq (rewind gM) <| .seq (op0 fillOne false gM gO (by decide)) <|
  .seq (rewind gR) <| .seq (op0 (Rules.fill false) false gR gO (by decide)) <|
  .seq (op0 Rules.copy true gBR gO (by decide)) <| .seq (rewind gBR) <|
  .seq (cpy gB0 gO (by decide)) <| .seq (rewind gB0) <|
  .seq (cpy gB1 gO (by decide)) (rewind gB1)

/-- The undo record's words onto `gU`, last word first. -/
noncomputable def emitUndo : Cmd 0 20 :=
  .seq (cpy gB0 gU (by decide)) <| .seq (rewind gB0) <|
  .seq (cpy gB1 gU (by decide)) <| .seq (rewind gB1) <|
  .seq (rewind gR) <| .seq (op0 (Rules.fill false) false gR gU (by decide)) <|
  .seq (op0 Rules.copy true gBR gU (by decide)) <| .seq (rewind gBR) <|
  .seq (rewind gM) <| .seq (op0 fillOne false gM gU (by decide)) <|
  .seq (rewind gP) <| .seq (op0 fillOne false gP gU (by decide)) (emit [[false]] gU)

/-- Count the move: `k + 1`, `L - 1`, and clear `ρ`. -/
noncomputable def advance : Cmd 0 20 :=
  .seq (clear gR) <| .seq (clear gP) <| .seq (op0 Rules.copy true gOne gK (by decide)) <|
  .seq (rewind gOne) <| .seq (rewind gL) <| .seq (op1 Rules.drop false gL gOne gS (by decide) (by decide) (by decide)) <|
  .seq (rewind gOne) <| .seq (clear gL) <| .seq (rewind gS) <| .seq (cpy gS gL (by decide)) (clear gS)

/-- One move: compute `ρ`, write the forward and undo words, count it. -/
noncomputable def emitMove : Cmd 0 20 := .seq rhoCalc <| .seq pCalc <| .seq emitFwd <| .seq emitUndo advance

set_option maxHeartbeats 8000000 in
theorem runs_rhoCalc {L m : ℕ} (σ : Fin 20 → WTape) (hL : σ gL = endv L) (hM : σ gM = endv m)
    (hR : σ gR = emp) (hS : σ gS = emp) (hOne : σ gOne = reg (ones 1)) :
    Runs rhoCalc σ (· = Function.update σ gR (endv (L - m - 1))) (20 * L + 4 * m + 200) := by
  have t1 : time Rules.drop (List.replicate L true) (fun _ => List.replicate m true) ≤ L + m + 6 :=
    (time_le Rules.drop (ones L) (fun _ => ones m) m (fun _ => by simp)).trans (by simp)
  have t2 : time Rules.drop (List.replicate (L - m) true) (fun _ => [true]) ≤ L - m + 1 + 6 :=
    (time_le Rules.drop (ones (L - m)) (fun _ => ones 1) 1 (fun _ => by simp)).trans (by simp)
  apply Runs.of_wp
  simp only [rhoCalc, cpy, WP, wp_op0, wp_op1, wp_rewind, wp_clear]
  tsimp [hL, hM, hR, hS, hOne, endv, emp, reg, Rules.output_copy, Rules.output_drop, ones, List.drop_replicate]
  refine ⟨?_, ?_⟩
  · funext i; fin_cases i <;> first | rfl | tsimp [hL, hM, hR, hS, hOne, endv, emp, reg, ones, Nat.sub_sub]
  · simp [time_copy, clen, WTape.words]; omega

set_option maxHeartbeats 8000000 in
theorem runs_subP_M {P x : ℕ} (σ : Fin 20 → WTape) (hP : σ gP = endv P) (hX : σ gM = endv x)
    (hS : σ gS = emp) :
    Runs (subP gM (by decide) (by decide)) σ (· = Function.update (Function.update σ gM (endv x)) gP (endv (P - x)))
      (8 * P + 4 * x + 60) := by
  have t1 : time Rules.drop (List.replicate P true) (fun _ => List.replicate x true) ≤ P + x + 6 :=
    (time_le Rules.drop (ones P) (fun _ => ones x) x (fun _ => by simp)).trans (by simp)
  apply Runs.of_wp
  simp only [subP, cpy, WP, wp_op0, wp_op1, wp_rewind, wp_clear]
  tsimp [hP, hX, hS, endv, emp, reg, Rules.output_copy, Rules.output_drop, ones, List.drop_replicate]
  refine ⟨?_, ?_⟩
  · funext i; fin_cases i <;> first | rfl | tsimp [hP, hX, hS, endv, emp, reg, ones]
  · simp [time_copy, clen, WTape.words]; omega

set_option maxHeartbeats 8000000 in
theorem runs_subP_One {P x : ℕ} (σ : Fin 20 → WTape) (hP : σ gP = endv P) (hX : σ gOne = reg (ones x))
    (hS : σ gS = emp) :
    Runs (subP gOne (by decide) (by decide)) σ (· = Function.update (Function.update σ gOne (endv x)) gP (endv (P - x)))
      (8 * P + 4 * x + 60) := by
  have t1 : time Rules.drop (List.replicate P true) (fun _ => List.replicate x true) ≤ P + x + 6 :=
    (time_le Rules.drop (ones P) (fun _ => ones x) x (fun _ => by simp)).trans (by simp)
  apply Runs.of_wp
  simp only [subP, cpy, WP, wp_op0, wp_op1, wp_rewind, wp_clear]
  tsimp [hP, hX, hS, endv, emp, reg, Rules.output_copy, Rules.output_drop, ones, List.drop_replicate]
  refine ⟨?_, ?_⟩
  · funext i; fin_cases i <;> first | rfl | tsimp [hP, hX, hS, endv, emp, reg, ones]
  · simp [time_copy, clen, WTape.words]; omega

set_option maxHeartbeats 8000000 in
theorem runs_subP_R {P x : ℕ} (σ : Fin 20 → WTape) (hP : σ gP = endv P) (hX : σ gR = endv x)
    (hS : σ gS = emp) :
    Runs (subP gR (by decide) (by decide)) σ (· = Function.update (Function.update σ gR (endv x)) gP (endv (P - x)))
      (8 * P + 4 * x + 60) := by
  have t1 : time Rules.drop (List.replicate P true) (fun _ => List.replicate x true) ≤ P + x + 6 :=
    (time_le Rules.drop (ones P) (fun _ => ones x) x (fun _ => by simp)).trans (by simp)
  apply Runs.of_wp
  simp only [subP, cpy, WP, wp_op0, wp_op1, wp_rewind, wp_clear]
  tsimp [hP, hX, hS, endv, emp, reg, Rules.output_copy, Rules.output_drop, ones, List.drop_replicate]
  refine ⟨?_, ?_⟩
  · funext i; fin_cases i <;> first | rfl | tsimp [hP, hX, hS, endv, emp, reg, ones]
  · simp [time_copy, clen, WTape.words]; omega

set_option maxHeartbeats 8000000 in
theorem runs_pCalc {n m ρ : ℕ} (σ : Fin 20 → WTape) (hN : σ gN = reg (ones n)) (hM : σ gM = endv m)
    (hRho : σ gR = endv ρ) (hP : σ gP = emp) (hS : σ gS = emp) (hOne : σ gOne = reg (ones 1)) :
    Runs pCalc σ (· = Function.update σ gP (endv (n - m - 1 - ρ))) (30 * n + 8 * m + 8 * ρ + 300) := by
  have s1 := runs_cpy (a := 0) (show gN ≠ gP by decide) σ (by simp [hN, reg]) (by simp [hP, emp])
  set σ₁ := Function.update (Function.update σ gN (σ gN).next) gP ((σ gP).put false [(σ gN).cur]) with hσ₁
  have s2 := runs_rewind (a := 0) gN σ₁
  set σ₂ := Function.update σ₁ gN ⟨[], (σ₁ gN).left.reverse ++ (σ₁ gN).right⟩ with hσ₂
  have s3 := runs_subP_M (P := n) (x := m) σ₂ (by tsimp [hσ₂, hσ₁, hN, hP, reg, emp, endv, WTape.put])
    (by tsimp [hσ₂, hσ₁, hM, endv]) (by tsimp [hσ₂, hσ₁, hS])
  set σ₃ := Function.update (Function.update σ₂ gM (endv m)) gP (endv (n - m)) with hσ₃
  have s4 := runs_subP_One (P := n - m) (x := 1) σ₃ (by tsimp [hσ₃]) (by tsimp [hσ₃, hσ₂, hσ₁, hOne])
    (by tsimp [hσ₃, hσ₂, hσ₁, hS])
  set σ₄ := Function.update (Function.update σ₃ gOne (endv 1)) gP (endv (n - m - 1)) with hσ₄
  have s5 := runs_rewind (a := 0) gOne σ₄
  set σ₅ := Function.update σ₄ gOne ⟨[], (σ₄ gOne).left.reverse ++ (σ₄ gOne).right⟩ with hσ₅
  have s6 := runs_subP_R (P := n - m - 1) (x := ρ) σ₅ (by tsimp [hσ₅, hσ₄]) (by tsimp [hσ₅, hσ₄, hσ₃, hσ₂, hσ₁, hRho, endv])
    (by tsimp [hσ₅, hσ₄, hσ₃, hσ₂, hσ₁, hS])
  refine (Runs.then s1 (Runs.then s2 (Runs.then s3 (Runs.then s4 (Runs.then s5 s6))))).mono (fun τ he => ?_) ?_
  · rw [he]; funext i; fin_cases i <;> first | rfl | tsimp [hσ₅, hσ₄, hσ₃, hσ₂, hσ₁, hN, hM, hRho, hP, hOne, reg, endv,
      emp, WTape.put, WTape.next, ones]
  · tsimp [hσ₄, hσ₁, hN, hP, reg, emp, endv, WTape.put, WTape.next, WTape.cur, clen]
    have : n - m ≤ n := Nat.sub_le _ _
    have : n - m - 1 ≤ n := by omega
    omega

set_option maxHeartbeats 8000000 in
theorem runs_emitFwd {R k m ρ : ℕ} (hR0 : 0 < R) (σ : Fin 20 → WTape) {O : List (List Bool)}
    (hO : σ gO = ⟨O, []⟩) (hK : σ gP = endv k) (hM : σ gM = endv m) (hRho : σ gR = endv ρ)
    (hBR : σ gBR = reg (bin R)) (hB0 : σ gB0 = reg []) (hB1 : σ gB1 = reg [true]) :
    Runs emitFwd σ (· = Function.update σ gO ⟨(swapWords R k m ρ 0 1).reverse ++ O, []⟩)
      (4 * (k + m + ρ + (bin R).length) + 120) := by
  have hbR : bin R ≠ [] := by
    intro h; have := value_bin R; rw [h] at this; simp [Counter.value] at this; omega
  have hpm : ∀ x, bin (2 ^ x * R) = List.replicate x false ++ bin R := fun x => bin_two_pow_mul x R hR0
  apply Runs.of_wp
  simp only [emitFwd, cpy, WP, wp_op0, wp_rewind, wp_emit]
  tsimp [hO, hK, hM, hRho, hBR, hB0, hB1, endv, reg, Rules.output_copy, output_fillOne,
    Rules.output_fill, hbR]
  refine ⟨?_, ?_⟩
  · funext i; fin_cases i <;> first | rfl | tsimp [hO, hK, hM, hRho, hBR, hB0, hB1, endv, reg, swapWords,
      bin_two_pow, hpm, bin_zero, bin_one, WTape.put]
  · simp [time_copy, time_fillOne, time_fill, length_ones]; omega

set_option maxHeartbeats 8000000 in
theorem runs_emitUndo {R k m ρ : ℕ} (hR0 : 0 < R) (σ : Fin 20 → WTape) {U : List (List Bool)}
    (hU : σ gU = ⟨U, []⟩) (hK : σ gP = endv k) (hM : σ gM = endv m) (hRho : σ gR = endv ρ)
    (hBR : σ gBR = reg (bin R)) (hB0 : σ gB0 = reg []) (hB1 : σ gB1 = reg [true]) :
    Runs emitUndo σ (· = Function.update σ gU ⟨swapWords R k m ρ 1 0 ++ U, []⟩)
      (4 * (k + m + ρ + (bin R).length) + 120) := by
  have hbR : bin R ≠ [] := by
    intro h; have := value_bin R; rw [h] at this; simp [Counter.value] at this; omega
  have hpm : ∀ x, bin (2 ^ x * R) = List.replicate x false ++ bin R := fun x => bin_two_pow_mul x R hR0
  apply Runs.of_wp
  simp only [emitUndo, cpy, WP, wp_op0, wp_rewind, wp_emit]
  tsimp [hU, hK, hM, hRho, hBR, hB0, hB1, endv, reg, Rules.output_copy, output_fillOne,
    Rules.output_fill, hbR]
  refine ⟨?_, ?_⟩
  · funext i; fin_cases i <;> first | rfl | tsimp [hU, hK, hM, hRho, hBR, hB0, hB1, endv, reg, swapWords,
      bin_two_pow, hpm, bin_zero, bin_one, WTape.put]
  · simp [time_copy, time_fillOne, time_fill, length_ones]; omega

set_option maxHeartbeats 8000000 in
theorem runs_advance {k L ρ P : ℕ} (σ : Fin 20 → WTape) (hK : σ gK = endv k) (hL : σ gL = endv L)
    (hRho : σ gR = endv ρ) (hS : σ gS = emp) (hOne : σ gOne = reg (ones 1)) (hP : σ gP = endv P) :
    Runs advance σ (· = Function.update (Function.update (Function.update (Function.update σ gR emp) gP emp)
      gK (endv (k + 1))) gL (endv (L - 1))) (2 * ρ + 2 * P + 12 * L + 4 * k + 90) := by
  have t1 : time Rules.drop (List.replicate L true) (fun _ => [true]) ≤ L + 1 + 6 :=
    (time_le Rules.drop (ones L) (fun _ => ones 1) 1 (fun _ => by simp)).trans (by simp)
  apply Runs.of_wp
  simp only [advance, cpy, WP, wp_op0, wp_op1, wp_rewind, wp_clear]
  tsimp [hK, hL, hRho, hS, hOne, hP, endv, emp, reg, Rules.output_copy, Rules.output_drop, ones,
    List.drop_replicate]
  refine ⟨?_, ?_⟩
  · funext i; fin_cases i <;> first | rfl | tsimp [hK, hL, hRho, hS, hOne, hP, endv, emp, reg, ones,
      WTape.put, List.replicate_succ']
  · simp [time_copy, clen, WTape.words]; omega

/-! ### The generator's states -/

/-- The bank: outputs `O`, `U`, counters `k`, `L`, `m`, the level step `s`, loop tapes, constants. -/
def bank (R lm1 c0 n : ℕ) (O U : List (List Bool)) (k L m s : ℕ) (fl ax lev : WTape) : Fin 20 → WTape :=
  fun i => match i.val with
  | 0 => ⟨O, []⟩ | 1 => ⟨U, []⟩ | 2 => endv k | 3 => endv L | 4 => endv m
  | 6 => reg (bin R) | 7 => reg [] | 8 => reg [true] | 11 => fl | 12 => reg (ones lm1)
  | 13 => reg (ones 1) | 14 => lev | 15 => ax | 16 => reg (ones s) | 17 => reg (ones c0)
  | 19 => reg (ones n)
  | _ => emp

set_option maxHeartbeats 8000000 in
/-- One move: the forward record onto `gO`, the undo record (reversed) onto `gU`, `k + 1`, `L - 1`. -/
theorem runs_emitMove {R lm1 c0 n : ℕ} (hR0 : 0 < R) {O U : List (List Bool)} {k L m s : ℕ}
    {fl ax lev : WTape} :
    Runs emitMove (bank R lm1 c0 n O U k L m s fl ax lev)
      (· = bank R lm1 c0 n ((swapWords R (n - m - 1 - (L - m - 1)) m (L - m - 1) 0 1).reverse ++ O)
        (swapWords R (n - m - 1 - (L - m - 1)) m (L - m - 1) 1 0 ++ U) (k + 1) (L - 1) m s fl ax lev)
      (60 * L + 30 * m + 12 * k + 40 * n + 8 * (bin R).length + 1000) := by
  set ρ := L - m - 1 with hρ
  set P := n - m - 1 - ρ with hP
  set σ := bank R lm1 c0 n O U k L m s fl ax lev with hσ
  have s1 := runs_rhoCalc (L := L) (m := m) σ (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
  set σ₁ := Function.update σ gR (endv ρ) with hσ₁
  have s1b := runs_pCalc (n := n) (m := m) (ρ := ρ) σ₁ (by tsimp [hσ₁, hσ, bank]) (by tsimp [hσ₁, hσ, bank])
    (by tsimp [hσ₁]) (by tsimp [hσ₁, hσ, bank]) (by tsimp [hσ₁, hσ, bank]) (by tsimp [hσ₁, hσ, bank])
  set σ₁' := Function.update σ₁ gP (endv P) with hσ₁'
  have s2 := runs_emitFwd (R := R) (k := P) (m := m) (ρ := ρ) hR0 σ₁' (O := O)
    (by tsimp [hσ₁', hσ₁, hσ, bank]) (by tsimp [hσ₁']) (by tsimp [hσ₁', hσ₁, hσ, bank]) (by tsimp [hσ₁', hσ₁])
    (by tsimp [hσ₁', hσ₁, hσ, bank]) (by tsimp [hσ₁', hσ₁, hσ, bank]) (by tsimp [hσ₁', hσ₁, hσ, bank])
  set σ₂ := Function.update σ₁' gO ⟨(swapWords R P m ρ 0 1).reverse ++ O, []⟩ with hσ₂
  have s3 := runs_emitUndo (R := R) (k := P) (m := m) (ρ := ρ) hR0 σ₂ (U := U)
    (by tsimp [hσ₂, hσ₁', hσ₁, hσ, bank]) (by tsimp [hσ₂, hσ₁']) (by tsimp [hσ₂, hσ₁', hσ₁, hσ, bank])
    (by tsimp [hσ₂, hσ₁', hσ₁]) (by tsimp [hσ₂, hσ₁', hσ₁, hσ, bank]) (by tsimp [hσ₂, hσ₁', hσ₁, hσ, bank])
    (by tsimp [hσ₂, hσ₁', hσ₁, hσ, bank])
  set σ₃ := Function.update σ₂ gU ⟨swapWords R P m ρ 1 0 ++ U, []⟩ with hσ₃
  have s4 := runs_advance (k := k) (L := L) (ρ := ρ) (P := P) σ₃ (by tsimp [hσ₃, hσ₂, hσ₁', hσ₁, hσ, bank])
    (by tsimp [hσ₃, hσ₂, hσ₁', hσ₁, hσ, bank]) (by tsimp [hσ₃, hσ₂, hσ₁', hσ₁])
    (by tsimp [hσ₃, hσ₂, hσ₁', hσ₁, hσ, bank]) (by tsimp [hσ₃, hσ₂, hσ₁', hσ₁, hσ, bank])
    (by tsimp [hσ₃, hσ₂, hσ₁'])
  refine (Runs.then s1 (Runs.then s1b (Runs.then s2 (Runs.then s3 s4)))).mono (fun τ e => ?_) ?_
  · rw [e]; funext i; fin_cases i <;> rfl
  · have : ρ ≤ L := by omega
    have : P ≤ n := by omega
    omega

/-! ### The top moves -/

theorem ones_append' (m w : ℕ) : ones m ++ ones w = ones (m + w) := by unfold ones; rw [List.replicate_add]

/-- Add the constant on `s` to the value on `d`. -/
noncomputable def addTo (s d : Fin 20) (h : s ≠ d) : Cmd 0 20 := .seq (op0 Rules.copy true s d h) (rewind s)

set_option maxHeartbeats 4000000 in
theorem runs_addTo {s d : Fin 20} (h : s ≠ d) {c v : ℕ} (σ : Fin 20 → WTape) (hs : σ s = reg (ones c))
    (hd : σ d = endv v) :
    Runs (addTo s d h) σ (· = Function.update σ d (endv (v + c))) (2 * c + 10) := by
  apply Runs.of_wp
  simp only [addTo, WP, wp_op0, wp_rewind]
  simp only [Function.update_apply, hs, hd, h, ↓reduceIte, endv, reg, WTape.next_mk,
    WTape.cur_mk, List.headD_cons, List.tail_cons, Rules.output_copy, ↓parse_syms]
  refine ⟨⟨by simp, by simp, by simp, fun _ => ⟨by simp, by simp⟩⟩, ?_, ?_⟩
  · funext i
    simp only [Function.update_apply]
    split_ifs <;> subst_vars <;> simp_all [ones_append', WTape.put, reg, endv]
  · simp [time_copy]; omega

/-- One axis of the top moves: a move when the axis is long, then `m + (ℓ - 1)`. -/
noncomputable def topBody : Cmd 0 20 :=
  .seq (.cond gFl emitMove (rewind gJ)) <| .seq (skp gFl gJ (by decide)) (addTo gLm1 gM (by decide))

/-- The top moves' outputs and counters after the axes with flags `f`. -/
def topRun (R lm1 n : ℕ) : List Bool → List (List Bool) → List (List Bool) → ℕ → ℕ → ℕ →
    List (List Bool) × List (List Bool) × ℕ × ℕ × ℕ
  | [], O, U, k, L, m => (O, U, k, L, m)
  | true :: f, O, U, k, L, m => topRun R lm1 n f ((swapWords R (n - m - 1 - (L - m - 1)) m (L - m - 1) 0 1).reverse ++ O)
      (swapWords R (n - m - 1 - (L - m - 1)) m (L - m - 1) 1 0 ++ U) (k + 1) (L - 1) (m + lm1)
  | false :: f, O, U, k, L, m => topRun R lm1 n f O U k L (m + lm1)

/-- The cost of one axis. -/
def topCost (N R lm1 : ℕ) : ℕ := 150 * N + 8 * (bin R).length + 4 * lm1 + 1100

set_option maxHeartbeats 8000000 in
theorem runs_topLoop {R lm1 c0 n s N : ℕ} (hR0 : 0 < R) (hnN : n ≤ N) {ax lev : WTape} :
    ∀ (f : List Bool) (done O U : List (List Bool)) (k L m : ℕ), k + f.length ≤ N → L ≤ N →
      m + f.length * lm1 ≤ N →
      Runs (.loop gFl topBody) (bank R lm1 c0 n O U k L m s ⟨done, f.map fun b => [b]⟩ ax lev)
        (· = bank R lm1 c0 n (topRun R lm1 n f O U k L m).1 (topRun R lm1 n f O U k L m).2.1
          (topRun R lm1 n f O U k L m).2.2.1 (topRun R lm1 n f O U k L m).2.2.2.1
          (topRun R lm1 n f O U k L m).2.2.2.2 s ⟨(f.map fun b => [b]).reverse ++ done, []⟩ ax lev)
        (f.length * (topCost N R lm1 + 2))
  | [], done, O, U, k, L, m, _, _, _ => by
    refine (Runs.loop_done (by simp [bank]) rfl).mono (fun τ e => ?_) (by simp)
    rw [← e]; rfl
  | b :: f, done, O, U, k, L, m, hk, hL, hm => by
    set σ := bank R lm1 c0 n O U k L m s ⟨done, (b :: f).map fun b => [b]⟩ ax lev with hσ
    simp only [List.length_cons] at hm
    -- the move, if any
    have hcond : Runs (.cond gFl emitMove (rewind gJ)) σ
        (· = bank R lm1 c0 n (if b then (swapWords R (n - m - 1 - (L - m - 1)) m (L - m - 1) 0 1).reverse ++ O else O)
          (if b then swapWords R (n - m - 1 - (L - m - 1)) m (L - m - 1) 1 0 ++ U else U) (if b then k + 1 else k)
          (if b then L - 1 else L) m s ⟨done, (b :: f).map fun b => [b]⟩ ax lev)
        (60 * L + 30 * m + 12 * k + 40 * n + 8 * (bin R).length + 1010) := by
      cases b
      · refine (Runs.cond_false (by simp [hσ, bank, startsOne_mk]) (runs_rewind gJ σ)).mono
          (fun τ e => ?_) (by simp [hσ, bank, clen, emp])
        rw [e]; funext i; fin_cases i <;> rfl
      · exact (Runs.cond_true (by simp [bank, startsOne_mk]) (runs_emitMove hR0)).mono
          (fun τ e => by rw [e]; rfl) (by omega)
    set σ₁ := bank R lm1 c0 n (if b then (swapWords R (n - m - 1 - (L - m - 1)) m (L - m - 1) 0 1).reverse ++ O else O)
          (if b then swapWords R (n - m - 1 - (L - m - 1)) m (L - m - 1) 1 0 ++ U else U) (if b then k + 1 else k)
          (if b then L - 1 else L) m s ⟨done, (b :: f).map fun b => [b]⟩ ax lev with hσ₁
    have s2 := runs_skp (a := 0) (show gFl ≠ gJ by decide) σ₁ (by simp [hσ₁, bank]) (by simp [hσ₁, bank, emp])
    set σ₂ := Function.update σ₁ gFl (σ₁ gFl).next with hσ₂
    have s3 := runs_addTo (c := lm1) (v := m) (show gLm1 ≠ gM by decide) σ₂ (by tsimp [hσ₂, hσ₁, bank])
      (by tsimp [hσ₂, hσ₁, bank])
    set σ₃ := Function.update σ₂ gM (endv (m + lm1)) with hσ₃
    have hσ₃' : σ₃ = bank R lm1 c0 n (if b then (swapWords R (n - m - 1 - (L - m - 1)) m (L - m - 1) 0 1).reverse ++ O else O)
          (if b then swapWords R (n - m - 1 - (L - m - 1)) m (L - m - 1) 1 0 ++ U else U) (if b then k + 1 else k)
          (if b then L - 1 else L) (m + lm1) s ⟨[b] :: done, f.map fun b => [b]⟩ ax lev := by
      funext i; fin_cases i <;> rfl
    have ih := runs_topLoop (R := R) (lm1 := lm1) (c0 := c0) (n := n) (s := s) (N := N) (ax := ax) (lev := lev) hR0 hnN f
      ([b] :: done) (if b then (swapWords R (n - m - 1 - (L - m - 1)) m (L - m - 1) 0 1).reverse ++ O else O)
      (if b then swapWords R (n - m - 1 - (L - m - 1)) m (L - m - 1) 1 0 ++ U else U) (if b then k + 1 else k)
      (if b then L - 1 else L) (m + lm1)
      (by simp only [List.length_cons] at hk; split_ifs <;> omega) (by split_ifs <;> omega)
      (by rw [Nat.succ_mul] at hm; omega)
    rw [← hσ₃'] at ih
    refine (Runs.loop_step (by simp [hσ, bank]) ((Runs.then hcond (Runs.then s2 s3)).mono
      (fun τ e => by rw [e]; exact ih) le_rfl)).mono (fun τ e => ?_) ?_
    · rw [e]; cases b <;> simp [topRun, List.reverse_cons]
    · have hc1 : (σ₁ gFl).cur.length + 5 = 6 := by simp [hσ₁, bank, WTape.cur]
      rw [hc1]
      simp only [List.length_cons] at hk
      have hmN : m ≤ N := by nlinarith
      have hlN : lm1 ≤ N := by nlinarith
      have : 60 * L + 30 * m + 12 * k + 40 * n + 8 * (bin R).length + 1010 + 1 + (6 + 1 + (2 * lm1 + 10)) ≤
          topCost N R lm1 := by simp only [topCost]; omega
      rw [List.length_cons, Nat.add_mul, one_mul]; omega

/-! ### The bottom moves -/

/-- One axis of a bottom level: the move, then `m + s`. -/
noncomputable def levelBody : Cmd 0 20 :=
  .seq emitMove <| .seq (addTo gSt gM (by decide)) (skp gAx gJ (by decide))

/-- Subtract one from the level step. -/
noncomputable def decStep : Cmd 0 20 :=
  .seq (op1 Rules.drop false gSt gOne gS (by decide) (by decide) (by decide)) <|
  .seq (rewind gOne) <| .seq (clear gSt) <| .seq (rewind gS) <| .seq (cpy gS gSt (by decide)) <|
  .seq (clear gS) (rewind gSt)

/-- Load `m = ℓ - 1 - b`. -/
noncomputable def loadM : Cmd 0 20 := .seq (clear gM) <| .seq (cpy gC0 gM (by decide)) (rewind gC0)

/-- One bottom level: `m = ℓ - 1 - b`, every axis, then the next level's step `s - 1`. -/
noncomputable def levelStep : Cmd 0 20 :=
  .seq loadM <| .seq (.loop gAx levelBody) <| .seq (rewind gAx) <| .seq decStep (skp gLev gJ (by decide))

/-- A level's outputs and counters after `e` axes. -/
def levRun (R s n : ℕ) : ℕ → List (List Bool) → List (List Bool) → ℕ → ℕ → ℕ →
    List (List Bool) × List (List Bool) × ℕ × ℕ × ℕ
  | 0, O, U, k, L, m => (O, U, k, L, m)
  | e + 1, O, U, k, L, m => levRun R s n e ((swapWords R (n - m - 1 - (L - m - 1)) m (L - m - 1) 0 1).reverse ++ O)
      (swapWords R (n - m - 1 - (L - m - 1)) m (L - m - 1) 1 0 ++ U) (k + 1) (L - 1) (m + s)

/-- The cost of one axis of a level. -/
def levCost (N R : ℕ) : ℕ := 150 * N + 8 * (bin R).length + 1100

set_option maxHeartbeats 8000000 in
theorem runs_levelLoop {R lm1 c0 n s N : ℕ} (hR0 : 0 < R) (hnN : n ≤ N) {fl lev : WTape} :
    ∀ (e : ℕ) (done O U : List (List Bool)) (k L m : ℕ), k + e ≤ N → L ≤ N → m + e * s ≤ N →
      Runs (.loop gAx levelBody) (bank R lm1 c0 n O U k L m s fl ⟨done, List.replicate e []⟩ lev)
        (· = bank R lm1 c0 n (levRun R s n e O U k L m).1 (levRun R s n e O U k L m).2.1
          (levRun R s n e O U k L m).2.2.1 (levRun R s n e O U k L m).2.2.2.1
          (levRun R s n e O U k L m).2.2.2.2 s fl ⟨List.replicate e [] ++ done, []⟩ lev)
        (e * (levCost N R + 2))
  | 0, done, O, U, k, L, m, _, _, _ => by
    refine (Runs.loop_done (by simp [bank]) rfl).mono (fun τ he => ?_) (by simp)
    rw [← he]; rfl
  | e + 1, done, O, U, k, L, m, hk, hL, hm => by
    set σ := bank R lm1 c0 n O U k L m s fl ⟨done, List.replicate (e + 1) []⟩ lev with hσ
    have s1 := runs_emitMove (lm1 := lm1) (c0 := c0) (n := n) (O := O) (U := U) (k := k) (L := L) (m := m) (s := s)
      (fl := fl) (ax := ⟨done, List.replicate (e + 1) []⟩) (lev := lev) hR0
    set σ₁ := bank R lm1 c0 n ((swapWords R (n - m - 1 - (L - m - 1)) m (L - m - 1) 0 1).reverse ++ O)
        (swapWords R (n - m - 1 - (L - m - 1)) m (L - m - 1) 1 0 ++ U) (k + 1) (L - 1) m s fl ⟨done, List.replicate (e + 1) []⟩ lev
      with hσ₁
    have s2 := runs_addTo (c := s) (v := m) (show gSt ≠ gM by decide) σ₁ (by tsimp [hσ₁, bank])
      (by tsimp [hσ₁, bank])
    set σ₂ := Function.update σ₁ gM (endv (m + s)) with hσ₂
    have s3 := runs_skp (a := 0) (show gAx ≠ gJ by decide) σ₂ (by tsimp [hσ₂, hσ₁, bank])
      (by tsimp [hσ₂, hσ₁, bank, emp])
    have hσ₃ : Function.update σ₂ gAx (σ₂ gAx).next = bank R lm1 c0 n ((swapWords R (n - m - 1 - (L - m - 1)) m (L - m - 1) 0 1).reverse ++ O)
        (swapWords R (n - m - 1 - (L - m - 1)) m (L - m - 1) 1 0 ++ U) (k + 1) (L - 1) (m + s) s fl
        ⟨[] :: done, List.replicate e []⟩ lev := by
      funext i; fin_cases i <;> first | rfl | simp [hσ₂, hσ₁, bank, WTape.next, List.replicate_succ]
    have ih := runs_levelLoop (R := R) (lm1 := lm1) (c0 := c0) (n := n) (s := s) (N := N) (fl := fl) (lev := lev) hR0 hnN e
      ([] :: done) ((swapWords R (n - m - 1 - (L - m - 1)) m (L - m - 1) 0 1).reverse ++ O) (swapWords R (n - m - 1 - (L - m - 1)) m (L - m - 1) 1 0 ++ U)
      (k + 1) (L - 1) (m + s) (by omega) (by omega) (by rw [Nat.add_mul, one_mul] at hm; omega)
    rw [← hσ₃] at ih
    refine (Runs.loop_step (by simp [bank]) ((Runs.then s1 (Runs.then s2 s3)).mono
      (fun τ he => by rw [he]; exact ih) le_rfl)).mono (fun τ he => ?_) ?_
    · rw [he]; simp only [levRun]
      rw [show List.replicate (e + 1) ([] : List Bool) ++ done = List.replicate e [] ++ [] :: done by
        rw [List.replicate_succ', List.append_assoc, List.singleton_append]]
    · have hc1 : (σ₂ gAx).cur.length + 5 = 5 := by tsimp [hσ₂, hσ₁, bank, WTape.cur, List.replicate_succ]
      rw [hc1]
      rw [Nat.add_mul, one_mul] at hm
      have hsN : s ≤ N := by nlinarith
      have : 60 * L + 30 * m + 12 * k + 40 * n + 8 * (bin R).length + 1000 + 1 + (2 * s + 10 + 1 + 5) ≤
          levCost N R := by simp only [levCost]; omega
      rw [Nat.add_mul, one_mul]; omega

set_option maxHeartbeats 8000000 in
theorem runs_decStep {s : ℕ} (σ : Fin 20 → WTape) (hSt : σ gSt = reg (ones s)) (hS : σ gS = emp)
    (hOne : σ gOne = reg (ones 1)) :
    Runs decStep σ (· = Function.update σ gSt (reg (ones (s - 1)))) (8 * s + 60) := by
  have t1 : time Rules.drop (List.replicate s true) (fun _ => [true]) ≤ s + 1 + 6 :=
    (time_le Rules.drop (ones s) (fun _ => ones 1) 1 (fun _ => by simp)).trans (by simp)
  apply Runs.of_wp
  simp only [decStep, cpy, WP, wp_op0, wp_op1, wp_rewind, wp_clear]
  tsimp [hSt, hS, hOne, emp, reg, Rules.output_copy, Rules.output_drop, ones, List.drop_replicate]
  refine ⟨?_, ?_⟩
  · funext i; fin_cases i <;> first | rfl | tsimp [hSt, hS, hOne, emp, reg, ones]
  · simp [time_copy, clen, WTape.words]; omega

/-- The bottom levels' outputs and counters: levels with steps `s, s - 1, …`, each over `D` axes from
`m = c₀`. -/
def botRun (R c0 D n : ℕ) : ℕ → List (List Bool) → List (List Bool) → ℕ → ℕ → ℕ → ℕ →
    List (List Bool) × List (List Bool) × ℕ × ℕ × ℕ × ℕ
  | 0, O, U, k, L, m, s => (O, U, k, L, m, s)
  | c + 1, O, U, k, L, _, s =>
    botRun R c0 D n c (levRun R s n D O U k L c0).1 (levRun R s n D O U k L c0).2.1 (levRun R s n D O U k L c0).2.2.1
      (levRun R s n D O U k L c0).2.2.2.1 (levRun R s n D O U k L c0).2.2.2.2 (s - 1)

theorem levRun_k (R s n : ℕ) : ∀ (e : ℕ) (O U : List (List Bool)) (k L m : ℕ), (levRun R s n e O U k L m).2.2.1 = k + e
  | 0, _, _, _, _, _ => rfl
  | e + 1, _, _, _, _, _ => by rw [levRun, levRun_k]; omega

theorem levRun_L (R s n : ℕ) : ∀ (e : ℕ) (O U : List (List Bool)) (k L m : ℕ), (levRun R s n e O U k L m).2.2.2.1 = L - e
  | 0, _, _, _, _, _ => rfl
  | e + 1, _, _, _, _, _ => by rw [levRun, levRun_L]; omega

/-- The cost of one level. -/
def levelCost (N R D : ℕ) : ℕ := D * (levCost N R + 2) + 20 * N + 2 * D + 300

set_option maxHeartbeats 8000000 in
theorem runs_levelStep {R lm1 c0 n N D : ℕ} (hR0 : 0 < R) {fl : WTape} {done : List (List Bool)} {lev : List (List Bool)}
    {O U : List (List Bool)} {k L m s : ℕ} (hk : k + D ≤ N) (hL : L ≤ N) (hc : c0 + D * s ≤ N) (hm : m ≤ N)
    (hDN : D ≤ N) (hsN : s ≤ N) (hnN : n ≤ N) :
    Runs levelStep (bank R lm1 c0 n O U k L m s fl ⟨[], List.replicate D []⟩ ⟨done, [] :: lev⟩)
      (· = bank R lm1 c0 n (levRun R s n D O U k L c0).1 (levRun R s n D O U k L c0).2.1
          (levRun R s n D O U k L c0).2.2.1 (levRun R s n D O U k L c0).2.2.2.1
          (levRun R s n D O U k L c0).2.2.2.2 (s - 1) fl ⟨[], List.replicate D []⟩ ⟨[] :: done, lev⟩)
      (levelCost N R D) := by
  set σ := bank R lm1 c0 n O U k L m s fl ⟨[], List.replicate D []⟩ ⟨done, [] :: lev⟩ with hσ
  have s1 : Runs loadM σ
      (· = bank R lm1 c0 n O U k L c0 s fl ⟨[], List.replicate D []⟩ ⟨done, [] :: lev⟩) (2 * m + 2 * c0 + 30) := by
    apply Runs.of_wp
    simp only [loadM, cpy, WP, wp_op0, wp_rewind, wp_clear]
    tsimp [hσ, bank, endv, emp, reg, Rules.output_copy]
    refine ⟨?_, ?_⟩
    · funext i; fin_cases i <;> first | rfl | tsimp [bank, endv, emp, reg]
    · simp [time_copy, clen, WTape.words]; omega
  have s2 := runs_levelLoop (R := R) (lm1 := lm1) (c0 := c0) (n := n) (s := s) (N := N) (fl := fl)
    (lev := ⟨done, [] :: lev⟩) hR0 hnN D [] O U k L c0 hk hL hc
  set r := levRun R s n D O U k L c0 with hr
  set σ₂ := bank R lm1 c0 n r.1 r.2.1 r.2.2.1 r.2.2.2.1 r.2.2.2.2 s fl ⟨List.replicate D [] ++ [], []⟩
    ⟨done, [] :: lev⟩ with hσ₂
  have s3 := runs_rewind (a := 0) gAx σ₂
  set σ₃ := Function.update σ₂ gAx ⟨[], (σ₂ gAx).left.reverse ++ (σ₂ gAx).right⟩ with hσ₃
  have s4 := runs_decStep (s := s) σ₃ (by tsimp [hσ₃, hσ₂, bank]) (by tsimp [hσ₃, hσ₂, bank])
    (by tsimp [hσ₃, hσ₂, bank])
  set σ₄ := Function.update σ₃ gSt (reg (ones (s - 1))) with hσ₄
  have s5 := runs_skp (a := 0) (show gLev ≠ gJ by decide) σ₄ (by tsimp [hσ₄, hσ₃, hσ₂, bank])
    (by tsimp [hσ₄, hσ₃, hσ₂, bank, emp])
  refine (Runs.then s1 (Runs.then s2 (Runs.then s3 (Runs.then s4 s5)))).mono (fun τ he => ?_) ?_
  · rw [he]; funext i; fin_cases i <;> first | rfl | tsimp [hσ₄, hσ₃, hσ₂, bank, WTape.next]
  · have hc1 : (σ₄ gLev).cur.length + 5 = 5 := by tsimp [hσ₄, hσ₃, hσ₂, bank, WTape.cur]
    have hc2 : clen (σ₂ gAx).left + 2 = D + 2 := by
      simp [hσ₂, bank, clen]
    rw [hc1, hc2]
    simp only [levelCost]
    omega

theorem levRun_m (R s n : ℕ) : ∀ (e : ℕ) (O U : List (List Bool)) (k L m : ℕ),
    (levRun R s n e O U k L m).2.2.2.2 = m + e * s
  | 0, _, _, _, _, _ => by simp [levRun]
  | e + 1, _, _, _, _, _ => by rw [levRun, levRun_m]; ring

set_option maxHeartbeats 8000000 in
theorem runs_botLoop {R lm1 c0 n N D : ℕ} (hR0 : 0 < R) (hnN : n ≤ N) {fl : WTape} (hDN : D ≤ N) :
    ∀ (c : ℕ) (done O U : List (List Bool)) (k L m s : ℕ), k + c * D ≤ N → L ≤ N → c0 + D * s ≤ N → m ≤ N →
      s ≤ N →
      Runs (.loop gLev levelStep) (bank R lm1 c0 n O U k L m s fl ⟨[], List.replicate D []⟩ ⟨done, List.replicate c []⟩)
        (· = bank R lm1 c0 n (botRun R c0 D n c O U k L m s).1 (botRun R c0 D n c O U k L m s).2.1
          (botRun R c0 D n c O U k L m s).2.2.1 (botRun R c0 D n c O U k L m s).2.2.2.1
          (botRun R c0 D n c O U k L m s).2.2.2.2.1 (botRun R c0 D n c O U k L m s).2.2.2.2.2 fl
          ⟨[], List.replicate D []⟩ ⟨List.replicate c [] ++ done, []⟩)
        (c * (levelCost N R D + 2))
  | 0, done, O, U, k, L, m, s, _, _, _, _, _ => by
    refine (Runs.loop_done (by simp [bank]) rfl).mono (fun τ he => ?_) (by simp)
    rw [← he]; rfl
  | c + 1, done, O, U, k, L, m, s, hk, hL, hc, hm, hs => by
    have s1 := runs_levelStep (R := R) (lm1 := lm1) (c0 := c0) (n := n) (N := N) (D := D) (fl := fl) (done := done)
      (lev := List.replicate c []) (O := O) (U := U) (k := k) (L := L) (m := m) (s := s) hR0
      (by rw [Nat.add_mul, one_mul] at hk; omega) hL hc hm hDN hs hnN
    rw [show (List.replicate c ([] : List Bool) : List (List Bool)) = List.replicate c [] from rfl] at s1
    have ih := runs_botLoop (R := R) (lm1 := lm1) (c0 := c0) (n := n) (N := N) (D := D) (fl := fl) hR0 hnN hDN c ([] :: done)
      (levRun R s n D O U k L c0).1 (levRun R s n D O U k L c0).2.1 (levRun R s n D O U k L c0).2.2.1
      (levRun R s n D O U k L c0).2.2.2.1 (levRun R s n D O U k L c0).2.2.2.2 (s - 1)
      (by rw [levRun_k]; rw [Nat.add_mul, one_mul] at hk; omega) (by rw [levRun_L]; omega)
      (by have : D * (s - 1) ≤ D * s := Nat.mul_le_mul_left _ (by omega); omega)
      (by rw [levRun_m]; exact hc) (by omega)
    refine (Runs.loop_step (by simp [bank]) (s1.mono (fun τ he => by rw [he]; exact ih) le_rfl)).mono
      (fun τ he => ?_) ?_
    · rw [he]; simp only [botRun]
      rw [show List.replicate (c + 1) ([] : List Bool) ++ done = List.replicate c [] ++ [] :: done by
        rw [List.replicate_succ', List.append_assoc, List.singleton_append]]
    · rw [Nat.add_mul, one_mul]; omega

/-! ### The moves' words -/

open LayoutMachines LayoutScript in
/-- The script words of a list of field swaps. -/
def wordsOf (n R : ℕ) (ops : List LayoutMachines.Op) : List (List Bool) :=
  (ops.map (LayoutMachines.opRec n R)).flatMap AxisDriver.Rec.words

theorem words_move (n R m ρ : ℕ) :
    AxisDriver.Rec.words (LayoutMachines.opRec n R (0, m, 1, ρ)) = swapWords R (n - m - 1 - ρ) m ρ 0 1 := by
  simp [LayoutMachines.opRec, LayoutMachines.opHdrs, LayoutMachines.opP, swapHdrsG, AxisDriver.Rec.words,
    swapWords]

theorem words_back (n R m ρ : ℕ) :
    AxisDriver.Rec.words (LayoutMachines.opRec n R (1, m, 0, ρ)) = swapWords R (n - m - 1 - ρ) m ρ 1 0 := by
  simp only [LayoutMachines.opRec, LayoutMachines.opHdrs, LayoutMachines.opP, swapHdrsG, AxisDriver.Rec.words,
    swapWords, Nat.sub_zero, add_zero]
  rw [show n - 1 - m = n - m - 1 by omega]

/-- The move tuples of the top loop. -/
def topTup (lm1 : ℕ) : ℕ → ℕ → List Bool → List (ℕ × ℕ)
  | _, _, [] => []
  | L, m, true :: f => (m, L - m - 1) :: topTup lm1 (L - 1) (m + lm1) f
  | L, m, false :: f => topTup lm1 L (m + lm1) f

theorem wordsOf_moveOps_cons (n R : ℕ) (q : ℕ × ℕ) (qs : List (ℕ × ℕ)) :
    wordsOf n R (LayoutMachines.moveOps (q :: qs)) =
      swapWords R (n - q.1 - 1 - q.2) q.1 q.2 0 1 ++ wordsOf n R (LayoutMachines.moveOps qs) := by
  simp [wordsOf, LayoutMachines.moveOps, words_move]

theorem wordsOf_backOps_append (n R : ℕ) (qs : List (ℕ × ℕ)) (q : ℕ × ℕ) :
    wordsOf n R (LayoutMachines.backOps (qs ++ [q])) =
      wordsOf n R (LayoutMachines.backOps qs) ++ swapWords R (n - q.1 - 1 - q.2) q.1 q.2 1 0 := by
  simp [wordsOf, LayoutMachines.backOps, words_back]

/-- `topRun_words`: the top loop writes the forward words of its moves, reversed, and the undo words of
its moves in reverse order. -/
theorem topRun_words (R lm1 n : ℕ) : ∀ (f : List Bool) (O U : List (List Bool)) (k L m : ℕ),
    (topRun R lm1 n f O U k L m).1 = (wordsOf n R (LayoutMachines.moveOps (topTup lm1 L m f))).reverse ++ O ∧
    (topRun R lm1 n f O U k L m).2.1 = wordsOf n R (LayoutMachines.backOps (topTup lm1 L m f).reverse) ++ U
  | [], O, U, k, L, m => by simp [topRun, topTup, wordsOf, LayoutMachines.moveOps, LayoutMachines.backOps]
  | true :: f, O, U, k, L, m => by
    obtain ⟨h1, h2⟩ := topRun_words R lm1 n f ((swapWords R (n - m - 1 - (L - m - 1)) m (L - m - 1) 0 1).reverse ++ O)
      (swapWords R (n - m - 1 - (L - m - 1)) m (L - m - 1) 1 0 ++ U) (k + 1) (L - 1) (m + lm1)
    refine ⟨?_, ?_⟩
    · simp only [topRun, topTup]; rw [h1, wordsOf_moveOps_cons]; simp
    · simp only [topRun, topTup, List.reverse_cons]; rw [h2, wordsOf_backOps_append]; simp

  | false :: f, O, U, k, L, m => by
    simp only [topRun, topTup]; exact topRun_words R lm1 n f O U k L (m + lm1)

end LayoutScriptTape

end IntegerMultBounds.Schoenhage
