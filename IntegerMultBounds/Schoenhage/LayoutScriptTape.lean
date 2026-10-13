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

/-- The move's forward words onto `gO`. -/
noncomputable def emitFwd : Cmd 0 20 :=
  .seq (emit [[false]] gO) <|
  .seq (rewind gK) <| .seq (op0 fillOne false gK gO (by decide)) <|
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
  .seq (rewind gK) <| .seq (op0 fillOne false gK gU (by decide)) (emit [[false]] gU)

/-- Count the move: `k + 1`, `L - 1`, and clear `ρ`. -/
noncomputable def advance : Cmd 0 20 :=
  .seq (clear gR) <| .seq (op0 Rules.copy true gOne gK (by decide)) <|
  .seq (rewind gOne) <| .seq (rewind gL) <| .seq (op1 Rules.drop false gL gOne gS (by decide) (by decide) (by decide)) <|
  .seq (rewind gOne) <| .seq (clear gL) <| .seq (rewind gS) <| .seq (cpy gS gL (by decide)) (clear gS)

/-- One move: compute `ρ`, write the forward and undo words, count it. -/
noncomputable def emitMove : Cmd 0 20 := .seq rhoCalc <| .seq emitFwd <| .seq emitUndo advance

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
theorem runs_emitFwd {R k m ρ : ℕ} (hR0 : 0 < R) (σ : Fin 20 → WTape) {O : List (List Bool)}
    (hO : σ gO = ⟨O, []⟩) (hK : σ gK = endv k) (hM : σ gM = endv m) (hRho : σ gR = endv ρ)
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
  · simp [time_copy, time_fillOne, time_fill, clen, WTape.words, length_ones]; omega

set_option maxHeartbeats 8000000 in
theorem runs_emitUndo {R k m ρ : ℕ} (hR0 : 0 < R) (σ : Fin 20 → WTape) {U : List (List Bool)}
    (hU : σ gU = ⟨U, []⟩) (hK : σ gK = endv k) (hM : σ gM = endv m) (hRho : σ gR = endv ρ)
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
  · simp [time_copy, time_fillOne, time_fill, clen, WTape.words, length_ones]; omega

set_option maxHeartbeats 8000000 in
theorem runs_advance {k L ρ : ℕ} (σ : Fin 20 → WTape) (hK : σ gK = endv k) (hL : σ gL = endv L)
    (hRho : σ gR = endv ρ) (hS : σ gS = emp) (hOne : σ gOne = reg (ones 1)) :
    Runs advance σ (· = Function.update (Function.update (Function.update σ gR emp) gK (endv (k + 1)))
      gL (endv (L - 1))) (2 * ρ + 12 * L + 4 * k + 80) := by
  have t1 : time Rules.drop (List.replicate L true) (fun _ => [true]) ≤ L + 1 + 6 :=
    (time_le Rules.drop (ones L) (fun _ => ones 1) 1 (fun _ => by simp)).trans (by simp)
  apply Runs.of_wp
  simp only [advance, cpy, WP, wp_op0, wp_op1, wp_rewind, wp_clear]
  tsimp [hK, hL, hRho, hS, hOne, endv, emp, reg, Rules.output_copy, Rules.output_drop, ones,
    List.drop_replicate]
  refine ⟨?_, ?_⟩
  · funext i; fin_cases i <;> first | rfl | tsimp [hK, hL, hRho, hS, hOne, endv, emp, reg, ones,
      WTape.put, List.replicate_succ']
  · simp [time_copy, clen, WTape.words]; omega

/-! ### The generator's states -/

/-- The bank: outputs `O`, `U`, counters `k`, `L`, `m`, the level step `s`, loop tapes, constants. -/
def bank (R lm1 c0 : ℕ) (O U : List (List Bool)) (k L m s : ℕ) (fl ax lev : WTape) : Fin 20 → WTape :=
  fun i => match i.val with
  | 0 => ⟨O, []⟩ | 1 => ⟨U, []⟩ | 2 => endv k | 3 => endv L | 4 => endv m
  | 6 => reg (bin R) | 7 => reg [] | 8 => reg [true] | 11 => fl | 12 => reg (ones lm1)
  | 13 => reg (ones 1) | 14 => lev | 15 => ax | 16 => endv s | 17 => reg (ones c0)
  | _ => emp

set_option maxHeartbeats 8000000 in
/-- One move: the forward record onto `gO`, the undo record (reversed) onto `gU`, `k + 1`, `L - 1`. -/
theorem runs_emitMove {R lm1 c0 : ℕ} (hR0 : 0 < R) {O U : List (List Bool)} {k L m s : ℕ}
    {fl ax lev : WTape} :
    Runs emitMove (bank R lm1 c0 O U k L m s fl ax lev)
      (· = bank R lm1 c0 ((swapWords R k m (L - m - 1) 0 1).reverse ++ O)
        (swapWords R k m (L - m - 1) 1 0 ++ U) (k + 1) (L - 1) m s fl ax lev)
      (44 * L + 12 * m + 12 * k + 8 * (bin R).length + 600) := by
  set σ := bank R lm1 c0 O U k L m s fl ax lev with hσ
  have s1 := runs_rhoCalc (L := L) (m := m) σ (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
  set σ₁ := Function.update σ gR (endv (L - m - 1)) with hσ₁
  have s2 := runs_emitFwd (R := R) (k := k) (m := m) (ρ := L - m - 1) hR0 σ₁ (O := O)
    (by tsimp [hσ₁, hσ, bank]) (by tsimp [hσ₁, hσ, bank]) (by tsimp [hσ₁, hσ, bank]) (by tsimp [hσ₁])
    (by tsimp [hσ₁, hσ, bank]) (by tsimp [hσ₁, hσ, bank]) (by tsimp [hσ₁, hσ, bank])
  set σ₂ := Function.update σ₁ gO ⟨(swapWords R k m (L - m - 1) 0 1).reverse ++ O, []⟩ with hσ₂
  have s3 := runs_emitUndo (R := R) (k := k) (m := m) (ρ := L - m - 1) hR0 σ₂ (U := U)
    (by tsimp [hσ₂, hσ₁, hσ, bank]) (by tsimp [hσ₂, hσ₁, hσ, bank]) (by tsimp [hσ₂, hσ₁, hσ, bank])
    (by tsimp [hσ₂, hσ₁]) (by tsimp [hσ₂, hσ₁, hσ, bank]) (by tsimp [hσ₂, hσ₁, hσ, bank])
    (by tsimp [hσ₂, hσ₁, hσ, bank])
  set σ₃ := Function.update σ₂ gU ⟨swapWords R k m (L - m - 1) 1 0 ++ U, []⟩ with hσ₃
  have s4 := runs_advance (k := k) (L := L) (ρ := L - m - 1) σ₃ (by tsimp [hσ₃, hσ₂, hσ₁, hσ, bank])
    (by tsimp [hσ₃, hσ₂, hσ₁, hσ, bank]) (by tsimp [hσ₃, hσ₂, hσ₁]) (by tsimp [hσ₃, hσ₂, hσ₁, hσ, bank])
    (by tsimp [hσ₃, hσ₂, hσ₁, hσ, bank])
  refine (Runs.then s1 (Runs.then s2 (Runs.then s3 s4))).mono (fun τ e => ?_) ?_
  · rw [e]; funext i; fin_cases i <;> rfl
  · have : L - m - 1 ≤ L := by omega
    omega

end LayoutScriptTape

end IntegerMultBounds.Schoenhage
