module

public import IntegerMultBounds.Schoenhage.Layers

/-! The constants of the twist block at rest, written on tapes (§6). From `ℓ` and `w` in unary and the
long-axis flags, one word program writes `ones w`, the ring constants `ones (2r)`, `ones (4r - 1)`,
`ones (4r)`, `ones (2r - 1)` for `r = 2^ℓ`, the zero counter `bits n 0` and `2^n` ticks for
`n = Σ (ℓ - 1 + [long])` (`runs_constGen`). Powers of two are built by doubling once per tick
(`runs_powLoop`). -/

@[expose] public section

namespace IntegerMultBounds.Schoenhage

open Machine Strm

namespace TwistConsts

/-! ### The bank -/

/-- `ℓ` in unary (input, kept). -/
abbrev cL : Fin 16 := 0
/-- `w` in unary (input, kept). -/
abbrev cW : Fin 16 := 1
/-- The long-axis flags (input, kept). -/
abbrev cF : Fin 16 := 2
/-- Output: `ones w`. -/
abbrev oW : Fin 16 := 3
/-- Output: `ones (2r)`. -/
abbrev o3 : Fin 16 := 4
/-- Output: `bits n 0`. -/
abbrev o15 : Fin 16 := 5
/-- Output: `2^n` ticks. -/
abbrev o17 : Fin 16 := 6
/-- Output: `ones (4r - 1)`. -/
abbrev o22 : Fin 16 := 7
/-- Output: `ones (4r)`. -/
abbrev o23 : Fin 16 := 8
/-- Output: `ones (2r - 1)`. -/
abbrev o24 : Fin 16 := 9
/-- Output: `ones (2r)`. -/
abbrev o25 : Fin 16 := 10
/-- Scratch: the value being doubled. -/
abbrev sR : Fin 16 := 11
/-- Scratch: doubling buffer. -/
abbrev sT : Fin 16 := 12
/-- Scratch: the sum `n`. -/
abbrev sN : Fin 16 := 13
/-- Scratch: ticks. -/
abbrev sK : Fin 16 := 14
/-- Scratch: the one-bit word and junk. -/
abbrev sJ : Fin 16 := 15

/-! ### Doubling -/

/-- Double the unary word on `sR`. -/
noncomputable def dbl : Cmd 0 16 :=
  .seq (op0 Rules.copy false sR sT (by decide)) <| .seq (rewind sR) <|
  .seq (op0 Rules.copy true sR sT (by decide)) <| .seq (clear sR) <| .seq (rewind sT) (regMove sT sR (by decide))

theorem runs_dbl (σ : Fin 16 → WTape) (x : ℕ) (hR : σ sR = reg (ones x)) (hT : σ sT = emp) :
    Runs dbl σ (· = Function.update σ sR (reg (ones (2 * x)))) (20 * x + 60) := by
  apply Runs.of_wp
  simp only [dbl, regMove, regIn, cpy, WP, wp_op0, wp_rewind, wp_clear]
  tsimp [hR, hT, emp, reg, Rules.output_copy, ones_append]
  have t1 := time_le Rules.copy (ones x) (fun j => j.elim0) 0 (fun j => j.elim0)
  have t2 := time_le Rules.copy (ones (x + x)) (fun j => j.elim0) 0 (fun j => j.elim0)
  refine ⟨?_, ?_⟩
  · funext i; fin_cases i <;> tsimp [hR, hT, emp, reg, two_mul]
  · simp [clen, WTape.words] at t1 t2 ⊢; omega

/-- Double `sR` once per tick on `sK`. -/
noncomputable def powLoop : Cmd 0 16 := .loop sK (.seq dbl (skp sK sJ (by decide)))

theorem runs_powLoop : ∀ (k x : ℕ) (L : List (List Bool)) (σ : Fin 16 → WTape),
    σ sK = ⟨L, List.replicate k []⟩ → σ sR = reg (ones x) → σ sT = emp → (σ sJ).right = [] →
    Runs powLoop σ (· = Function.update (Function.update σ sR (reg (ones (2 ^ k * x))))
      sK ⟨List.replicate k [] ++ L, []⟩) (k * (20 * 2 ^ k * x + 70))
  | 0, x, L, σ, hK, hR, hT, hJ => by
    refine (Runs.loop_done (Q := (· = σ)) (by rw [hK]; rfl) rfl).mono (fun τ e => ?_) (by simp)
    rw [e]; funext i; fin_cases i <;> tsimp [hK, hR]
  | k + 1, x, L, σ, hK, hR, hT, hJ => by
    have s1 := runs_dbl σ x hR hT
    have s2 := runs_skp (a := 0) (show sK ≠ sJ by decide) (Function.update σ sR (reg (ones (2 * x))))
      (by tsimp [hK, List.replicate_succ]) (by tsimp [hJ])
    have ih := runs_powLoop k (2 * x) ([] :: L)
      (Function.update (Function.update σ sR (reg (ones (2 * x)))) sK
        (Function.update σ sR (reg (ones (2 * x))) sK).next)
      (by tsimp [hK, List.replicate_succ, WTape.next]) (by tsimp) (by tsimp [hT]) (by tsimp [hJ])
    unfold powLoop at ih ⊢
    refine (Runs.loop_step (by rw [hK]; simp [List.replicate_succ]) (Runs.then s1 (s2.mono
      (fun τ e => by rw [e]; exact ih) le_rfl))).mono (fun τ e => ?_) ?_
    · rw [e]
      have hl : List.replicate k [] ++ [] :: L = List.replicate (k + 1) ([] : List Bool) ++ L := by
        simp [List.replicate_succ']
      have hp : 2 ^ k * (2 * x) = 2 ^ (k + 1) * x := by ring
      funext i
      fin_cases i <;> tsimp [hK, WTape.next, hl, hp]
    · have h1 : (Function.update σ sR (reg (ones (2 * x))) sK).cur.length = 0 := by
        tsimp [hK, WTape.cur, List.replicate_succ]
      rw [h1]
      have hp : 20 * 2 ^ k * (2 * x) = 20 * 2 ^ (k + 1) * x := by ring
      rw [hp]
      have : x ≤ 2 ^ (k + 1) * x := Nat.le_mul_of_pos_left _ (by positivity)
      nlinarith

/-! ### The sum `n` over the axes -/

/-- One axis: add `ℓ - 1` (on `sR`) and the axis's flag (one bit on `sJ`) to the sum on `sN`. -/
noncomputable def addFlag : Cmd 0 16 :=
  .seq (op0 Rules.copy true sR sN (by decide)) <| .seq (rewind sR) <|
  .seq (.cond cF (.seq (op0 Rules.copy true sJ sN (by decide)) (rewind sJ)) (rewind sT)) (skp cF sT (by decide))

/-- The flag sum: `a` plus one for a long axis, over the axes. -/
def flagSum (a : ℕ) (fl : List Bool) : ℕ := (fl.map fun b => a + if b then 1 else 0).sum

theorem runs_addFlag (σ : Fin 16 → WTape) (a m : ℕ) (b : Bool) (Lf R : List (List Bool))
    (hR : σ sR = reg (ones a)) (hJ : σ sJ = reg [true]) (hT : σ sT = emp) (hN : σ sN = ⟨[ones m], []⟩)
    (hF : σ cF = ⟨Lf, [b] :: R⟩) :
    Runs addFlag σ (· = Function.update (Function.update σ sN ⟨[ones (m + (a + if b then 1 else 0))], []⟩)
      cF ⟨[b] :: Lf, R⟩) (3 * a + 40) := by
  have t1 := time_le Rules.copy (ones a) (fun j => j.elim0) 0 (fun j => j.elim0)
  have t2 := time_le Rules.copy [true] (fun j => j.elim0) 0 (fun j => j.elim0)
  have t3 := time_le Rules.skip [b] (fun j => j.elim0) 0 (fun j => j.elim0)
  apply Runs.of_wp
  simp only [addFlag, skp, WP, wp_op0, wp_rewind]
  cases b <;> tsimp [hR, hJ, hT, hN, hF, emp, reg, Rules.output_copy, Rules.output_skip, StartsOne, WTape.put,
    WTape.next, WTape.cur, ones_append]
  all_goals
    have h1 : ones (m + a) ++ [true] = ones (m + (a + 1)) := by
      rw [show [true] = ones 1 from rfl, ones_append, Nat.add_assoc]
    refine ⟨?_, by simp at t1 t2 t3; omega⟩
    funext i
    fin_cases i <;> tsimp [hR, hJ, hT, hN, emp, reg, h1]

/-- Add every axis. -/
noncomputable def flagLoop : Cmd 0 16 := .loop cF addFlag

theorem runs_flagLoop (a : ℕ) : ∀ (fl : List Bool) (m : ℕ) (Lf : List (List Bool)) (σ : Fin 16 → WTape),
    σ sR = reg (ones a) → σ sJ = reg [true] → σ sT = emp → σ sN = ⟨[ones m], []⟩ →
    σ cF = ⟨Lf, fl.map fun b => [b]⟩ →
    Runs flagLoop σ (· = Function.update (Function.update σ sN ⟨[ones (m + flagSum a fl)], []⟩)
      cF ⟨(fl.map fun b => [b]).reverse ++ Lf, []⟩) (fl.length * (3 * a + 42))
  | [], m, Lf, σ, hR, hJ, hT, hN, hF => by
    refine (Runs.loop_done (Q := (· = σ)) (by rw [hF]; rfl) rfl).mono (fun τ e => ?_) (by simp)
    rw [e]; funext i; fin_cases i <;> tsimp [hF, hN, flagSum]
  | b :: fl, m, Lf, σ, hR, hJ, hT, hN, hF => by
    have s1 := runs_addFlag σ a m b Lf (fl.map fun b => [b]) hR hJ hT hN (by rw [hF]; rfl)
    have ih := runs_flagLoop a fl (m + (a + if b then 1 else 0)) ([b] :: Lf)
      (Function.update (Function.update σ sN ⟨[ones (m + (a + if b then 1 else 0))], []⟩) cF
        ⟨[b] :: Lf, fl.map fun b => [b]⟩) (by tsimp [hR]) (by tsimp [hJ]) (by tsimp [hT]) (by tsimp) (by tsimp)
    unfold flagLoop at ih ⊢
    refine (Runs.loop_step (by rw [hF]; simp) (s1.mono (fun τ e => by rw [e]; exact ih) le_rfl)).mono
      (fun τ e => ?_) ?_
    · rw [e]
      have hs : m + (a + if b then 1 else 0) + flagSum a fl = m + flagSum a (b :: fl) := by
        simp [flagSum]; ring
      funext i
      fin_cases i <;> tsimp [hs]
    · simp only [List.length_cons]
      nlinarith

/-! ### The straight-line blocks -/

theorem ones_tail (k : ℕ) : (ones k).tail = ones (k - 1) := by simp [ones, List.tail_replicate]

theorem clen_ticks (n : ℕ) : clen (List.replicate n ([] : List Bool)) = n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [List.replicate_succ, clen_cons, ih]; simp; omega

/-- Copy `w`, start `sR` at one, and ticks for `ℓ`. -/
noncomputable def blockA : Cmd 0 16 :=
  .seq (regDup cW oW (by decide)) <| .seq (emit [[true]] sR) <| .seq (rewind sR) <|
  .seq (op0 Rules.ticks false cL sK (by decide)) <| .seq (rewind cL) (rewind sK)

theorem runs_blockA (σ : Fin 16 → WTape) (l w : ℕ) (hL : σ cL = reg (ones l)) (hW : σ cW = reg (ones w))
    (hO : σ oW = emp) (hR : σ sR = emp) (hK : σ sK = emp) :
    Runs blockA σ (· = Function.update (Function.update (Function.update σ oW (reg (ones w))) sR (reg [true]))
      sK ⟨[], List.replicate l []⟩) (6 * w + 4 * l + 60) := by
  apply Runs.of_wp
  simp only [blockA, regDup, regIn, cpy, WP, wp_op0, wp_rewind, wp_emit]
  tsimp [hL, hW, hO, hR, hK, emp, reg, Rules.output_copy, Rules.output_ticks, WTape.put, WTape.next,
    WTape.cur]
  have t1 := time_le Rules.copy (ones w) (fun j => j.elim0) 0 (fun j => j.elim0)
  have t2 := time_le Rules.ticks (ones l) (fun j => j.elim0) 0 (fun j => j.elim0)
  refine ⟨?_, by simp [clen_ticks] at t1 t2 ⊢; omega⟩
  funext i; fin_cases i <;> tsimp [hL, hW, reg]

/-- Write `ones (k - 1)` on `o` from `ones k` on `s`, with `[true]` on `j`. -/
noncomputable def dropOne {t : ℕ} (s j o : Fin t) (h1 : s ≠ j) (h2 : s ≠ o) (h3 : j ≠ o) : Cmd 0 t :=
  .seq (op1 Rules.drop false s j o h1 h2 h3) <| .seq (rewind o) <| .seq (rewind s) (rewind j)

theorem runs_dropOne {t : ℕ} {s j o : Fin t} (h1 : s ≠ j) (h2 : s ≠ o) (h3 : j ≠ o) (σ : Fin t → WTape) (k : ℕ)
    (hs : σ s = reg (ones k)) (hj : σ j = reg [true]) (ho : σ o = emp) :
    Runs (dropOne s j o h1 h2 h3) σ (· = Function.update σ o (reg (ones (k - 1)))) (3 * k + 30) := by
  have d1 := time_le Rules.drop (ones k) (fun _ => [true]) 1 (fun _ => le_rfl)
  apply Runs.of_wp
  simp only [dropOne, WP, wp_op1, wp_rewind]
  simp [h1, h2, h3, h1.symm, hs, hj, ho, reg, emp, Rules.output_drop,
    WTape.put, WTape.next, WTape.cur, ↓parse_syms]
  refine ⟨?_, ?_⟩
  · funext x
    by_cases hxo : x = o
    · subst hxo
      rw [Function.update_of_ne (Ne.symm h3), Function.update_of_ne (Ne.symm h2), Function.update_self, ones_tail, Function.update_self]
    · by_cases hxs : x = s
      · subst hxs; simp [hxo, h1, hs, reg]
      · by_cases hxj : x = j
        · subst hxj; simp [hxo, hj, reg]
        · simp [hxo, hxs, hxj]
  · simp at d1; omega


/-- From the sum `n` on `sN`: the zero counter, then `sR` at one and ticks for `n`. -/
noncomputable def blockC : Cmd 0 16 :=
  .seq (clear sR) <| .seq (rewind sN) <| .seq (op0 (Rules.fill false) false sN o15 (by decide)) <|
  .seq (rewind o15) <| .seq (rewind sN) <| .seq (emit [[true]] sR) <| .seq (rewind sR) <|
  .seq (op0 Rules.ticks false sN sK (by decide)) <| .seq (rewind sN) <| .seq (rewind sK) (clear sJ)

theorem runs_blockC (σ : Fin 16 → WTape) (a n : ℕ) (hR : σ sR = reg (ones a)) (hN : σ sN = ⟨[ones n], []⟩)
    (h15 : σ o15 = emp) (hK : σ sK = emp) (hJ : σ sJ = reg [true]) :
    Runs blockC σ (· = Function.update (Function.update (Function.update (Function.update
      (Function.update σ o15 (reg (List.replicate n false))) sN (reg (ones n))) sR (reg [true]))
      sK ⟨[], List.replicate n []⟩) sJ emp) (2 * a + 12 * n + 80) := by
  have t1 := time_le (Rules.fill false) (ones n) (fun j => j.elim0) 0 (fun j => j.elim0)
  have t2 := time_le Rules.ticks (ones n) (fun j => j.elim0) 0 (fun j => j.elim0)
  apply Runs.of_wp
  simp only [blockC, WP, wp_op0, wp_rewind, wp_emit, wp_clear]
  tsimp [hR, hN, h15, hK, hJ, emp, reg, Rules.output_fill, Rules.output_ticks, WTape.put, WTape.next, WTape.cur]
  refine ⟨?_, ?_⟩
  · funext i; fin_cases i <;> tsimp [hR, hN, h15, hK, hJ, emp, reg]
  · simp only [WTape.words, List.reverse_nil, List.nil_append, clen_cons, clen_nil,
      length_ones, clen_ticks, List.length_singleton] at t1 t2 ⊢
    generalize time (Rules.fill false) (ones n) (fun j => j.elim0) = a1 at t1 ⊢
    generalize time Rules.ticks (ones n) (fun j => j.elim0) = a2 at t2 ⊢
    omega

/-- The ticks of `2^n` on `o17`, scratch cleared. -/
noncomputable def blockD : Cmd 0 16 :=
  .seq (clear sK) <| .seq (op0 Rules.ticks false sR o17 (by decide)) <| .seq (rewind o17) <|
  .seq (clear sR) (clear sN)

theorem runs_blockD (σ : Fin 16 → WTape) (n M : ℕ) (hR : σ sR = reg (ones M)) (hN : σ sN = reg (ones n))
    (hK : σ sK = ⟨List.replicate n [], []⟩) (h17 : σ o17 = emp) :
    Runs blockD σ (· = Function.update (Function.update (Function.update (Function.update σ sK emp)
      o17 ⟨[], List.replicate M []⟩) sR emp) sN emp) (6 * M + 4 * n + 40) := by
  have t2 := time_le Rules.ticks (ones M) (fun j => j.elim0) 0 (fun j => j.elim0)
  apply Runs.of_wp
  simp only [blockD, WP, wp_op0, wp_rewind, wp_clear]
  tsimp [hR, hN, hK, h17, emp, reg, Rules.output_ticks, WTape.put, WTape.next, WTape.cur]
  refine ⟨?_, ?_⟩
  · funext i; fin_cases i <;> tsimp [hR, hN, hK, h17, emp, reg]
  · simp only [WTape.words, List.reverse_nil, List.nil_append, List.append_nil, clen_cons, clen_nil,
      length_ones, List.reverse_replicate, clen_ticks, List.reverse_singleton] at t2 ⊢
    generalize time Rules.ticks (ones M) (fun j => j.elim0) = a2 at t2 ⊢
    omega

/-! ### The whole program -/

theorem clen_flags (fl : List Bool) : clen ((fl.map fun b => [b]).reverse) = 2 * fl.length := by
  rw [clen_reverse]
  induction fl with
  | nil => rfl
  | cons b fl ih => simp only [List.map_cons, clen_cons, List.length_cons, ih]; simp; ring

/-- Write the twist block's constants and `ones w`. -/
noncomputable def constGen : Cmd 0 16 :=
  .seq blockA <| .seq powLoop <| .seq (clear sK) <| .seq dbl <| .seq (regDup sR o25 (by decide)) <|
  .seq (regDup sR o3 (by decide)) <| .seq (emit [[true]] sJ) <| .seq (rewind sJ) <|
  .seq (dropOne sR sJ o24 (by decide) (by decide) (by decide)) <| .seq dbl <|
  .seq (regDup sR o23 (by decide)) <| .seq (dropOne sR sJ o22 (by decide) (by decide) (by decide)) <|
  .seq (clear sR) <| .seq (dropOne cL sJ sR (by decide) (by decide) (by decide)) <|
  .seq (emit [[]] sN) <| .seq (rewind cF) <| .seq flagLoop <| .seq blockC <| .seq powLoop blockD

/-- The inputs: `ℓ` and `w` in unary and the flags `fl` as one-bit words, reversed on the left. -/
def cIn (l w : ℕ) (fl : List Bool) : Fin 16 → WTape := fun i =>
  if i = cL then reg (ones l) else if i = cW then reg (ones w)
  else if i = cF then ⟨(fl.map fun b => [b]).reverse, []⟩ else emp

/-- The inputs and the constants, for `r = 2^ℓ` and `n = Σ (ℓ - 1 + [long])`. -/
def cOut (l w : ℕ) (fl : List Bool) : Fin 16 → WTape := fun i =>
  if i = oW then reg (ones w) else if i = o3 then reg (ones (2 * 2 ^ l))
  else if i = o15 then reg (List.replicate (flagSum (l - 1) fl) false)
  else if i = o17 then ⟨[], List.replicate (2 ^ flagSum (l - 1) fl) []⟩
  else if i = o22 then reg (ones (4 * 2 ^ l - 1)) else if i = o23 then reg (ones (4 * 2 ^ l))
  else if i = o24 then reg (ones (2 * 2 ^ l - 1)) else if i = o25 then reg (ones (2 * 2 ^ l)) else cIn l w fl i

/-- The constants program's step bound. -/
def constCost (l w : ℕ) (fl : List Bool) : ℕ :=
  6 * w + l * (20 * 2 ^ l * 1 + 70) + 200 * 2 ^ l + 40 * l + fl.length * (3 * (l - 1) + 50) +
    flagSum (l - 1) fl * (20 * 2 ^ flagSum (l - 1) fl * 1 + 70) + 10 * 2 ^ flagSum (l - 1) fl +
    20 * flagSum (l - 1) fl + 800

set_option maxHeartbeats 8000000 in
theorem runs_constGen (l w : ℕ) (fl : List Bool) :
    Runs constGen (cIn l w fl) (· = cOut l w fl) (constCost l w fl) := by
  set X := 2 ^ l
  set n := flagSum (l - 1) fl
  set σ0 := cIn l w fl
  have s1 := runs_blockA σ0 l w (by tsimp [σ0, cIn]) (by tsimp [σ0, cIn]) (by tsimp [σ0, cIn])
    (by tsimp [σ0, cIn]) (by tsimp [σ0, cIn])
  set σ1 := Function.update (Function.update (Function.update σ0 oW (reg (ones w))) sR (reg [true]))
    sK ⟨[], List.replicate l []⟩
  have s2 := runs_powLoop l 1 [] σ1 (by tsimp [σ1]) (by tsimp [σ1]; rfl) (by tsimp [σ1, σ0, cIn])
    (by tsimp [σ1, σ0, cIn, emp])
  set σ2 := Function.update (Function.update σ1 sR (reg (ones (2 ^ l * 1)))) sK ⟨List.replicate l [] ++ [], []⟩
  have s3 := runs_clear (a := 0) sK σ2
  set σ3 := Function.update σ2 sK ⟨[], []⟩
  have s4 := runs_dbl σ3 X (by tsimp [σ3, σ2, X]) (by tsimp [σ3, σ2, σ1, σ0, cIn])
  set σ4 := Function.update σ3 sR (reg (ones (2 * X)))
  have s5 := runs_regDup (a := 0) (show sR ≠ o25 by decide) σ4 (w := ones (2 * X)) (by tsimp [σ4])
    (by tsimp [σ4, σ3, σ2, σ1, σ0, cIn])
  set σ5 := Function.update σ4 o25 (reg (ones (2 * X)))
  have s6 := runs_regDup (a := 0) (show sR ≠ o3 by decide) σ5 (w := ones (2 * X)) (by tsimp [σ5, σ4])
    (by tsimp [σ5, σ4, σ3, σ2, σ1, σ0, cIn])
  set σ6 := Function.update σ5 o3 (reg (ones (2 * X)))
  have s7 := runs_emit (a := 0) [[true]] sJ σ6 (by tsimp [σ6, σ5, σ4, σ3, σ2, σ1, σ0, cIn, emp])
  set σ7 := Function.update σ6 sJ ⟨[[true]].reverse ++ (σ6 sJ).left, []⟩
  have s8 := runs_rewind (a := 0) sJ σ7
  set σ8 := Function.update σ7 sJ ⟨[], (σ7 sJ).left.reverse ++ (σ7 sJ).right⟩
  have hJ8 : σ8 sJ = reg [true] := by tsimp [σ8, σ7, σ6, σ5, σ4, σ3, σ2, σ1, σ0, cIn, emp, reg]
  have s9 := runs_dropOne (show sR ≠ sJ by decide) (show sR ≠ o24 by decide) (show sJ ≠ o24 by decide) σ8 (2 * X)
    (by tsimp [σ8, σ7, σ6, σ5, σ4]) hJ8 (by tsimp [σ8, σ7, σ6, σ5, σ4, σ3, σ2, σ1, σ0, cIn])
  set σ9 := Function.update σ8 o24 (reg (ones (2 * X - 1)))
  have s10 := runs_dbl σ9 (2 * X) (by tsimp [σ9, σ8, σ7, σ6, σ5, σ4])
    (by tsimp [σ9, σ8, σ7, σ6, σ5, σ4, σ3, σ2, σ1, σ0, cIn])
  set σ10 := Function.update σ9 sR (reg (ones (2 * (2 * X))))
  have s11 := runs_regDup (a := 0) (show sR ≠ o23 by decide) σ10 (w := ones (2 * (2 * X))) (by tsimp [σ10])
    (by tsimp [σ10, σ9, σ8, σ7, σ6, σ5, σ4, σ3, σ2, σ1, σ0, cIn])
  set σ11 := Function.update σ10 o23 (reg (ones (2 * (2 * X))))
  have s12 := runs_dropOne (show sR ≠ sJ by decide) (show sR ≠ o22 by decide) (show sJ ≠ o22 by decide) σ11
    (2 * (2 * X)) (by tsimp [σ11, σ10]) (by tsimp [σ11, σ10, σ9, hJ8])
    (by tsimp [σ11, σ10, σ9, σ8, σ7, σ6, σ5, σ4, σ3, σ2, σ1, σ0, cIn])
  set σ12 := Function.update σ11 o22 (reg (ones (2 * (2 * X) - 1)))
  have s13 := runs_clear (a := 0) sR σ12
  set σ13 := Function.update σ12 sR ⟨[], []⟩
  have s14 := runs_dropOne (show cL ≠ sJ by decide) (show cL ≠ sR by decide) (show sJ ≠ sR by decide) σ13 l
    (by tsimp [σ13, σ12, σ11, σ10, σ9, σ8, σ7, σ6, σ5, σ4, σ3, σ2, σ1, σ0, cIn])
    (by tsimp [σ13, σ12, σ11, σ10, σ9, hJ8]) (by tsimp [σ13, emp])
  set σ14 := Function.update σ13 sR (reg (ones (l - 1)))
  have s15 := runs_emit (a := 0) [[]] sN σ14 (by tsimp [σ14, σ13, σ12, σ11, σ10, σ9, σ8, σ7, σ6, σ5, σ4, σ3, σ2,
    σ1, σ0, cIn, emp])
  set σ15 := Function.update σ14 sN ⟨[[]].reverse ++ (σ14 sN).left, []⟩
  have s16 := runs_rewind (a := 0) cF σ15
  set σ16 := Function.update σ15 cF ⟨[], (σ15 cF).left.reverse ++ (σ15 cF).right⟩
  have s17 := runs_flagLoop (l - 1) fl 0 [] σ16 (by tsimp [σ16, σ15, σ14])
    (by tsimp [σ16, σ15, σ14, σ13, σ12, σ11, σ10, σ9, hJ8])
    (by tsimp [σ16, σ15, σ14, σ13, σ12, σ11, σ10, σ9, σ8, σ7, σ6, σ5, σ4, σ3, σ2, σ1, σ0, cIn])
    (by tsimp [σ16, σ15, σ14, σ13, σ12, σ11, σ10, σ9, σ8, σ7, σ6, σ5, σ4, σ3, σ2, σ1, σ0, cIn, emp])
    (by tsimp [σ16, σ15, σ14, σ13, σ12, σ11, σ10, σ9, σ8, σ7, σ6, σ5, σ4, σ3, σ2, σ1, σ0, cIn])
  set σ17 := Function.update (Function.update σ16 sN ⟨[ones (0 + n)], []⟩) cF
    ⟨(fl.map fun b => [b]).reverse ++ [], []⟩
  have s18 := runs_blockC σ17 (l - 1) n (by tsimp [σ17, σ16, σ15, σ14]) (by tsimp [σ17])
    (by tsimp [σ17, σ16, σ15, σ14, σ13, σ12, σ11, σ10, σ9, σ8, σ7, σ6, σ5, σ4, σ3, σ2, σ1, σ0, cIn])
    (by tsimp [σ17, σ16, σ15, σ14, σ13, σ12, σ11, σ10, σ9, σ8, σ7, σ6, σ5, σ4, σ3, emp])
    (by tsimp [σ17, σ16, σ15, σ14, σ13, σ12, σ11, σ10, σ9, hJ8])
  set σ18 := Function.update (Function.update (Function.update (Function.update
      (Function.update σ17 o15 (reg (List.replicate n false))) sN (reg (ones n))) sR (reg [true]))
      sK ⟨[], List.replicate n []⟩) sJ emp
  have s19 := runs_powLoop n 1 [] σ18 (by tsimp [σ18]) (by tsimp [σ18]; rfl)
    (by tsimp [σ18, σ17, σ16, σ15, σ14, σ13, σ12, σ11, σ10, σ9, σ8, σ7, σ6, σ5, σ4, σ3, σ2, σ1, σ0, cIn])
    (by tsimp [σ18, emp])
  set σ19 := Function.update (Function.update σ18 sR (reg (ones (2 ^ n * 1)))) sK ⟨List.replicate n [] ++ [], []⟩
  have s20 := runs_blockD σ19 n (2 ^ n * 1) (by tsimp [σ19]) (by tsimp [σ19, σ18]) (by tsimp [σ19])
    (by tsimp [σ19, σ18, σ17, σ16, σ15, σ14, σ13, σ12, σ11, σ10, σ9, σ8, σ7, σ6, σ5, σ4, σ3, σ2, σ1, σ0, cIn])
  have h4 : 2 * (2 * 2 ^ l) = 4 * 2 ^ l := by ring
  refine (Runs.then s1 (Runs.then s2 (Runs.then s3 (Runs.then s4 (Runs.then s5 (Runs.then s6 (Runs.then s7
    (Runs.then s8 (Runs.then s9 (Runs.then s10 (Runs.then s11 (Runs.then s12 (Runs.then s13 (Runs.then s14
    (Runs.then s15 (Runs.then s16 (Runs.then s17 (Runs.then s18 (Runs.then s19 s20))))))))))))))))))).mono
    (fun τ e => ?_) ?_
  · rw [e]
    funext i
    fin_cases i <;> tsimp [σ19, σ18, σ17, σ16, σ15, σ14, σ13, σ12, σ11, σ10, σ9, σ8, σ7, σ6, σ5, σ4, σ3, σ2, σ1, σ0,
      cIn, cOut, emp, reg, X, n, h4]
  · tsimp [σ19, σ18, σ17, σ16, σ15, σ14, σ13, σ12, σ11, σ10, σ9, σ8, σ7, σ6, σ5, σ4, σ3, σ2, σ1, σ0, cIn,
      WTape.words, clen_ticks, length_ones, constCost, emp, reg]
    have hc := clen_flags fl
    have hq : fl.length * (3 * (l - 1) + 50) = fl.length * (3 * (l - 1) + 42) + 8 * fl.length := by ring
    rw [hc, hq]
    generalize l * (20 * 2 ^ l + 70) = P1
    generalize fl.length * (3 * (l - 1) + 42) = P3
    generalize flagSum (l - 1) fl * (20 * 2 ^ flagSum (l - 1) fl + 70) = P2 at *
    simp only [X, n] at *
    omega


end TwistConsts

end IntegerMultBounds.Schoenhage
