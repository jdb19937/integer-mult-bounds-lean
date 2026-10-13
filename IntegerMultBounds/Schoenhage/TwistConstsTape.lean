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
  simp only [addFlag, cpy, skp, WP, wp_op0, wp_rewind]
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

end TwistConsts

end IntegerMultBounds.Schoenhage
