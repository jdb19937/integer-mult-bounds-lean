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

end TwistConsts

end IntegerMultBounds.Schoenhage
