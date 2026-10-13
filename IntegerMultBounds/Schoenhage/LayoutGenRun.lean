module

public import IntegerMultBounds.Schoenhage.LayoutGenSetup
public import IntegerMultBounds.Schoenhage.TransformGen

/-! The §6 layout-script writer on one bank of 48 tapes. From `ones ℓ`, `ones K`,
`ones w`, one tick per axis, the long-axis flags and `ones D`, it computes the
address length `n`, `b = (ℓ - 1) mod K` and `q = (ℓ - 1) div K`, `bin R` and
`bin K`, and the axis-major arrangement (setup); runs the prefix moves
(`LayoutScriptTape.movesGen`) and the chunk-exchange scan (`LayoutSwapTape.step`);
copies the forward script, or reverses the undo script, onto the output tape; and
empties every other tape it used. -/

@[expose] public section

namespace IntegerMultBounds.Schoenhage

open Machine Strm Resampling Script TwistDescriptors LayoutScriptTape LayoutGenSetup

namespace LayoutGenRun

/-! ### The bank

Tapes `0, …, 19` are the move generator's (`LayoutScriptTape.bank`); `20, …, 31`
the exchange scan's own; `32, …, 37` the inputs; `38` the output; `39, …, 47`
scratch. -/

/-- `ones ℓ`. -/
abbrev tIL : Fin 48 := 32
/-- `ones K`. -/
abbrev tKI : Fin 48 := 33
/-- `ones w`. -/
abbrev tIW : Fin 48 := 34
/-- One tick per axis, on the left. -/
abbrev tXB : Fin 48 := 35
/-- The long-axis flags, on the left. -/
abbrev tXA : Fin 48 := 36
/-- `ones D`. -/
abbrev tKN : Fin 48 := 37
/-- The output. -/
abbrev tOut : Fin 48 := 38

/-- The inputs, everything else empty. -/
def lstart (ℓ K w D : ℕ) (f : List Bool) : Fin 48 → WTape :=
  fun i => match i.val with
  | 32 => reg (ones ℓ) | 33 => reg (ones K) | 34 => reg (ones w)
  | 35 => ⟨List.replicate D [], []⟩ | 36 => ⟨(f.map fun b => [b]).reverse, []⟩ | 37 => reg (ones D)
  | _ => emp

/-! ### Setup, part one: constants and copies -/

/-- The constants of both generators. -/
noncomputable def constsA : Cmd 0 48 :=
  .seq (emit [[true]] 13) <| .seq (rewind 13) <| .seq (emit [[]] 7) <| .seq (rewind 7) <|
  .seq (emit [[true]] 8) <| .seq (rewind 8) <| .seq (emit [[]] 2) <| .seq (emit [[]] 4) <|
  .seq (emit [[]] 22) <| .seq (emit [[]] 28) <| .seq (emit [[]] 29) <| .seq (emit [[false]] 27) (rewind 27)

/-- The state after `constsA`. -/
def stA (ℓ K w D : ℕ) (f : List Bool) : Fin 48 → WTape :=
  fun i => match i.val with
  | 2 => endv 0 | 4 => endv 0 | 7 => reg [] | 8 => reg [true] | 13 => reg (ones 1)
  | 22 => endv 0 | 27 => reg [false] | 28 => endv 0 | 29 => endv 0
  | _ => lstart ℓ K w D f i

set_option maxHeartbeats 8000000 in
theorem runs_constsA (ℓ K w D : ℕ) (f : List Bool) :
    Runs constsA (lstart ℓ K w D f) (· = stA ℓ K w D f) 40 := by
  apply Runs.of_wp
  simp only [constsA, WP, wp_rewind, wp_emit]
  tsimp [lstart, emp]
  funext i; fin_cases i <;> first | rfl | tsimp [lstart, stA, emp, endv, reg, ones]

/-- Copy the flags to the move generator's flag tape. -/
noncomputable def copyFlags : Cmd 0 48 := .seq (rewind 36) <| .seq (appendAll 36 11 (by decide)) (rewind 11)

/-- Copy the axis ticks to the move generator's axis tape. -/
noncomputable def copyTicks : Cmd 0 48 := .seq (rewind 35) <| .seq (appendAll 35 15 (by decide)) (rewind 15)

/-- `ones (ℓ - 1)`. -/
noncomputable def lm1Calc : Cmd 0 48 :=
  .seq (op1 Rules.drop false 32 13 12 (by decide) (by decide) (by decide)) <| .seq (rewind 32) <|
  .seq (rewind 13) (rewind 12)

/-- The state after the copies and `ℓ - 1`. -/
def stB (ℓ K w D : ℕ) (f : List Bool) : Fin 48 → WTape :=
  Function.update (Function.update (Function.update (stA ℓ K w D f) 11 ⟨[], f.map fun b => [b]⟩) 15
    ⟨[], List.replicate D []⟩) 12 (reg (ones (ℓ - 1)))

theorem clen_flagWords : ∀ g : List Bool, clen (g.map fun b => [b]) = 2 * g.length
  | [] => rfl
  | b :: g => by
    have := clen_flagWords g
    simp only [List.map_cons, clen, List.sum_cons, List.length_cons] at this ⊢; simp at this ⊢; omega

set_option maxHeartbeats 8000000 in
theorem runs_copies (ℓ K w D : ℕ) (f : List Bool) :
    Runs (.seq copyFlags (.seq copyTicks lm1Calc)) (stA ℓ K w D f) (· = stB ℓ K w D f)
      (13 * f.length + 10 * D + 4 * ℓ + 60) := by
  set σ := stA ℓ K w D f with hσ
  have a1 := runs_rewind (a := 0) 36 σ
  set σ₁ := Function.update σ 36 ⟨[], (σ 36).left.reverse ++ (σ 36).right⟩ with hσ₁
  have a2 := runs_appendAll (a := 0) (show (36 : Fin 48) ≠ 11 by decide) 1 (f.map fun b => [b]) σ₁ [] []
    (by tsimp [hσ₁, hσ, stA, lstart]) (by tsimp [hσ₁, hσ, stA, lstart, emp])
    (by intro x hx; simp only [List.mem_map] at hx; obtain ⟨b, _, rfl⟩ := hx; simp)
  set σ₂ := Function.update (Function.update σ₁ 36 ⟨(f.map fun b => [b]).reverse ++ [], []⟩) 11
    ⟨(f.map fun b => [b]).reverse ++ [], []⟩ with hσ₂
  have a3 := runs_rewind (a := 0) 11 σ₂
  set σ₃ := Function.update σ₂ 11 ⟨[], (σ₂ 11).left.reverse ++ (σ₂ 11).right⟩ with hσ₃
  have b1 := runs_rewind (a := 0) 35 σ₃
  set σ₄ := Function.update σ₃ 35 ⟨[], (σ₃ 35).left.reverse ++ (σ₃ 35).right⟩ with hσ₄
  have b2 := runs_appendAll (a := 0) (show (35 : Fin 48) ≠ 15 by decide) 0 (List.replicate D []) σ₄ [] []
    (by tsimp [hσ₄, hσ₃, hσ₂, hσ₁, hσ, stA, lstart, List.reverse_replicate])
    (by tsimp [hσ₄, hσ₃, hσ₂, hσ₁, hσ, stA, lstart, emp]) (by simp)
  set σ₅ := Function.update (Function.update σ₄ 35 ⟨(List.replicate D []).reverse ++ [], []⟩) 15
    ⟨(List.replicate D ([] : List Bool)).reverse ++ [], []⟩ with hσ₅
  have b3 := runs_rewind (a := 0) 15 σ₅
  set σ₆ := Function.update σ₅ 15 ⟨[], (σ₅ 15).left.reverse ++ (σ₅ 15).right⟩ with hσ₆
  have t1 : time Rules.drop (List.replicate ℓ true) (fun _ => List.replicate 1 true) ≤ ℓ + 1 + 6 :=
    (time_le Rules.drop (ones ℓ) (fun _ => ones 1) 1 (fun _ => by simp)).trans (by simp)
  have c1 : Runs lm1Calc σ₆ (· = Function.update σ₆ 12 (reg (ones (ℓ - 1)))) (4 * ℓ + 20) := by
    apply Runs.of_wp
    simp only [lm1Calc, WP, wp_op1, wp_rewind]
    tsimp [hσ₆, hσ₅, hσ₄, hσ₃, hσ₂, hσ₁, hσ, stA, lstart, emp, reg, Rules.output_drop, ones, List.drop_replicate]
    refine ⟨?_, ?_⟩
    · funext i; fin_cases i <;> first | rfl | tsimp [hσ₆, hσ₅, hσ₄, hσ₃, hσ₂, hσ₁, hσ, stA, lstart, reg, ones]
    · simp at t1 ⊢; omega
  refine (Runs.seq (Runs.then a1 (Runs.then a2 a3) |>.mono (fun τ h => by
    rw [h]; exact Runs.seq (Runs.then b1 (Runs.then b2 b3) |>.mono (fun τ' h' => by rw [h']; exact c1) le_rfl))
    le_rfl)).mono (fun τ h => ?_) ?_
  · rw [h]; funext i; fin_cases i <;> first | rfl | tsimp [hσ₆, hσ₅, hσ₄, hσ₃, hσ₂, hσ₁, hσ, stB, stA, lstart,
      List.reverse_replicate, reg]
  · have h1 : clen (σ 36).left = 2 * f.length := by
      tsimp [hσ, stA, lstart]; rw [clen_reverse, clen_flagWords]
    have h2 : clen (σ₂ 11).left = 2 * f.length := by
      tsimp [hσ₂]; rw [clen_reverse, clen_flagWords]
    have h3 : clen (σ₃ 35).left = D := by
      tsimp [hσ₃, hσ₂, hσ₁, hσ, stA, lstart, clen]
    have h4 : clen (σ₅ 15).left = D := by tsimp [hσ₅, clen]
    rw [h1, h2, h3, h4]
    simp
    omega

/-! ### Setup, part two: the address length -/

/-- Where the address-length program's tapes sit. -/
def fnv : Fin 6 → ℕ := ![19, 15, 11, 12, 13, 10]

theorem fnv_lt (i : Fin 6) : fnv i < 48 := by fin_cases i <;> decide

/-- The address-length program's tapes in the bank. -/
def fn (i : Fin 6) : Fin 48 := ⟨fnv i, fnv_lt i⟩

theorem fn_injective : Function.Injective fn := by
  intro i j h; have := congrArg Fin.val h; simp only [fn] at this; revert i j; decide

/-- The address length `n = D (ℓ - 1) + #long`. -/
def nOf (ℓ D : ℕ) (f : List Bool) : ℕ := D * (ℓ - 1) + (f.filter id).length

/-- The address length, then `L = n` for the move generator. -/
noncomputable def nPhase : Cmd 0 48 :=
  .seq (nCalc.map fn fn_injective) <| .seq (cpy 19 3 (by decide)) (rewind 19)

/-- The state after the address length. -/
def stC (ℓ K w D : ℕ) (f : List Bool) : Fin 48 → WTape :=
  Function.update (Function.update (stB ℓ K w D f) 19 (reg (ones (nOf ℓ D f)))) 3 (endv (nOf ℓ D f))

set_option maxHeartbeats 8000000 in
theorem runs_nPhase (ℓ K w D : ℕ) (f : List Bool) :
    Runs nPhase (stB ℓ K w D f) (· = stC ℓ K w D f)
      (D * (2 * (ℓ - 1) + 18) + f.length * 30 + 3 * D + 4 * f.length + 3 * (D * (ℓ - 1) + f.length) + 30 +
        4 * nOf ℓ D f + 20) := by
  have hc : stB ℓ K w D f ∘ fn = nbank (ℓ - 1) emp ⟨[], List.replicate D []⟩ ⟨[], f.map fun b => [b]⟩ := by
    funext i; fin_cases i <;> tsimp [fn, fnv, stB, stA, lstart, nbank, emp]
  have s1 := runs_nCalc (ℓ - 1) D f
  rw [← hc] at s1
  have s1' := Runs.map_eq fn fn_injective s1 (Function.update (stB ℓ K w D f) 19 (reg (ones (nOf ℓ D f))))
    (by funext i; fin_cases i <;> tsimp [fn, fnv, stB, stA, lstart, nbank, nOf, emp])
    (by
      intro x hx
      have h19 : x ≠ 19 := fun e => hx 0 (by rw [e]; rfl)
      simp [Function.update_apply, h19])
  set σ := Function.update (stB ℓ K w D f) 19 (reg (ones (nOf ℓ D f))) with hσ
  have s2 : Runs (a := 0) (.seq (cpy 19 3 (by decide)) (rewind 19)) σ (· = stC ℓ K w D f) (2 * nOf ℓ D f + 12) := by
    apply Runs.of_wp
    simp only [cpy, WP, wp_op0, wp_rewind]
    tsimp [hσ, stB, stA, lstart, emp, reg, Rules.output_copy]
    refine ⟨?_, ?_⟩
    · funext i; fin_cases i <;> first | rfl | tsimp [hσ, stC, stB, stA, lstart, reg, endv]
    · simp [time_copy, length_ones, clen]; omega
  refine (Runs.seq (s1'.mono (fun τ h => by rw [h]; exact s2) le_rfl)).mono (fun τ h => h) ?_
  omega

/-! ### Setup, part three: `q` and `b` -/

/-- Where the division program's tapes sit. -/
def fdv : Fin 20 → ℕ := ![39, 33, 0, 1, 40, 41, 2, 3, 4, 5, 7, 8, 9, 42, 43, 10, 14, 16, 17, 18]

theorem fdv_lt (i : Fin 20) : fdv i < 48 := by fin_cases i <;> decide

/-- The division program's tapes in the bank. -/
def fd (i : Fin 20) : Fin 48 := ⟨fdv i, fdv_lt i⟩

theorem fd_injective : Function.Injective fd := by
  intro i j h; have := congrArg Fin.val h; simp only [fd] at this; revert i j; decide

/-- Fuel and a copy of `ℓ - 1`. -/
noncomputable def divPrep : Cmd 0 48 :=
  .seq (op0 Rules.ticks false 12 40 (by decide)) <| .seq (rewind 12) <| .seq (rewind 40) <|
  .seq (cpy 12 39 (by decide)) <| .seq (rewind 12) (rewind 39)

/-- After the division: the level ticks, `c₀ = ℓ - 1 - b`, `s₀ = c₀ + (b - 1)`, cleanup. -/
noncomputable def divPost : Cmd 0 48 :=
  .seq (op0 Rules.ticks false 39 14 (by decide)) <| .seq (rewind 39) <| .seq (rewind 14) <|
  .seq (op1 Rules.drop false 12 39 17 (by decide) (by decide) (by decide)) <| .seq (rewind 12) <|
  .seq (rewind 39) <| .seq (rewind 17) <|
  .seq (op1 Rules.drop false 39 13 43 (by decide) (by decide) (by decide)) <| .seq (rewind 39) <|
  .seq (rewind 13) <| .seq (cpy 17 16 (by decide)) <| .seq (rewind 17) <| .seq (rewind 43) <|
  .seq (op0 Rules.copy true 43 16 (by decide)) <| .seq (rewind 43) <| .seq (rewind 16) <|
  .seq (clear 43) <| .seq (rewind 41) <| .seq (clear 40) (clear 39)

/-- The division phase. -/
noncomputable def divPhase : Cmd 0 48 :=
  .seq divPrep <| .seq (SigmaConstsTape.divLoop.map fd fd_injective) divPost

/-- The state after the division. -/
def stD (ℓ K w D : ℕ) (f : List Bool) : Fin 48 → WTape :=
  Function.update (Function.update (Function.update (Function.update (stC ℓ K w D f) 41
    ⟨[], List.replicate ((ℓ - 1) / K) []⟩) 14 ⟨[], List.replicate ((ℓ - 1) % K) []⟩) 17
    (reg (ones (ℓ - 1 - (ℓ - 1) % K)))) 16 (reg (ones (ℓ - 1 - (ℓ - 1) % K + ((ℓ - 1) % K - 1))))

theorem divRes_self (K x : ℕ) : SigmaConstsTape.divRes K x x = x % K := by
  unfold SigmaConstsTape.divRes
  rw [min_eq_right (Nat.div_le_self x K), Nat.mod_eq_sub_mul_div, mul_comm]

set_option maxHeartbeats 16000000 in
theorem runs_divPhase {ℓ K : ℕ} (hK : 0 < K) (w D : ℕ) (f : List Bool) :
    Runs divPhase (stC ℓ K w D f) (· = stD ℓ K w D f)
      ((ℓ - 1) * (16 * (ℓ - 1) + 10 * K + 110) + 100 * ℓ + 600) := by
  set x := ℓ - 1 with hx
  set σ := stC ℓ K w D f with hσ
  have t0 : time Rules.ticks (ones x) (fun j => j.elim0) ≤ x + 5 :=
    (time_le Rules.ticks (ones x) (fun j => j.elim0) 0 (fun j => j.elim0)).trans (by simp)
  have s1 : Runs divPrep σ (· = Function.update (Function.update σ 40 ⟨[], List.replicate x []⟩) 39 (reg (ones x)))
      (8 * x + 40) := by
    apply Runs.of_wp
    simp only [divPrep, cpy, WP, wp_op0, wp_rewind]
    tsimp [hσ, stC, stB, stA, lstart, emp, reg, Rules.output_ticks, Rules.output_copy, length_ones, ← hx]
    refine ⟨?_, ?_⟩
    · funext i; fin_cases i <;> first | rfl | tsimp [hσ, stC, stB, stA, lstart, reg, List.reverse_replicate, ← hx]
    · simp [time_copy, length_ones] at t0 ⊢; omega
  set σ₁ := Function.update (Function.update σ 40 ⟨[], List.replicate x []⟩) 39 (reg (ones x)) with hσ₁
  have hd := SigmaConstsTape.runs_divLoop hK x x (σ₁ ∘ fd) [] []
    (by tsimp [hσ₁, fd, fdv]) (by tsimp [hσ₁, hσ, fd, fdv, stC, stB, stA, lstart, ← hx])
    (by tsimp [hσ₁, fd, fdv]) (by tsimp [hσ₁, hσ, fd, fdv, stC, stB, stA, lstart, emp])
    (by tsimp [hσ₁, hσ, fd, fdv, stC, stB, stA, lstart, emp]) (by tsimp [hσ₁, hσ, fd, fdv, stC, stB, stA, lstart, emp])
    (by tsimp [hσ₁, hσ, fd, fdv, stC, stB, stA, lstart, emp])
  rw [divRes_self, min_eq_right (Nat.div_le_self x K)] at hd
  set σ₂ := Function.update (Function.update (Function.update σ₁ 39 (reg (ones (x % K)))) 41
    ⟨List.replicate (x / K) [] ++ [], []⟩) 40 ⟨List.replicate x [] ++ [], []⟩ with hσ₂
  have s2 := Runs.map_eq fd fd_injective hd σ₂
    (by funext i; fin_cases i <;> tsimp [hσ₂, fd, fdv])
    (by
      intro y hy
      have h39 : y ≠ 39 := fun e => hy 0 (by rw [e]; rfl)
      have h41 : y ≠ 41 := fun e => hy 5 (by rw [e]; rfl)
      have h40 : y ≠ 40 := fun e => hy 4 (by rw [e]; rfl)
      simp [hσ₂, h39, h41, h40])
  have t1 : time Rules.ticks (List.replicate (x % K) true) (fun j => j.elim0) ≤ x % K + 5 :=
    (time_le Rules.ticks (ones (x % K)) (fun j => j.elim0) 0 (fun j => j.elim0)).trans (by simp)
  have t2 : time Rules.drop (List.replicate x true) (fun _ => List.replicate (x % K) true) ≤ x + x % K + 6 :=
    (time_le Rules.drop (ones x) (fun _ => ones (x % K)) (x % K) (fun _ => by simp)).trans (by simp)
  have t3 : time Rules.drop (List.replicate (x % K) true) (fun _ => [true]) ≤ x % K + 1 + 6 :=
    (time_le Rules.drop (ones (x % K)) (fun _ => ones 1) 1 (fun _ => by simp)).trans (by simp)
  have hmod : x % K ≤ x := Nat.mod_le _ _
  have hdiv : x / K ≤ x := Nat.div_le_self x K
  have s3 : Runs divPost σ₂ (· = stD ℓ K w D f) (80 * x + 500) := by
    apply Runs.of_wp
    simp only [divPost, cpy, WP, wp_op0, wp_op1, wp_rewind, wp_clear]
    tsimp [hσ₂, hσ₁, hσ, stC, stB, stA, lstart, emp, reg, Rules.output_ticks, Rules.output_copy,
      Rules.output_drop, ones, List.drop_replicate, length_ones, ← hx]
    refine ⟨?_, ?_⟩
    · funext i; fin_cases i <;> first | rfl | tsimp [hσ₂, hσ₁, hσ, stD, stC, stB, stA, lstart, reg, ones,
        List.reverse_replicate, List.replicate_add, Nat.sub_sub, ← hx]
    · simp [time_copy, clen, WTape.words] at t1 t2 t3 ⊢
      omega
  refine (Runs.then s1 (Runs.then s2 s3)).mono (fun τ h => h) ?_
  omega

/-! ### Setup, part four: the binary words and `n - 2K` -/

/-- Where the converter for `bin w` sits. -/
def fb1v : Fin 5 → ℕ := ![34, 44, 45, 46, 10]
/-- Where the converter for `bin K` sits. -/
def fb2v : Fin 5 → ℕ := ![33, 24, 45, 46, 10]

theorem fb1v_lt (i : Fin 5) : fb1v i < 48 := by fin_cases i <;> decide
theorem fb2v_lt (i : Fin 5) : fb2v i < 48 := by fin_cases i <;> decide

def fb1 (i : Fin 5) : Fin 48 := ⟨fb1v i, fb1v_lt i⟩
def fb2 (i : Fin 5) : Fin 48 := ⟨fb2v i, fb2v_lt i⟩

theorem fb1_injective : Function.Injective fb1 := by
  intro i j h; have := congrArg Fin.val h; simp only [fb1] at this; revert i j; decide
theorem fb2_injective : Function.Injective fb2 := by
  intro i j h; have := congrArg Fin.val h; simp only [fb2] at this; revert i j; decide

/-- `bin R = 0^(ℓ+1) · bin w` on tape 6. -/
noncomputable def binRGlue : Cmd 0 48 :=
  .seq (op0 (Rules.fill false) false 32 6 (by decide)) <| .seq (rewind 32) <| .seq (emit [[false]] 46) <|
  .seq (rewind 46) <| .seq (op0 Rules.copy true 46 6 (by decide)) <| .seq (clear 46) <|
  .seq (op0 Rules.copy true 44 6 (by decide)) <| .seq (rewind 44) <| .seq (rewind 6) (clear 44)

/-- Subtract `K` from tape 23. -/
noncomputable def subK23 : Cmd 0 48 :=
  .seq (rewind 23) <| .seq (op1 Rules.drop false 23 33 30 (by decide) (by decide) (by decide)) <|
  .seq (clear 23) <| .seq (rewind 30) <| .seq (cpy 30 23 (by decide)) <| .seq (clear 30) (rewind 33)

/-- `n - 2K` on tape 23. -/
noncomputable def nKGlue : Cmd 0 48 :=
  .seq (cpy 19 23 (by decide)) <| .seq (rewind 19) <| .seq subK23 <| .seq subK23 (rewind 23)

/-- The binary words and `n - 2K`. -/
noncomputable def binPhase : Cmd 0 48 :=
  .seq (binOf.map fb1 fb1_injective) <| .seq binRGlue <| .seq (binOf.map fb2 fb2_injective) nKGlue

/-- The record length `R = 2 · 2^ℓ · w`. -/
def recLen (ℓ w : ℕ) : ℕ := 2 * 2 ^ ℓ * w

/-- The state after the binary words. -/
def stE (ℓ K w D : ℕ) (f : List Bool) : Fin 48 → WTape :=
  Function.update (Function.update (Function.update (stD ℓ K w D f) 6 (reg (bin (recLen ℓ w)))) 24
    (reg (bin K))) 23 (reg (ones (nOf ℓ D f - K - K)))

theorem bin_recLen {ℓ w : ℕ} (hw : 0 < w) :
    bin (recLen ℓ w) = List.replicate ℓ false ++ [false] ++ bin w := by
  rw [recLen, show 2 * 2 ^ ℓ * w = 2 ^ (ℓ + 1) * w by ring, bin_two_pow_mul _ _ hw, List.replicate_succ']

set_option maxHeartbeats 16000000 in
theorem runs_binPhase {ℓ K w : ℕ} (hw : 0 < w) (D : ℕ) (f : List Bool) :
    Runs binPhase (stD ℓ K w D f) (· = stE ℓ K w D f)
      (8 * w * w + 76 * w + 8 * K * K + 80 * K + 20 * nOf ℓ D f + 10 * ℓ + 400) := by
  set σ := stD ℓ K w D f with hσ
  -- bin w
  have hb1 : σ ∘ fb1 = bbank w emp emp := by
    funext i; fin_cases i <;> tsimp [hσ, fb1, fb1v, bbank, stD, stC, stB, stA, lstart, emp]
  have s1 := runs_binOf w
  rw [← hb1] at s1
  have s1' := Runs.map_eq fb1 fb1_injective s1 (Function.update σ 44 (reg (bin w)))
    (by funext i; fin_cases i <;> tsimp [fb1, fb1v, bbank, hσ, stD, stC, stB, stA, lstart, emp])
    (by intro y hy; have h44 : y ≠ 44 := fun e => hy 1 (by rw [e]; rfl); simp [h44])
  set σ₁ := Function.update σ 44 (reg (bin w)) with hσ₁
  have hbw : bin w ≠ [] := by
    intro h; have := value_bin w; rw [h] at this; simp [Counter.value] at this; omega
  have s2 : Runs binRGlue σ₁ (· = Function.update σ (6 : Fin 48) (reg (bin (recLen ℓ w)))) (4 * ℓ + 6 * w + 60) := by
    apply Runs.of_wp
    simp only [binRGlue, WP, wp_op0, wp_rewind, wp_emit, wp_clear]
    tsimp [hσ₁, hσ, stD, stC, stB, stA, lstart, emp, reg, Rules.output_fill, Rules.output_copy, length_ones, hbw]
    refine ⟨?_, ?_⟩
    · funext i; fin_cases i <;> first | rfl | tsimp [hσ₁, hσ, stD, stC, stB, stA, lstart, reg, bin_recLen hw, WTape.put]
    · have := length_bin_le w
      have tf := time_fill false (ones ℓ) (fun j => j.elim0)
      simp [time_copy, clen, WTape.words, length_ones] at tf ⊢; omega
  set σ₂ := Function.update σ (6 : Fin 48) (reg (bin (recLen ℓ w))) with hσ₂
  -- bin K
  have hb2 : σ₂ ∘ fb2 = bbank K emp emp := by
    funext i; fin_cases i <;> tsimp [hσ₂, hσ, fb2, fb2v, bbank, stD, stC, stB, stA, lstart, emp]
  have s3 := runs_binOf K
  rw [← hb2] at s3
  have s3' := Runs.map_eq fb2 fb2_injective s3 (Function.update σ₂ 24 (reg (bin K)))
    (by funext i; fin_cases i <;> tsimp [fb2, fb2v, bbank, hσ₂, hσ, stD, stC, stB, stA, lstart, emp])
    (by intro y hy; have h24 : y ≠ 24 := fun e => hy 1 (by rw [e]; rfl); simp [h24])
  set σ₃ := Function.update σ₂ 24 (reg (bin K)) with hσ₃
  -- n - 2K
  have t1 : time Rules.drop (List.replicate (nOf ℓ D f) true) (fun _ => List.replicate K true) ≤
      nOf ℓ D f + K + 6 :=
    (time_le Rules.drop (ones (nOf ℓ D f)) (fun _ => ones K) K (fun _ => by simp)).trans (by simp)
  have t2 : time Rules.drop (List.replicate (nOf ℓ D f - K) true) (fun _ => List.replicate K true) ≤
      nOf ℓ D f - K + K + 6 :=
    (time_le Rules.drop (ones (nOf ℓ D f - K)) (fun _ => ones K) K (fun _ => by simp)).trans (by simp)
  have s4 : Runs nKGlue σ₃ (· = stE ℓ K w D f) (20 * nOf ℓ D f + 10 * K + 100) := by
    apply Runs.of_wp
    simp only [nKGlue, subK23, cpy, WP, wp_op0, wp_op1, wp_rewind, wp_clear]
    tsimp [hσ₃, hσ₂, hσ, stD, stC, stB, stA, lstart, emp, reg, Rules.output_copy, Rules.output_drop, ones,
      List.drop_replicate]
    refine ⟨?_, ?_⟩
    · funext i; fin_cases i <;> first | rfl | tsimp [hσ₃, hσ₂, hσ, stE, stD, stC, stB, stA, lstart, reg, ones,
        Nat.sub_sub]
    · simp [time_copy, clen, WTape.words] at t1 t2 ⊢; omega
  refine (Runs.then s1' (Runs.then s2 (Runs.then s3' s4))).mono (fun τ h => h) ?_
  nlinarith

/-! ### Setup, part five: the arrangement -/

/-- Where the arrangement generator's tapes sit. -/
def fav : Fin 9 → ℕ := ![20, 15, 41, 37, 42, 43, 13, 10, 46]

theorem fav_lt (i : Fin 9) : fav i < 48 := by fin_cases i <;> decide

def fa (i : Fin 9) : Fin 48 := ⟨fav i, fav_lt i⟩

theorem fa_injective : Function.Injective fa := by
  intro i j h; have := congrArg Fin.val h; simp only [fa] at this; revert i j; decide

/-- The arrangement on tape 20, head at the start; the chunk ticks erased. -/
noncomputable def arrPhase : Cmd 0 48 := .seq (arrGen.map fa fa_injective) <| .seq (rewind 20) (clear 41)

/-- The state after the setup. -/
def stF (ℓ K w D : ℕ) (f : List Bool) : Fin 48 → WTape :=
  Function.update (Function.update (stE ℓ K w D f) 20
    ⟨[], (LayoutScript.axisArr ((ℓ - 1) / K) D).map ones⟩) 41 emp

set_option maxHeartbeats 16000000 in
theorem runs_arrPhase (ℓ K w D : ℕ) (f : List Bool) :
    Runs arrPhase (stE ℓ K w D f) (· = stF ℓ K w D f)
      (arrCost D ((ℓ - 1) / K) (D + (ℓ - 1) / K * D) + 4 * ((ℓ - 1) / K * D * (D + (ℓ - 1) / K * D + 1)) +
        4 * ((ℓ - 1) / K) + 20) := by
  set q := (ℓ - 1) / K with hq
  set σ := stE ℓ K w D f with hσ
  have ha : σ ∘ fa = abank D ⟨[], []⟩ ⟨[], List.replicate D []⟩ ⟨[], List.replicate q []⟩ emp emp := by
    funext i; fin_cases i <;> tsimp [hσ, fa, fav, abank, stE, stD, stC, stB, stA, lstart, emp, ← hq]
  have s1 := runs_arrGen (D := D) (q := q) (V := D + q * D) le_rfl
  rw [← ha] at s1
  have s1' := Runs.map_eq fa fa_injective s1
    (Function.update σ 20 ⟨((LayoutScript.axisArr q D).map ones).reverse, []⟩)
    (by funext i; fin_cases i <;> tsimp [fa, fav, abank, hσ, stE, stD, stC, stB, stA, lstart, emp, ← hq])
    (by intro y hy; have h20 : y ≠ 20 := fun e => hy 0 (by rw [e]; rfl); simp [h20])
  set σ₁ := Function.update σ 20 ⟨((LayoutScript.axisArr q D).map ones).reverse, []⟩ with hσ₁
  have s2 := runs_rewind (a := 0) 20 σ₁
  set σ₂ := Function.update σ₁ 20 ⟨[], (σ₁ 20).left.reverse ++ (σ₁ 20).right⟩ with hσ₂
  have s3 := runs_clear (a := 0) 41 σ₂
  refine (Runs.then s1' (Runs.then s2 s3)).mono (fun τ h => ?_) ?_
  · rw [h]; funext i; fin_cases i <;> first | rfl | tsimp [hσ₂, hσ₁, hσ, stF, stE, stD, stC, stB, stA, lstart, emp,
      ← hq]
  · have hW : ∀ x ∈ LayoutScript.axisArr q D, x ≤ D + q * D := fun x hx =>
      ((LayoutSwapTape.good_axisArr (W := q * D) le_rfl).1 x hx).2.trans (by omega)
    have h1 : clen (σ₁ 20).left ≤ q * D * (D + q * D + 1) := by
      have := LayoutSwapTape.clen_ones_le (LayoutScript.axisArr q D) hW
      tsimp [hσ₁, clen_reverse]
      simpa [LayoutScript.axisArr] using this
    have h2 : clen (σ₂ 41).words = q := by
      tsimp [hσ₂, hσ₁, hσ, stE, stD, WTape.words, clen, ← hq]
    rw [h2]
    omega

end LayoutGenRun

end IntegerMultBounds.Schoenhage
