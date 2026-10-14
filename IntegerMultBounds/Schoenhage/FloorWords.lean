module

public import IntegerMultBounds.Schoenhage.LineFit
public import IntegerMultBounds.Resampling.NeumannWords

/-! Flooring two's complement words by one bit: drop the lowest bit and keep
the low `w` bits. `floorLoop` maps every word of tape `0` onto tape `4`
(`runs_floorLoop`); the signed value of the result is the floor of half the
original when it fits in `w` bits (`signed_floorWord`). -/

@[expose] public section

set_option maxRecDepth 10000

namespace IntegerMultBounds.Schoenhage

open Machine Strm

variable {a : ℕ}

/-- Drop the lowest bit, then keep `w` bits. -/
def floorWord (w : ℕ) (x : List Bool) : List Bool := Rules.fit w (x.drop 1)

/-- Tape `0`: the words; `1`: the word `[true]`; `2`: `w` in unary; `3`: scratch; `4`: the output. -/
noncomputable def floorLoop : Cmd a 5 :=
  .loop 0 (.seq (op1 Rules.drop false 0 1 3 (by decide) (by decide) (by decide)) <| .seq (rewind 1) <|
    .seq (rewind 3) <| .seq (op1 Rules.take false 2 3 4 (by decide) (by decide) (by decide)) <|
    .seq (rewind 2) (clear 3))

theorem runs_floorLoop {w W : ℕ} :
    ∀ (ls : List (List Bool)) (σ : Fin 5 → WTape) (Ls Os : List (List Bool)),
      (∀ x ∈ ls, x.length ≤ W) → σ 1 = reg [true] → σ 2 = reg (ones w) → σ 3 = emp →
      σ 0 = ⟨Ls, ls⟩ → σ 4 = ⟨Os, []⟩ →
      Runs (a := a) floorLoop σ (· = Function.update (Function.update σ 0 ⟨ls.reverse ++ Ls, []⟩) 4
        ⟨(ls.map (floorWord w)).reverse ++ Os, []⟩) (ls.length * (8 * w + 8 * W + 70))
  | [], σ, Ls, Os, _, _, _, _, h0, h4 => by
    refine (Runs.loop_done (by simp [h0]) rfl).mono (fun σ' e => ?_) (by simp)
    rw [← e]; funext y
    by_cases a1 : y = 0 <;> by_cases a2 : y = 4 <;> simp_all
  | l :: ls, σ, Ls, Os, hW, h1, h2, h3, h0, h4 => by
    have hl := hW l (by simp)
    have s1 : Runs (a := a) (.seq (op1 Rules.drop false 0 1 3 (by decide) (by decide) (by decide)) <|
        .seq (rewind 1) <| .seq (rewind 3) <| .seq (op1 Rules.take false 2 3 4 (by decide) (by decide) (by decide)) <|
        .seq (rewind 2) (clear 3)) σ
        (· = Function.update (Function.update σ 0 ⟨l :: Ls, ls⟩) 4 ⟨[floorWord w l] ++ Os, []⟩)
        (8 * w + 8 * l.length + 60) := by
      apply Runs.of_wp
      simp only [WP, wp_op1, wp_rewind, wp_clear]
      have c0 : (σ 0).cur = l := by rw [h0]; rfl
      have c1 : (σ 1).cur = [true] := by rw [h1]; rfl
      simp only [c0, c1, Rules.output_drop, parse_syms]
      refine ⟨⟨by simp [h0], by simp [h1, reg], by simp [h3, emp], by simp, by simp⟩, ?_⟩
      simp only [Function.update_self, Function.update_of_ne (show (1 : Fin 5) ≠ 3 by decide),
        Function.update_of_ne (show (2 : Fin 5) ≠ 3 by decide),
        Function.update_of_ne (show (2 : Fin 5) ≠ 1 by decide), Function.update_of_ne (show (2 : Fin 5) ≠ 0 by decide),
        Function.update_of_ne (show (4 : Fin 5) ≠ 3 by decide), Function.update_of_ne (show (4 : Fin 5) ≠ 1 by decide),
        Function.update_of_ne (show (4 : Fin 5) ≠ 0 by decide), Function.update_of_ne (show (3 : Fin 5) ≠ 1 by decide),
       
        Function.update_of_ne (show (3 : Fin 5) ≠ 2 by decide),
        h1, h2, h3, h4, h0, reg, emp, WTape.next_mk, WTape.cur_mk, WTape.put_false, List.headD_cons, List.tail_cons,
        List.reverse_nil, List.nil_append, List.reverse_cons, List.append_nil]
      simp only [Rules.output_take, parse_syms, length_ones]
      refine ⟨⟨by simp, by simp, by simp, by simp, by simp⟩, ?_⟩
      refine ⟨?_, ?_⟩
      · funext y
        fin_cases y <;> simp [floorWord, h1, h2, h3, reg, emp]
      · have t1 := time_le Rules.drop l (fun _ => [true]) 1 (fun _ => by simp)
        have t2 := time_le Rules.take (ones w) (fun _ => l.drop 1) l.length (fun _ => by simp)
        simp only [length_ones] at t2
        rcases l with _ | ⟨b, l'⟩
        · simp [clen, WTape.words] at t1 t2 ⊢; omega
        · simp [clen, WTape.words] at t1 t2 hl ⊢; omega
    have ih := runs_floorLoop (w := w) (W := W) ls (Function.update (Function.update σ 0 ⟨l :: Ls, ls⟩) 4
        ⟨[floorWord w l] ++ Os, []⟩) (l :: Ls) (floorWord w l :: Os) (fun y hy => hW y (by simp [hy]))
      (by simp [h1]) (by simp [h2]) (by simp [h3]) (by simp) (by simp)
    refine (Runs.loop_step (by simp [h0]) (s1.mono (fun σ' e => by rw [e]; exact ih) le_rfl)).mono
      (fun σ' e => ?_) ?_
    · rw [e]; funext y
      by_cases a1 : y = 0 <;> by_cases a2 : y = 4 <;> simp_all
    · simp only [List.length_cons]; nlinarith

/-! ### Values -/

open TwosComplement in
theorem signed_cons (b : Bool) (y : List Bool) (hy : y ≠ []) :
    signed (b :: y) = (if b then 1 else 0) + 2 * signed y := by
  unfold signed
  rw [List.getLastD_cons, getLastD_eq y hy, getLastD_eq y hy]
  simp only [Counter.value, List.length_cons, pow_succ]
  split_ifs <;> push_cast <;> ring

open TwosComplement in
/-- The floored word has the floor of half the original value when it fits. -/
theorem signed_floorWord (w : ℕ) (x : List Bool) (hw : 1 ≤ w) (hwx : w + 1 ≤ x.length)
    (h1 : -(2 : ℤ) ^ (w - 1) ≤ signed x / 2) (h2 : signed x / 2 < 2 ^ (w - 1)) :
    signed (floorWord w x) = signed x / 2 := by
  obtain ⟨b, y, rfl⟩ : ∃ b y, x = b :: y := by
    cases x with
    | nil => simp at hwx
    | cons b y => exact ⟨b, y, rfl⟩
  have hy : y ≠ [] := by intro e; subst e; simp at hwx; omega
  have hcons := signed_cons b y hy
  have hdiv : signed (b :: y) / 2 = signed y := by
    rw [hcons]; split_ifs <;> omega
  rw [hdiv] at h1 h2
  simp only [List.length_cons] at hwx
  rw [floorWord, List.drop_one, List.tail_cons, fit_take _ _ (by omega), hdiv]
  exact Resampling.NeumannWords.signed_take y w hw (by omega) h1 h2

end IntegerMultBounds.Schoenhage
