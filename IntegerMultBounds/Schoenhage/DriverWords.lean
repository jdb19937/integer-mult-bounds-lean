module

public import IntegerMultBounds.Schoenhage.DriverMath

/-! Word formats inside the transform drivers: an array as one word, or as its
component words. `joinAll` concatenates the remaining words of a tape into one
word on another (`runs_joinAll`); `chunkw` cuts one word into component words. -/

@[expose] public section

namespace IntegerMultBounds.Schoenhage

open Machine Strm

variable {a t : ℕ}

/-- Append each remaining word of `s` to the last word of `d`. -/
noncomputable def joinLoop' (s d : Fin t) (h : s ≠ d) : Cmd a t := .loop s (op0 Rules.copy true s d h)

/-- Concatenate the remaining words of `s` into one new word on `d`. -/
noncomputable def joinAll (s d : Fin t) (h : s ≠ d) : Cmd a t := .seq (emit [[]] d) (joinLoop' s d h)

theorem runs_joinLoop' {s d : Fin t} (h : s ≠ d) :
    ∀ (ws : List (List Bool)) (σ : Fin t → WTape) (Ls Ld : List (List Bool)) (acc : List Bool),
      σ s = ⟨Ls, ws⟩ → σ d = ⟨acc :: Ld, []⟩ →
      Runs (a := a) (joinLoop' s d h) σ
        (· = Function.update (Function.update σ s ⟨ws.reverse ++ Ls, []⟩) d ⟨(acc ++ ws.flatten) :: Ld, []⟩)
        (ws.length * 10 + clen ws)
  | [], σ, Ls, Ld, acc, hs, hd => by
    refine (Runs.loop_done (by simp [hs]) rfl).mono (fun τ e => ?_) (by simp)
    subst e
    funext y
    by_cases hy : y = d
    · subst hy; simp [hd]
    · by_cases hy' : y = s
      · subst hy'; simp [hy, hs]
      · simp [hy, hy']
  | x :: ws, σ, Ls, Ld, acc, hs, hd => by
    have s1 := runs_op0 (a := a) Rules.copy true h σ (by simp [hs]) (by simp [hd]) [x]
      (by simp [hs, WTape.cur, Rules.output_copy]) (by simp [hd])
    set σ₁ := Function.update (Function.update σ s (σ s).next) d ((σ d).put true [x])
    have h₁ : σ₁ s = ⟨x :: Ls, ws⟩ := by simp [σ₁, h, hs, WTape.next, WTape.cur]
    have h₂ : σ₁ d = ⟨(acc ++ x) :: Ld, []⟩ := by simp [σ₁, hd, WTape.put]
    have ih := runs_joinLoop' h ws σ₁ (x :: Ls) Ld (acc ++ x) h₁ h₂
    refine (Runs.loop_step (by simp [hs]) (s1.mono (fun τ e => by rw [e]; exact ih) le_rfl)).mono
      (fun τ e => ?_) ?_
    · rw [e]
      funext y
      by_cases hy : y = d
      · subst hy; simp
      · by_cases hy' : y = s
        · subst hy'; simp [hy]
        · simp [σ₁, hy, hy']
    · simp [hs, WTape.cur, time_copy, clen_cons]; omega

theorem runs_joinAll {s d : Fin t} (h : s ≠ d) (ws : List (List Bool)) (σ : Fin t → WTape)
    (Ls Ld : List (List Bool)) (hs : σ s = ⟨Ls, ws⟩) (hd : σ d = ⟨Ld, []⟩) :
    Runs (a := a) (joinAll s d h) σ
      (· = Function.update (Function.update σ s ⟨ws.reverse ++ Ls, []⟩) d ⟨ws.flatten :: Ld, []⟩)
      (ws.length * 10 + clen ws + 2) := by
  have s1 := runs_emit (a := a) [[]] d σ (by simp [hd])
  set σ₁ := Function.update σ d ⟨[[]].reverse ++ (σ d).left, []⟩
  have ih := runs_joinLoop' (a := a) h ws σ₁ Ls Ld [] (by simp [σ₁, h, hs]) (by simp [σ₁, hd])
  refine (Runs.then s1 ih).mono (fun τ e => ?_) (by simp [clen]; omega)
  rw [e]
  funext y
  by_cases hy : y = d
  · subst hy; simp
  · by_cases hy' : y = s
    · subst hy'; simp [σ₁, hy]
    · simp [σ₁, hy, hy']

end IntegerMultBounds.Schoenhage
