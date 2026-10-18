module

public import IntegerMultBounds.MathlibTM2.DFT.HostSteps
import Mathlib.Tactic.Ring

/-!
# A loop over a counter register

`M.countLoop D B F iter` tests register `F`, then runs rounds of `iter`, each followed by a new
test of `F`, while `F` is nonempty. `countLoop_exec`: from an invariant `Inv` that fixes when `F`
is nonempty (`Inv i → (F nonempty ↔ i < n)`) and ignores the flag, with every round taking
`Inv i` to `Inv (i + 1)` in at most `c` steps, the loop takes `Inv 0` to `Inv n` in at most
`n (c + 2) + 2` steps.
-/

@[expose] public section

open Computability IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host

namespace IntegerMultBounds.MathlibTM2.DFT

namespace HostMultiplier

variable {κ : ℝ} (M : HostMultiplier κ) (D : ℕ) (B : Type)

/-- Rounds of `iter` while register `F` is nonempty. -/
def countLoop (F : Fin (M.T + D)) (iter : DPr (Option M.P) (M.T + D) M.Q M.A (M.U × B)) :
    DPr (Option M.P) (M.T + D) M.Q M.A (M.U × B) :=
  .seq (hostCode (.act (peekR F))) (.loop (·.flag) (.seq iter (hostCode (.act (peekR F)))))

theorem countLoop_exec (main : DPr (Option M.P) (M.T + D) M.Q M.A (M.U × B))
    (F : Fin (M.T + D)) (iter : DPr (Option M.P) (M.T + D) M.Q M.A (M.U × B))
    (Inv : ℕ → HS (M.T + D) M.Q M.A (M.U × B) → Stacks (M.T + D) M.A → Prop) (n c : ℕ)
    (gi go : List Γ')
    (hflag : ∀ i v S b, Inv i v S → Inv i { v with flag := b } S)
    (hF : ∀ i v S, Inv i v S → ((S.R F).head?.isSome = true ↔ i < n))
    (hstep : ∀ i, i < n → ∀ v S, Inv i v S → ∃ v' S' m, Inv (i + 1) v' S' ∧ m ≤ c ∧
      Exec (M.tab D B main) iter (dmk v S gi go) m (dmk v' S' gi go))
    (v : HS (M.T + D) M.Q M.A (M.U × B)) (S : Stacks (M.T + D) M.A) (h0 : Inv 0 v S) :
    ∃ v' S' m, Inv n v' S' ∧ m ≤ n * (c + 2) + 2 ∧
      Exec (M.tab D B main) (M.countLoop D B F iter) (dmk v S gi go) m (dmk v' S' gi go) := by
  have aux : ∀ j i v S, i + j = n → Inv i v S → v.flag = (S.R F).head?.isSome →
      ∃ v' S' m, Inv n v' S' ∧ m ≤ j * (c + 2) + 1 ∧
        Exec (M.tab D B main) (.loop (·.flag) (.seq iter (hostCode (.act (peekR F)))))
          (dmk v S gi go) m (dmk v' S' gi go) := by
    intro j
    induction j with
    | zero =>
      intro i v S hij hI hf
      obtain rfl : i = n := by omega
      have hfl : v.flag = false := by
        rw [hf]
        cases h : (S.R F).head?.isSome
        · rfl
        · exact absurd ((hF i v S hI).1 h) (lt_irrefl _)
      exact ⟨v, S, 1, hI, by omega, Exec.loop_false hfl⟩
    | succ j ih =>
      intro i v S hij hI hf
      have hin : i < n := by omega
      have hft : v.flag = true := by rw [hf]; exact (hF i v S hI).2 hin
      obtain ⟨v₁, S₁, m₁, hI₁, hm₁, e₁⟩ := hstep i hin v S hI
      have e₂ := M.peek_exec D B main F v₁ S₁ gi go
      obtain ⟨v₂, S₂, m₂, hI₂, hm₂, e₃⟩ := ih (i + 1)
        { v₁ with flag := (S₁.R F).head?.isSome } S₁ (by omega) (hflag _ _ _ _ hI₁) rfl
      refine ⟨v₂, S₂, m₁ + 1 + m₂ + 1, hI₂, ?_, Exec.loop_true hft (Exec.seq e₁ e₂) e₃⟩
      have : (j + 1) * (c + 2) = j * (c + 2) + (c + 2) := by ring
      omega
  obtain ⟨v', S', m, hI, hm, e⟩ := aux n 0 { v with flag := (S.R F).head?.isSome } S (by omega)
    (hflag _ _ _ _ h0) rfl
  exact ⟨v', S', 1 + m, hI, by omega, Exec.seq (M.peek_exec D B main F v S gi go) e⟩

end HostMultiplier

end IntegerMultBounds.MathlibTM2.DFT
