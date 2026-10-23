module

public import IntegerMultBounds.MathlibTM2.Routing.SelectorRunLoop

/-! Expand a compact selector stream and rewind its complete archived input.
Only the dense selector output changes; the traversal code is fixed. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host

variable {T Q A W : ℕ} {P U : Type}

def selectorRunCompileProgram (rg : SelectorRunReg → Fin T) : Pr P T Q A U :=
  .seq (.act (peekR (rg .src)))
    (.seq (.loop (·.flag) (selectorRunLoopBody rg)) (moveR (rg .archive) (rg .src) id))

theorem selectorRunCompile_exec (body : P → Pr P T Q A U)
    (rg : SelectorRunReg → Fin T) (hrg : Function.Injective rg)
    (Lg L : ℕ) (runs : List (SparseSelectorRun W)) (hfit : ∀ run ∈ runs, run.gap < 2 ^ Lg)
    (v : HS T Q A U) (S : Stacks T A)
    (hsrc : S.R (rg .src) = selectorRunFrames Lg L runs)
    (harchive : S.R (rg .archive) = [])
    (hblock : S.R (rg .block) = binSyms L 0 ++ [separator])
    (hblank : ∀ r, r ≠ .src → r ≠ .archive → r ≠ .block → r ≠ .dst → S.R (rg r) = []) :
    ∃ (v' : HS T Q A U) (steps : ℕ), v'.user = v.user ∧
      steps ≤ selectorRunLoopCost Lg L runs + 2 * (selectorRunFrames (A := A) Lg L runs).length + 3 ∧
      Exec body (selectorRunCompileProgram rg) (mk v S) steps
        (mk v' { S with R := Function.update S.R (rg .dst) (descriptorSelectorFrames L (SparseSelectorRun.expand runs.reverse) ++ S.R (rg .dst)) }) := by
  let input := selectorRunFrames (A := A) Lg L runs
  let rows := descriptorSelectorFrames (A := A) L (SparseSelectorRun.expand runs.reverse)
  let v₁ := { v with flag := input.head?.isSome }
  have hp : (peekR (rg .src) : Act T Q A U).run (mk v S) = mk v₁ S := by
    simp only [peekR_run, hsrc]; rfl
  obtain ⟨v₂, n₂, hu₂, ht₂, he₂⟩ := selectorRunLoop_exec body rg hrg Lg L runs hfit v₁ S hsrc hblock hblank rfl
  let S₂ : Stacks T A := { S with R := selectorRunLoopBank S.R rg Lg L runs }
  obtain ⟨v₃, hu₃, he₃⟩ := moveR_exec body (rg .archive) (rg .src) (hrg.ne (by decide)) id v₂ S₂
  have ha : S₂.R (rg .archive) = input.reverse := by simp [S₂, selectorRunLoopBank, hrg.eq_iff, harchive, input]
  have hf : movedR S₂.R (rg .archive) (rg .src) id (S₂.R (rg .archive)) =
      Function.update S.R (rg .dst) (rows ++ S.R (rg .dst)) := by
    rw [ha]
    funext j
    by_cases hs : j = rg .src
    · subst j; simp [movedR, S₂, selectorRunLoopBank, hrg.eq_iff, hsrc, input]
    · by_cases ha : j = rg .archive
      · subst j; simp [movedR, hrg.eq_iff, harchive]
      · by_cases hd : j = rg .dst
        · subst j; simp [movedR, S₂, selectorRunLoopBank, hs, ha, rows]
        · simp [movedR, S₂, selectorRunLoopBank, hs, ha, hd]
  rw [hf, ha, List.length_reverse] at he₃
  exact ⟨v₃, 1 + (n₂ + (2 * input.length + 2)), hu₃.trans hu₂, by dsimp only [input]; omega,
    Exec.seq (hp ▸ Exec.act (body := body) (peekR (rg .src)) (mk v S)) (Exec.seq he₂ he₃)⟩

end IntegerMultBounds.MathlibTM2.Routing
