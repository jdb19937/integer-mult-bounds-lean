module

public import IntegerMultBounds.MathlibTM2.Routing.SelectorRunLoopData

/-! One fixed loop expands an arbitrary compact sparse selector stream. Input
is archived for rewind; only input, archive and output change. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host

variable {T Q A W : ℕ} {P U : Type}

def selectorRunLoopBody (rg : SelectorRunReg → Fin T) : Pr P T Q A U :=
  .seq (selectorRunStepProgram rg) (.act (peekR (rg .src)))

theorem selectorRunLoop_exec (body : P → Pr P T Q A U)
    (rg : SelectorRunReg → Fin T) (hrg : Function.Injective rg)
    (Lg L : ℕ) (runs : List (SparseSelectorRun W)) (hfit : ∀ run ∈ runs, run.gap < 2 ^ Lg)
    (v : HS T Q A U) (S : Stacks T A)
    (hsrc : S.R (rg .src) = selectorRunFrames Lg L runs)
    (hblock : S.R (rg .block) = binSyms L 0 ++ [separator])
    (hblank : ∀ r, r ≠ .src → r ≠ .archive → r ≠ .block → r ≠ .dst → S.R (rg r) = [])
    (hflag : v.flag = (selectorRunFrames (A := A) Lg L runs).head?.isSome) :
    ∃ (v' : HS T Q A U) (steps : ℕ), v'.user = v.user ∧
      steps ≤ selectorRunLoopCost Lg L runs ∧
      Exec body (.loop (·.flag) (selectorRunLoopBody rg)) (mk v S) steps
        (mk v' { S with R := selectorRunLoopBank S.R rg Lg L runs }) := by
  induction runs generalizing v S with
  | nil =>
    refine ⟨v, 1, rfl, by simp [selectorRunLoopCost], ?_⟩
    rw [selectorRunLoopBank_nil S.R rg hrg Lg L hsrc]
    exact Exec.loop_false (by simpa only [selectorRunFrames, List.head?_nil, Option.isSome_none, mk_var] using hflag)
  | cons run runs ih =>
    obtain ⟨v₁, n₁, hu₁, ht₁, he₁⟩ := selectorRunStep_exec body rg hrg Lg L run.gap
      (hfit run (by simp)) run.selector (selectorRunFrames Lg L runs) v S hsrc hblock hblank
    let S₁ : Stacks T A := { S with R := selectorRunStepBank S.R rg Lg L run.gap run.selector (selectorRunFrames Lg L runs) }
    have hi : S₁.R (rg .src) = selectorRunFrames Lg L runs := by
      simp [S₁, selectorRunStepBank, hrg.eq_iff]
    have hb : S₁.R (rg .block) = binSyms L 0 ++ [separator] := by
      simp [S₁, selectorRunStepBank, hrg.eq_iff, hblock]
    have hblank₁ := selectorRunStepBank_blank S.R rg hrg Lg L run.gap run.selector (selectorRunFrames Lg L runs) hblank
    let v₂ := { v₁ with flag := (selectorRunFrames (A := A) Lg L runs).head?.isSome }
    have hp : (peekR (rg .src) : Act T Q A U).run (mk v₁ S₁) = mk v₂ S₁ := by
      simp only [peekR_run, hi]; rfl
    obtain ⟨v₃, n₃, hu₃, ht₃, he₃⟩ := ih (fun r hr => hfit r (by simp [hr])) v₂ S₁ hi hb hblank₁ rfl
    have hf : v.flag = true := by
      obtain ⟨x, xs, hx⟩ := List.exists_cons_of_ne_nil (selectorRunFrames_cons_ne_nil (A := A) Lg L run runs)
      simpa only [hx, List.head?_cons, Option.isSome_some] using hflag
    have hbank := selectorRunLoopBank_step S.R rg hrg Lg L run runs
    change selectorRunLoopBank S₁.R rg Lg L runs = _ at hbank
    rw [hbank] at he₃
    have hex := Exec.loop_true (body := body) (f := (·.flag)) (by simpa only [mk_var] using hf)
      (Exec.seq he₁ (hp ▸ Exec.act (body := body) (peekR (rg .src)) (mk v₁ S₁))) he₃
    refine ⟨v₃, n₁ + n₃ + 2, hu₃.trans hu₁, ?_, Exec.cast hex (by omega) rfl⟩
    simp only [selectorRunLoopCost]
    omega

end IntegerMultBounds.MathlibTM2.Routing
