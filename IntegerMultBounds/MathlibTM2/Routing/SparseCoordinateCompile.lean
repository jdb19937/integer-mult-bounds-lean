module

public import IntegerMultBounds.MathlibTM2.Routing.SparseCoordinateFrame

/-! Traverse absolute sparse coordinates and rewind their full input archive.
Only the compact output and advanced cursor change. All traversal is fixed code. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host

variable {T Q A : ℕ} {P U : Type}

def sparseCoordinateCompileProgram (rg : SparseCoordinateReg → Fin T) : Pr P T Q A U :=
  .seq (.act (peekR (rg .src))) (.seq (.loop (·.flag) (sparseCoordinateLoopBody rg))
    (moveR (rg .archive) (rg .src) id))

theorem sparseCoordinateCompile_exec (body : P → Pr P T Q A U)
    (rg : SparseCoordinateReg → Fin T) (hrg : Function.Injective rg)
    (L Ls cursor : ℕ) (entries : List (ℕ × ℕ)) (hready : SparseCoordinatesReady L cursor entries)
    (v : HS T Q A U) (S : Stacks T A)
    (hsrc : S.R (rg .src) = sparseCoordinateFrames L Ls entries) (harchive : S.R (rg .archive) = [])
    (hcursor : S.R (rg .cursor) = binSyms L cursor) (hone : S.R (rg .one) = binSyms L 1)
    (hblank : ∀ r, r ≠ .src → r ≠ .archive → r ≠ .cursor → r ≠ .one → r ≠ .dst → S.R (rg r) = []) :
    ∃ v', v'.user = v.user ∧
      Exec body (sparseCoordinateCompileProgram rg) (mk v S)
        (entries.length * (32 * L + 12 * Ls + 54) + 2 * (sparseCoordinateFrames (A := A) L Ls entries).length + 4)
        (mk v' { S with R := Function.update (Function.update S.R (rg .dst) (sparseCoordinateOutput L Ls cursor entries ++ S.R (rg .dst))) (rg .cursor) (binSyms L (sparseCoordinateEnd cursor entries)) }) := by
  let input := sparseCoordinateFrames (A := A) L Ls entries
  let v₁ := { v with flag := input.head?.isSome }
  have hp : (peekR (rg .src) : Act T Q A U).run (mk v S) = mk v₁ S := by
    simp only [peekR_run, hsrc]; rfl
  obtain ⟨v₂, n₂, hu₂, ht₂, he₂⟩ := sparseCoordinateLoop_exec body rg hrg L Ls cursor entries hready
    v₁ S hsrc hcursor hone hblank rfl
  let S₂ : Stacks T A := { S with R := sparseCoordinateTraceBank S.R rg L Ls cursor entries }
  obtain ⟨v₃, hu₃, he₃⟩ := moveR_exec body (rg .archive) (rg .src) (hrg.ne (by decide)) id v₂ S₂
  have ha : S₂.R (rg .archive) = input.reverse := by
    dsimp only [S₂]
    rw [sparseCoordinateTrace_archive S.R rg hrg L Ls cursor entries, harchive, List.append_nil]
  have hs : S₂.R (rg .src) = [] := sparseCoordinateTrace_src S.R rg hrg L Ls cursor entries hsrc
  have hd := sparseCoordinateTrace_output S.R rg hrg L Ls cursor entries
  have hc := sparseCoordinateTrace_cursor S.R rg L Ls cursor entries hcursor
  have hf : movedR S₂.R (rg .archive) (rg .src) id (S₂.R (rg .archive)) =
      Function.update (Function.update S.R (rg .dst) (sparseCoordinateOutput L Ls cursor entries ++ S.R (rg .dst)))
        (rg .cursor) (binSyms L (sparseCoordinateEnd cursor entries)) := by
    rw [ha]
    funext j
    by_cases hj : j = rg .src
    · subst j; simp [movedR, hs, input, hsrc, hrg.eq_iff]
    · by_cases hjA : j = rg .archive
      · subst j; simp [movedR, harchive, hrg.eq_iff]
      · by_cases hjC : j = rg .cursor
        · subst j; simp [movedR, hj, hjA, S₂, hc]
        · by_cases hjD : j = rg .dst
          · subst j; simp [movedR, hj, hjA, hjC, S₂, hd]
          · simp only [movedR, Function.update_of_ne hjA, Function.update_of_ne hj, Function.update_of_ne hjC, Function.update_of_ne hjD]
            exact sparseCoordinateTrace_keep S.R rg L Ls cursor entries j hj hjA hjC hjD
  rw [hf, ha, List.length_reverse] at he₃
  refine ⟨v₃, hu₃.trans hu₂, ?_⟩
  have he := Exec.seq (hp ▸ Exec.act (body := body) (peekR (rg .src)) (mk v S)) (Exec.seq he₂ he₃)
  dsimp only [input] at he
  convert he using 1 <;> first | omega | rfl

end IntegerMultBounds.MathlibTM2.Routing
