module

public import IntegerMultBounds.MathlibTM2.Routing.MetadataJob

/-!
# Executed copy-and-increment for coordinate operands

The fixed program preserves a live binary coordinate and constructs its successor
in a separate register of the same width. Scratch tapes are restored; width and
value are read from the input. Callers establish room when interpreting the word
as an untruncated natural number.
-/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host

variable {T Q A : ℕ} {P U : Type}

def binarySuccessorProgram (src dst tmp work cy : Fin T) : Pr P T Q A U :=
  .seq (bcopy src dst tmp work) (countIter dst tmp cy)

/-- Construct the next binary coordinate, restoring the operand and scratch. -/
theorem binarySuccessor_exec (body : P → Pr P T Q A U) (src dst tmp work cy : Fin T)
    (hreg : [src, dst, tmp, work].Nodup) (L x : ℕ)
    (v : HS T Q A U) (S : Stacks T A) (hsrc : S.R src = binSyms L x)
    (hdst : S.R dst = []) (htmp : S.R tmp = []) (hwork : S.R work = []) :
    ∃ v', v'.user = v.user ∧
      Exec body (binarySuccessorProgram src dst tmp work cy) (mk v S) (10 * L + 11)
        (mk v' { S with R := Function.update S.R dst (binSyms L (x + 1)) }) := by
  have hn := hreg
  regs_ne hn
  obtain ⟨v₁, hu₁, he₁⟩ := bcopy_exec body hreg v S htmp hwork
  let S₁ : Stacks T A := { S with R := Function.update S.R dst (S.R src ++ S.R dst) }
  have hdst₁ : S₁.R dst = binSyms L x := by simp [S₁, hsrc, hdst]
  have htmp₁ : S₁.R tmp = [] := by simp [S₁, Ne.symm ‹dst ≠ tmp›, htmp]
  obtain ⟨v₂, hu₂, he₂⟩ := countIter_exec body (c := dst) (tmp := tmp) ‹dst ≠ tmp› cy v₁ S₁ hdst₁ htmp₁
  refine ⟨v₂, hu₂.trans hu₁, ?_⟩
  refine Exec.cast (Exec.seq he₁ he₂) ?_ ?_
  · rw [hsrc, length_binSyms]
    omega
  · simp only [S₁, Function.update_idem]

end IntegerMultBounds.MathlibTM2.Routing
