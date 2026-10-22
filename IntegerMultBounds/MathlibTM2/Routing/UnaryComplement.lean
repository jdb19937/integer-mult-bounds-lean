module

public import IntegerMultBounds.MathlibTM2.Routing.BinarySuccessor
public import IntegerMultBounds.MathlibTM2.Routing.UnaryDifference

/-!
# Executed coordinate complements

From binary width x and coordinate y<x, construct x-(y+1) unary ticks.
Successor generation, subtraction, unary conversion and clearing both temporary
binary words execute; the original width and coordinate are restored.
-/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2.Node (tick)

variable {T Q A : ℕ} {P U : Type}

def unaryComplementProgram (width coord next bin dst work tx ty tz cy : Fin T) : Pr P T Q A U :=
  .seq (binarySuccessorProgram coord next tx ty cy)
    (.seq (unaryDifferenceProgram width next bin dst work tx ty tz cy) (bclear next))

/-- Construct the high-padding tape directly from binary width and coordinate. -/
theorem unaryComplement_exec (body : P → Pr P T Q A U)
    (width coord next bin dst work tx ty tz cy : Fin T)
    (hreg : [width, coord, next, bin, dst, work, tx, ty, tz].Nodup)
    (hcw : cy ≠ width) (hcn : cy ≠ next)
    (L x y : ℕ) (hx : x < 2 ^ L) (hy : y < x)
    (v : HS T Q A U) (S : Stacks T A)
    (hwidth : S.R width = binSyms L x) (hcoord : S.R coord = binSyms L y)
    (hnext : S.R next = []) (hbin : S.R bin = []) (hdst : S.R dst = [])
    (hwork : S.R work = []) (htx : S.R tx = []) (hty : S.R ty = []) (htz : S.R tz = []) :
    ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧
      m ≤ L * (4 * (x - (y + 1)) + 33) + 2 * (x - (y + 1)) + 29 ∧
      Exec body (unaryComplementProgram width coord next bin dst work tx ty tz cy) (mk v S) m
        (mk v' { S with R := Function.update S.R dst (List.replicate (x - (y + 1)) tick) }) := by
  have hn := hreg
  regs_ne hn
  obtain ⟨v₁, hu₁, he₁⟩ := binarySuccessor_exec body coord next tx ty cy (by regs_nodup)
    L y v S hcoord hnext htx hty
  let S₁ : Stacks T A := { S with R := Function.update S.R next (binSyms L (y + 1)) }
  obtain ⟨v₂, m₂, hu₂, hm₂, he₂⟩ := unaryDifference_exec body width next bin dst work tx ty tz cy
    (by regs_nodup) hcw hcn L x (y + 1) hx (by omega) v₁ S₁
    (by simp [S₁, ‹width ≠ next›, hwidth]) (by simp [S₁])
    (by simp [S₁, Ne.symm ‹next ≠ bin›, hbin])
    (by simp [S₁, Ne.symm ‹next ≠ dst›, hdst])
    (by simp [S₁, Ne.symm ‹next ≠ work›, hwork])
    (by simp [S₁, Ne.symm ‹next ≠ tx›, htx])
    (by simp [S₁, Ne.symm ‹next ≠ ty›, hty])
    (by simp [S₁, Ne.symm ‹next ≠ tz›, htz])
  let S₂ : Stacks T A := { S₁ with R := Function.update S₁.R dst (List.replicate (x - (y + 1)) tick) }
  have hnext₂ : S₂.R next = binSyms L (y + 1) := by simp [S₂, S₁, ‹next ≠ dst›]
  obtain ⟨v₃, hu₃, _, he₃⟩ := bclear_exec body next v₂ S₂
  have hfinal : Function.update S₂.R next [] = Function.update S.R dst (List.replicate (x - (y + 1)) tick) := by
    funext j
    by_cases hj : j = next
    · subst j; simp [‹next ≠ dst›, hnext]
    · by_cases hk : j = dst
      · subst j; simp [S₂, Ne.symm ‹next ≠ dst›]
      · simp [S₂, S₁, hj, hk]
  refine ⟨v₃, (10 * L + 11) + (m₂ + (2 * (S₂.R next).length + 2)), hu₃.trans (hu₂.trans hu₁), ?_, ?_⟩
  · rw [hnext₂, length_binSyms]
    have he : L * (4 * (x - (y + 1)) + 33) = 12 * L + L * (4 * (x - (y + 1)) + 21) := by ring
    rw [he]
    omega
  · refine Exec.cast (Exec.seq he₁ (Exec.seq he₂ he₃)) rfl ?_
    simp only [hfinal]
    rfl

end IntegerMultBounds.MathlibTM2.Routing
