module

public import IntegerMultBounds.MathlibTM2.Routing.ElementaryCoordinateInitial
public import IntegerMultBounds.MathlibTM2.Routing.ElementaryCoordinateFinal

/-!
# Complete executed elementary coordinate-bank construction

Starting from three binary inputs, one fixed program builds every coordinate
and exponent tape required by header and source-mask generation. Only the seven
coordinate destinations change. All original inputs and shared scratch survive.
-/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host

variable {T Q A : ℕ} {P U : Type}

def elementaryCoordinateProgram (rg : ElementaryCoordinateReg → Fin T) : Pr P T Q A U :=
  .seq (elementaryCoordinateInitialProgram rg) (elementaryCoordinateFinalProgram rg)

/-- No unary coordinates or exponent tapes are assumed prepared. -/
theorem elementaryCoordinates_exec {n : ℕ} (body : P → Pr P T Q A U)
    (rg : ElementaryCoordinateReg → Fin T) (hrg : Function.Injective rg)
    (L : ℕ) (hn : n < 2 ^ L) (target source : Fin n) (hne : source ≠ target)
    (v : HS T Q A U) (S : Stacks T A)
    (hwidth : S.R (rg .width) = binSyms L n)
    (htarget : S.R (rg .target) = binSyms L target.val)
    (hsource : S.R (rg .source) = binSyms L source.val)
    (hblank : ∀ r : ElementaryCoordinateReg, r ≠ .width → r ≠ .target → r ≠ .source → S.R (rg r) = []) :
    ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧
      m ≤ 5 * (L * (4 * n + 33) + 2 * n + 31) + 6 * n + 6 * L + 15 ∧
      Exec body (elementaryCoordinateProgram rg) (mk v S) m
        (mk v' { S with R := elementaryCoordinateFinalBank (elementaryCoordinateInitialBank S.R rg target.val source.val) rg L target source }) := by
  have ht := target.isLt
  have hs := source.isLt
  obtain ⟨v₁, m₁, hu₁, hm₁, he₁⟩ := elementaryCoordinateInitial_exec body rg hrg L target.val source.val
    (by omega) (by omega) v S htarget hsource
    (hblank _ (by simp) (by simp) (by simp))
    (hblank _ (by simp) (by simp) (by simp))
    (hblank _ (by simp) (by simp) (by simp))
    (fun i => hblank _ (by simp) (by simp) (by simp))
  let S₁ : Stacks T A := { S with R := elementaryCoordinateInitialBank S.R rg target.val source.val }
  obtain ⟨v₂, m₂, hu₂, hm₂, he₂⟩ := elementaryCoordinateFinal_exec body rg hrg L hn target source hne v₁ S₁
    (by simp [S₁, elementaryCoordinateInitialBank, hrg.eq_iff, hwidth])
    (by simp [S₁, elementaryCoordinateInitialBank, hrg.eq_iff, htarget])
    (by simp [S₁, elementaryCoordinateInitialBank, hrg.eq_iff, hsource])
    (by simp [S₁, elementaryCoordinateInitialBank, hrg.eq_iff])
    (by simp [S₁, elementaryCoordinateInitialBank, hrg.eq_iff])
    (by simp [S₁, elementaryCoordinateInitialBank, hrg.eq_iff, hblank])
    (by simp [S₁, elementaryCoordinateInitialBank, hrg.eq_iff, hblank])
    (by simp [S₁, elementaryCoordinateInitialBank, hrg.eq_iff, hblank])
    (by simp [S₁, elementaryCoordinateInitialBank, hrg.eq_iff, hblank])
    (by intro i; simp [S₁, elementaryCoordinateInitialBank, hrg.eq_iff, hblank])
  have htCost : L * (4 * target.val + 11) + 2 * target.val + 6 ≤ L * (4 * n + 33) + 2 * n + 31 := by
    have h := Nat.mul_le_mul_left L (by omega : 4 * target.val + 11 ≤ 4 * n + 33)
    omega
  have hsCost : L * (4 * source.val + 11) + 2 * source.val + 6 ≤ L * (4 * n + 33) + 2 * n + 31 := by
    have h := Nat.mul_le_mul_left L (by omega : 4 * source.val + 11 ≤ 4 * n + 33)
    omega
  exact ⟨v₂, m₁ + m₂, hu₂.trans hu₁, by omega, Exec.seq he₁ he₂⟩

end IntegerMultBounds.MathlibTM2.Routing
