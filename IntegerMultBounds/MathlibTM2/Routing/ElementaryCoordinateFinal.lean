module

public import IntegerMultBounds.MathlibTM2.Routing.ElementaryCoordinateBank

/-! Execute the row exponent, renamed source and mask-padding coordinate stage. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2.Node (tick)

theorem elementaryCoordinateFinal_exec {T Q A n : ℕ} {P U : Type}
    (body : P → Pr P T Q A U) (rg : ElementaryCoordinateReg → Fin T) (hrg : Function.Injective rg)
    (L : ℕ) (hn : n < 2 ^ L) (target source : Fin n) (hne : source ≠ target)
    (v : HS T Q A U) (S : Stacks T A)
    (hwidth : S.R (rg .width) = binSyms L n)
    (htarget : S.R (rg .target) = binSyms L target.val)
    (hsource : S.R (rg .source) = binSyms L source.val)
    (htargetUnary : (S.R (rg .targetUnary)).length = target.val)
    (hsourceUnary : (S.R (rg .sourceUnary)).length = source.val)
    (hrow0 : S.R (rg .rowExp) = []) (hrenamed0 : S.R (rg .renamed) = [])
    (hcoord0 : S.R (rg .coord) = []) (hhigh0 : S.R (rg .high) = [])
    (hscratch : ∀ i, S.R (rg (.scratch i)) = []) :
    ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧
      m ≤ 3 * (L * (4 * n + 33) + 2 * n + 31) + 6 * L + 8 ∧
      Exec body (elementaryCoordinateFinalProgram rg) (mk v S) m
        (mk v' { S with R := elementaryCoordinateFinalBank S.R rg L target source }) := by
  let q := ((elementarySwapSpec target).coordinate source).val
  have hq : q < n := ((elementarySwapSpec target).coordinate source).isLt
  obtain ⟨v₁, m₁, hu₁, hm₁, he₁⟩ := elementaryRowExponent_exec body target (rg .targetUnary)
    (rg .width) (rg .target) (rg (.scratch 0)) (rg (.scratch 1)) (rg .rowExp) (rg (.scratch 2))
    (rg (.scratch 3)) (rg (.scratch 4)) (rg (.scratch 5)) (rg (.scratch 6))
    (by simp [List.nodup_cons, hrg.eq_iff]) (by simp [hrg.eq_iff]) (by simp [hrg.eq_iff])
    L hn v S htargetUnary hwidth htarget (hscratch 0) (hscratch 1) hrow0
    (hscratch 2) (hscratch 3) (hscratch 4) (hscratch 5)
  let S₁ : Stacks T A :=
    { S with R := Function.update S.R (rg .rowExp) (List.replicate (n - (target.val + (elementarySwapSpec target).w)) tick) }
  obtain ⟨v₂, hu₂, he₂⟩ := elementarySourceCoordinate_exec body target source hne
    (rg .sourceUnary) (rg .source) (rg .target) (rg .renamed) (rg (.scratch 3)) (rg (.scratch 4))
    (by simp [List.nodup_cons, hrg.eq_iff]) (by simp [List.nodup_cons, hrg.eq_iff]) L v₁ S₁
    (by simpa [S₁, hrg.eq_iff] using hsourceUnary)
    (by simp [S₁, hrg.eq_iff, hsource]) (by simp [S₁, hrg.eq_iff, htarget])
    (by simp [S₁, hrg.eq_iff, hrenamed0])
    (by simp [S₁, hrg.eq_iff, hscratch]) (by simp [S₁, hrg.eq_iff, hscratch])
  let S₂ : Stacks T A := { S₁ with R := Function.update S₁.R (rg .renamed) (binSyms L q) }
  obtain ⟨v₃, m₃, hu₃, hm₃, he₃⟩ := toUnary_exec body (a := rg .renamed) (z := rg .coord)
    (w := rg (.scratch 2)) (t := rg (.scratch 3)) (t₂ := rg (.scratch 4))
    (by simp [List.nodup_cons, hrg.eq_iff]) (by omega : q < 2 ^ L) v₂ S₂
    (by simp [S₂])
    (by simp [S₂, S₁, hrg.eq_iff, hscratch])
    (by simp [S₂, S₁, hrg.eq_iff, hscratch])
    (by simp [S₂, S₁, hrg.eq_iff, hscratch])
  have hcoord₂ : S₂.R (rg .coord) = [] := by simp [S₂, S₁, hrg.eq_iff, hcoord0]
  rw [hcoord₂, List.append_nil] at he₃
  let S₃ : Stacks T A := { S₂ with R := Function.update S₂.R (rg .coord) (List.replicate q tick) }
  obtain ⟨v₄, m₄, hu₄, hm₄, he₄⟩ := unaryComplement_exec body (rg .width) (rg .renamed)
    (rg (.scratch 0)) (rg (.scratch 1)) (rg .high) (rg (.scratch 2)) (rg (.scratch 3))
    (rg (.scratch 4)) (rg (.scratch 5)) (rg (.scratch 6))
    (by simp [List.nodup_cons, hrg.eq_iff]) (by simp [hrg.eq_iff]) (by simp [hrg.eq_iff])
    L n q hn hq v₃ S₃
    (by simp [S₃, S₂, S₁, hrg.eq_iff, hwidth]) (by simp [S₃, S₂, hrg.eq_iff])
    (by simp [S₃, S₂, S₁, hrg.eq_iff, hscratch])
    (by simp [S₃, S₂, S₁, hrg.eq_iff, hscratch])
    (by simp [S₃, S₂, S₁, hrg.eq_iff, hhigh0])
    (by simp [S₃, S₂, S₁, hrg.eq_iff, hscratch])
    (by simp [S₃, S₂, S₁, hrg.eq_iff, hscratch])
    (by simp [S₃, S₂, S₁, hrg.eq_iff, hscratch])
    (by simp [S₃, S₂, S₁, hrg.eq_iff, hscratch])
  have hm₃' : m₃ ≤ L * (4 * n + 33) + 2 * n + 31 := by
    have h := Nat.mul_le_mul_left L (by omega : 4 * q + 11 ≤ 4 * n + 33)
    omega
  have hm₄' : m₄ ≤ L * (4 * n + 33) + 2 * n + 31 := by
    have hd := Nat.sub_le n (q + 1)
    have h := Nat.mul_le_mul_left L (by omega : 4 * (n - (q + 1)) + 33 ≤ 4 * n + 33)
    omega
  refine ⟨v₄, m₁ + ((6 * L + 8) + (m₃ + m₄)), hu₄.trans (hu₃.trans (hu₂.trans hu₁)), by omega, ?_⟩
  exact Exec.seq he₁ (Exec.seq he₂ (Exec.seq he₃ he₄))

end IntegerMultBounds.MathlibTM2.Routing
