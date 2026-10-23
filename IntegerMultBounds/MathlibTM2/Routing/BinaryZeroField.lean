module

public import IntegerMultBounds.MathlibTM2.Routing.MetadataJob

/-! Generate a zero field from a binary width, clearing the temporary unary
counter. This removes the need for an input word whose length supplies the width. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2.Node (tick)

inductive BinaryZeroReg where
  | width | unary | dst | scratch (i : Fin 3)
  deriving DecidableEq

def binaryZeroFieldProgram {T Q A : ℕ} {P U : Type} (rg : BinaryZeroReg → Fin T) : Pr P T Q A U :=
  .seq (toUnary (rg .width) (rg .unary) (rg (.scratch 0)) (rg (.scratch 1)) (rg (.scratch 2)))
    (.seq (bzero (rg .unary) (rg .dst) (rg (.scratch 1))) (bclear (rg .unary)))

theorem binaryZeroField_exec {T Q A : ℕ} {P U : Type}
    (body : P → Pr P T Q A U) (rg : BinaryZeroReg → Fin T) (hrg : Function.Injective rg)
    (L n : ℕ) (hn : n < 2 ^ L) (v : HS T Q A U) (S : Stacks T A)
    (hwidth : S.R (rg .width) = binSyms L n) (hunary : S.R (rg .unary) = [])
    (hscratch : ∀ i, S.R (rg (.scratch i)) = []) :
    ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧
      m ≤ L * (4 * n + 11) + 8 * n + 12 ∧
      Exec body (binaryZeroFieldProgram rg) (mk v S) m
        (mk v' { S with R := Function.update S.R (rg .dst) (binSyms n 0 ++ S.R (rg .dst)) }) := by
  obtain ⟨v₁, m₁, hu₁, hm₁, he₁⟩ := toUnary_exec body (a := rg .width) (z := rg .unary)
    (w := rg (.scratch 0)) (t := rg (.scratch 1)) (t₂ := rg (.scratch 2))
    (by simp [List.nodup_cons, hrg.eq_iff]) hn v S hwidth
    (hscratch 0) (hscratch 1) (hscratch 2)
  rw [hunary, List.append_nil] at he₁
  let S₁ : Stacks T A := { S with R := Function.update S.R (rg .unary) (List.replicate n tick) }
  obtain ⟨v₂, hu₂, he₂⟩ := bzero_exec body (wR := rg .unary) (c := rg .dst) (t := rg (.scratch 1))
    (by simp [List.nodup_cons, hrg.eq_iff]) v₁ S₁
    (by simp [S₁, hrg.eq_iff, hscratch])
  have hunary₁ : S₁.R (rg .unary) = List.replicate n tick := by simp [S₁]
  have hdst₁ : S₁.R (rg .dst) = S.R (rg .dst) := by simp [S₁, hrg.eq_iff]
  rw [hunary₁, List.length_replicate, hdst₁] at he₂
  let S₂ : Stacks T A := { S₁ with R := Function.update S₁.R (rg .dst) (binSyms n 0 ++ S.R (rg .dst)) }
  obtain ⟨v₃, hu₃, _, he₃⟩ := bclear_exec body (rg .unary) v₂ S₂
  have hunary₂ : S₂.R (rg .unary) = List.replicate n tick := by simp [S₂, S₁, hrg.eq_iff]
  have hfinal : Function.update S₂.R (rg .unary) [] =
      Function.update S.R (rg .dst) (binSyms n 0 ++ S.R (rg .dst)) := by
    funext j
    by_cases hj : j = rg .unary
    · subst j; simp [hrg.eq_iff, hunary]
    · by_cases hk : j = rg .dst
      · subst j; simp [S₂, hrg.eq_iff]
      · simp [S₂, S₁, hj, hk]
  rw [hfinal, hunary₂, List.length_replicate] at he₃
  exact ⟨v₃, m₁ + ((4 * n + 4) + (2 * n + 2)), hu₃.trans (hu₂.trans hu₁), by omega,
    Exec.seq he₁ (Exec.seq he₂ he₃)⟩

end IntegerMultBounds.MathlibTM2.Routing
