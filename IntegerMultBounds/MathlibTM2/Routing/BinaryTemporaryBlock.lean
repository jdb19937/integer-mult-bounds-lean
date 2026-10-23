module

public import IntegerMultBounds.MathlibTM2.Routing.PaddedOnesBlock
public import IntegerMultBounds.MathlibTM2.Routing.UnaryDifference

/-! Generate a complete temporary-mask block from binary segment/run widths.
The unary padding and all arithmetic intermediates are constructed and erased. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2.Layer.CompactMasks
open IntegerMultBounds.MathlibTM2.Node (tick)

inductive TemporaryBlockReg where
  | width | run | bin | high | dst | work | scratch (i : Fin 3)
  deriving DecidableEq

def binaryTemporaryBlockProgram {T Q A : ℕ} {P U : Type} (rg : TemporaryBlockReg → Fin T) : Pr P T Q A U :=
  .seq (unaryDifferenceProgram (rg .width) (rg .run) (rg .bin) (rg .high) (rg .work)
    (rg (.scratch 0)) (rg (.scratch 1)) (rg (.scratch 2)) (rg (.scratch 2)))
    (.seq (paddedOnesBlockProgram (rg .run) (rg .high) (rg .dst) (rg .work) (rg (.scratch 0)) (rg (.scratch 1)))
      (bclear (rg .high)))

def binaryTemporaryBlockCost (L K G : ℕ) :=
  (L * (4 * (K - G) + 21) + 2 * (K - G) + 16) +
    (L * (4 * G + 11) + 6 * G + 6 * (K - G) + 14) + (2 * (K - G) + 2)

theorem binaryTemporaryBlock_exec {T Q A : ℕ} {P U : Type}
    (body : P → Pr P T Q A U) (rg : TemporaryBlockReg → Fin T) (hrg : Function.Injective rg)
    (L K G : ℕ) (hK : K < 2 ^ L) (hGK : G ≤ K) (v : HS T Q A U) (S : Stacks T A)
    (hwidth : S.R (rg .width) = binSyms L K) (hrun : S.R (rg .run) = binSyms L G)
    (hblank : ∀ r, r ≠ .width → r ≠ .run → S.R (rg r) = []) :
    ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧ m ≤ binaryTemporaryBlockCost L K G ∧
      Exec body (binaryTemporaryBlockProgram rg) (mk v S) m
        (mk v' { S with R := Function.update S.R (rg .dst) (binSyms K (maskVal G id)) }) := by
  obtain ⟨v₁, m₁, hu₁, hm₁, he₁⟩ := unaryDifference_exec body (rg .width) (rg .run) (rg .bin)
    (rg .high) (rg .work) (rg (.scratch 0)) (rg (.scratch 1)) (rg (.scratch 2)) (rg (.scratch 2))
    (by simp [List.nodup_cons, hrg.eq_iff]) (by simp [hrg.eq_iff]) (by simp [hrg.eq_iff])
    L K G hK hGK v S hwidth hrun
    (hblank .bin (by simp) (by simp)) (hblank .high (by simp) (by simp))
    (hblank .work (by simp) (by simp)) (hblank (.scratch 0) (by simp) (by simp))
    (hblank (.scratch 1) (by simp) (by simp)) (hblank (.scratch 2) (by simp) (by simp))
  let S₁ : Stacks T A := { S with R := Function.update S.R (rg .high) (List.replicate (K - G) tick) }
  obtain ⟨v₂, m₂, hu₂, hm₂, he₂⟩ := paddedOnesBlock_exec body (rg .run) (rg .high) (rg .dst)
    (rg .work) (rg (.scratch 0)) (rg (.scratch 1)) (by simp [List.nodup_cons, hrg.eq_iff])
    L G (by omega) v₁ S₁ (by simp [S₁, hrg.eq_iff, hrun])
    (by simp [S₁, hrg.eq_iff, hblank .dst (by simp) (by simp)])
    (by simp [S₁, hrg.eq_iff, hblank .work (by simp) (by simp)])
    (by simp [S₁, hrg.eq_iff, hblank (.scratch 0) (by simp) (by simp)])
    (by simp [S₁, hrg.eq_iff, hblank (.scratch 1) (by simp) (by simp)])
  have hh₁ : S₁.R (rg .high) = List.replicate (K - G) tick := by simp [S₁]
  rw [hh₁, List.length_replicate] at he₂ hm₂
  rw [show G + (K - G) = K by omega] at he₂
  let S₂ : Stacks T A := { S₁ with R := Function.update S₁.R (rg .dst) (binSyms K (maskVal G id)) }
  obtain ⟨v₃, hu₃, _, he₃⟩ := bclear_exec body (rg .high) v₂ S₂
  have hh₂ : S₂.R (rg .high) = List.replicate (K - G) tick := by simp [S₂, S₁, hrg.eq_iff]
  have hf : Function.update S₂.R (rg .high) [] = Function.update S.R (rg .dst) (binSyms K (maskVal G id)) := by
    funext j
    by_cases hj : j = rg .high
    · subst j; simp [hrg.eq_iff, hblank .high (by simp) (by simp)]
    · by_cases hk : j = rg .dst
      · subst j; simp [S₂, hrg.eq_iff]
      · simp [S₂, S₁, hj, hk]
  rw [hf, hh₂, List.length_replicate] at he₃
  exact ⟨v₃, m₁ + (m₂ + (2 * (K - G) + 2)), hu₃.trans (hu₂.trans hu₁),
    by unfold binaryTemporaryBlockCost; omega, Exec.seq he₁ (Exec.seq he₂ he₃)⟩

end IntegerMultBounds.MathlibTM2.Routing
