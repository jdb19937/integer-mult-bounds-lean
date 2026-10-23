module

public import IntegerMultBounds.MathlibTM2.Routing.BinaryMask

/-! Emit one generated descriptor row into a reusable accumulating output tape. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host

def binaryMaskEmitProgram {T Q A : ℕ} {P U : Type} (rg : BinaryMaskReg → Fin T) (out : Fin T) : Pr P T Q A U :=
  .seq (binaryMaskProgram rg) (.seq (moveR (rg .dst) (rg (.scratch 0)) id) (moveR (rg (.scratch 0)) out id))

theorem binaryMaskEmit_exec {T Q A : ℕ} {P U : Type}
    (body : P → Pr P T Q A U) (rg : BinaryMaskReg → Fin T) (hrg : Function.Injective rg)
    (out : Fin T) (hout : ∀ r, out ≠ rg r) (L M : ℕ) (hM : M < 2 ^ L) (q : Fin M)
    (v : HS T Q A U) (S : Stacks T A)
    (hwidth : S.R (rg .width) = binSyms L M) (hsource : S.R (rg .source) = binSyms L q.val)
    (hlow : S.R (rg .low) = []) (hhigh : S.R (rg .high) = []) (hdst : S.R (rg .dst) = [])
    (hscratch : ∀ i, S.R (rg (.scratch i)) = []) :
    ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧
      m ≤ 2 * (L * (4 * M + 33) + 2 * M + 31) + 16 * M + 28 ∧
      Exec body (binaryMaskEmitProgram rg out) (mk v S) m
        (mk v' { S with R := Function.update S.R out (binSyms M (2 ^ q.val) ++ S.R out) }) := by
  obtain ⟨v₁, m₁, hu₁, hm₁, he₁⟩ := binaryMask_exec body rg hrg L M hM q v S
    hwidth hsource hlow hhigh hdst hscratch
  let word : List (Fin (A + 4)) := binSyms M (2 ^ q.val)
  let S₁ : Stacks T A := { S with R := Function.update S.R (rg .dst) word }
  obtain ⟨v₂, hu₂, he₂⟩ := moveR_exec body (rg .dst) (rg (.scratch 0)) (by simp [hrg.eq_iff]) id v₁ S₁
  have hdst₁ : S₁.R (rg .dst) = word := by simp [S₁]
  let S₂ : Stacks T A := { S with R := Function.update S.R (rg (.scratch 0)) word.reverse }
  have hbank₂ : movedR S₁.R (rg .dst) (rg (.scratch 0)) id (S₁.R (rg .dst)) = S₂.R := by
    funext j
    by_cases hj : j = rg .dst
    · subst j; simp [movedR, S₂, hrg.eq_iff, hdst]
    · by_cases hk : j = rg (.scratch 0)
      · subst j; simp [movedR, S₂, S₁, hrg.eq_iff, hscratch]
      · simp [movedR, S₂, S₁, hj, hk]
  rw [hbank₂, hdst₁] at he₂
  have he₂' : Exec body (moveR (rg .dst) (rg (.scratch 0)) id) (mk v₁ S₁) (2 * M + 2) (mk v₂ S₂) := by
    simpa only [word, length_binSyms] using he₂
  obtain ⟨v₃, hu₃, he₃⟩ := moveR_exec body (rg (.scratch 0)) out (hout _).symm id v₂ S₂
  have htmp₂ : S₂.R (rg (.scratch 0)) = word.reverse := by simp [S₂]
  have hfinal : movedR S₂.R (rg (.scratch 0)) out id (S₂.R (rg (.scratch 0))) =
      Function.update S.R out (word ++ S.R out) := by
    funext j
    by_cases hj : j = out
    · subst j; simp [movedR, S₂, hout]
    · by_cases hk : j = rg (.scratch 0)
      · subst j; simp [movedR, hscratch, (hout (.scratch 0)).symm]
      · simp [movedR, S₂, hj, hk]
  rw [hfinal, htmp₂, List.length_reverse] at he₃
  have he₃' : Exec body (moveR (rg (.scratch 0)) out id) (mk v₂ S₂) (2 * M + 2)
      (mk v₃ { S with R := Function.update S.R out (word ++ S.R out) }) := by
    simpa only [word, length_binSyms] using he₃
  exact ⟨v₃, m₁ + ((2 * M + 2) + (2 * M + 2)), hu₃.trans (hu₂.trans hu₁), by omega,
    Exec.seq he₁ (Exec.seq he₂' he₃')⟩

end IntegerMultBounds.MathlibTM2.Routing
