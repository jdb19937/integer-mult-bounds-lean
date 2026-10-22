module

public import IntegerMultBounds.MathlibTM2.Routing.ElementaryCoordinateBank

/-! Execute the initial target, source and gap coordinate-bank construction. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2.Node (tick)

/-- Both binary coordinates are preserved; the unary gap is the saturating
predecessor of the target. The same scratch bank is restored between phases. -/
theorem elementaryCoordinateInitial_exec {T Q A : ℕ} {P U : Type}
    (body : P → Pr P T Q A U) (rg : ElementaryCoordinateReg → Fin T) (hrg : Function.Injective rg)
    (L target source : ℕ) (htarget : target < 2 ^ L) (hsource : source < 2 ^ L)
    (v : HS T Q A U) (S : Stacks T A)
    (htargetBin : S.R (rg .target) = binSyms L target)
    (hsourceBin : S.R (rg .source) = binSyms L source)
    (htarget0 : S.R (rg .targetUnary) = []) (hsource0 : S.R (rg .sourceUnary) = [])
    (hgap0 : S.R (rg .gap) = []) (hscratch : ∀ i, S.R (rg (.scratch i)) = []) :
    ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧
      m ≤ (L * (4 * target + 11) + 2 * target + 6) +
        (L * (4 * source + 11) + 2 * source + 6) + (6 * target + 7) ∧
      Exec body (elementaryCoordinateInitialProgram rg) (mk v S) m
        (mk v' { S with R := elementaryCoordinateInitialBank S.R rg target source }) := by
  obtain ⟨v₁, m₁, hu₁, hm₁, he₁⟩ := toUnary_exec body (a := rg .target) (z := rg .targetUnary)
    (w := rg (.scratch 2)) (t := rg (.scratch 3)) (t₂ := rg (.scratch 4))
    (by simp [List.nodup_cons, hrg.eq_iff]) htarget v S htargetBin (hscratch 2) (hscratch 3) (hscratch 4)
  rw [htarget0, List.append_nil] at he₁
  let S₁ : Stacks T A := { S with R := Function.update S.R (rg .targetUnary) (List.replicate target tick) }
  obtain ⟨v₂, m₂, hu₂, hm₂, he₂⟩ := toUnary_exec body (a := rg .source) (z := rg .sourceUnary)
    (w := rg (.scratch 2)) (t := rg (.scratch 3)) (t₂ := rg (.scratch 4))
    (by simp [List.nodup_cons, hrg.eq_iff]) hsource v₁ S₁
    (by simp [S₁, hrg.eq_iff, hsourceBin])
    (by simp [S₁, hrg.eq_iff, hscratch])
    (by simp [S₁, hrg.eq_iff, hscratch])
    (by simp [S₁, hrg.eq_iff, hscratch])
  have hsource₁ : S₁.R (rg .sourceUnary) = [] := by simp [S₁, hrg.eq_iff, hsource0]
  rw [hsource₁, List.append_nil] at he₂
  let S₂ : Stacks T A := { S₁ with R := Function.update S₁.R (rg .sourceUnary) (List.replicate source tick) }
  have htarget₂ : S₂.R (rg .targetUnary) = List.replicate target tick := by simp [S₂, S₁, hrg.eq_iff]
  obtain ⟨v₃, hu₃, he₃⟩ := unaryPredecessor_exec body (rg .targetUnary) (rg .gap)
    (rg (.scratch 3)) (rg (.scratch 4)) (by simp [List.nodup_cons, hrg.eq_iff]) v₂ S₂
    (by simp [S₂, S₁, hrg.eq_iff, hgap0])
    (by simp [S₂, S₁, hrg.eq_iff, hscratch])
    (by simp [S₂, S₁, hrg.eq_iff, hscratch])
  have he₃' : Exec body (unaryPredecessorProgram (rg .targetUnary) (rg .gap)
      (rg (.scratch 3)) (rg (.scratch 4))) (mk v₂ S₂) (6 * target + 7)
      (mk v₃ { S with R := elementaryCoordinateInitialBank S.R rg target source }) := by
    simpa [S₂, S₁, hrg.eq_iff, elementaryCoordinateInitialBank] using he₃
  refine ⟨v₃, m₁ + (m₂ + (6 * target + 7)), hu₃.trans (hu₂.trans hu₁), by omega, ?_⟩
  exact Exec.seq he₁ (Exec.seq he₂ he₃')

end IntegerMultBounds.MathlibTM2.Routing
