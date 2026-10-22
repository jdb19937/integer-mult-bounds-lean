module

public import IntegerMultBounds.MathlibTM2.Routing.ElementaryCompilerBank

/-! Actual coordinate construction followed by header generation on one bank. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2.Node (tick)

/-- The header arithmetic reads generated coordinates, rather than prepared
exponent tapes. All original binary inputs and shared scratch are preserved. -/
theorem elementaryCompilerHeaders_exec {T Q A n : ℕ} {P U : Type}
    (body : P → Pr P T Q A U) (rg : ElementaryCompilerReg → Fin T) (hrg : Function.Injective rg)
    (L Lb B : ℕ) (hn : n < 2 ^ L) (hB : B < 2 ^ Lb) (target source : Fin n) (hne : source ≠ target)
    (rowBits : List Bool) (v : HS T Q A U) (S : Stacks T A)
    (hwidth : S.R (rg (.coordinate .width)) = binSyms L n)
    (htarget : S.R (rg (.coordinate .target)) = binSyms L target.val)
    (hsource : S.R (rg (.coordinate .source)) = binSyms L source.val)
    (hrows : S.R (rg .rows) = rowBits.map bitSymbol) (hblock : S.R (rg .block) = binSyms Lb B)
    (hblank : ∀ r, r ∉ elementaryCompilerInputs → S.R (rg r) = []) :
    ∃ (triple : List Bool) (v' : HS T Q A U) (m : ℕ),
      GrowingCounterData.Canonical triple ∧ Counter.value triple = 3 * B ∧ triple.length ≤ Lb + 2 ∧
      v'.user = v.user ∧
      m ≤ (5 * (L * (4 * n + 33) + 2 * n + 31) + 6 * n + 6 * L + 15) +
        (6 * rowBits.length + 12 * n + 44 * Lb + 190) ∧
      Exec body (.seq (elementaryCoordinateProgram (fun r => rg (.coordinate r)))
        (elementaryHeaderProgram (fun r => rg (elementaryCompilerHeader r)))) (mk v S) m
        (mk v' { S with R := elementaryCompilerHeaders S.R rg L target source rowBits triple }) := by
  have hcoord : Function.Injective (fun r => rg (.coordinate r)) :=
    fun _ _ h => ElementaryCompilerReg.coordinate.inj (hrg h)
  obtain ⟨v₁, m₁, hu₁, hm₁, he₁⟩ := elementaryCoordinates_exec body (fun r => rg (.coordinate r))
    hcoord L hn target source hne v S hwidth htarget hsource
    (by intro r hw ht hs; exact hblank _ (by simp [elementaryCompilerInputs, hw, ht, hs]))
  let S₁ : Stacks T A := { S with R := elementaryCompilerCoordinates S.R rg L target source }
  have hscratch (i : Fin 7) : S₁.R (rg (elementaryCompilerHeader (.scratch i))) = [] := by
    simp [S₁, elementaryCompilerCoordinates, elementaryCoordinateFinalBank,
      elementaryCoordinateInitialBank, elementaryCompilerHeader, hrg.eq_iff,
      hblank (.coordinate (.scratch i)) (by simp [elementaryCompilerInputs])]
  obtain ⟨triple, v₂, m₂, hc, hv, hl, hu₂, hm₂, he₂⟩ := elementaryHeader_exec body
    (fun r => rg (elementaryCompilerHeader r)) (hrg.comp elementaryCompilerHeader_injective)
    rowBits Lb B hB v₁ S₁
    (by simp [S₁, elementaryCompilerCoordinates, elementaryCoordinateFinalBank,
      elementaryCoordinateInitialBank, elementaryCompilerHeader, hrg.eq_iff, hrows])
    (by simp [S₁, elementaryCompilerCoordinates, elementaryCoordinateFinalBank,
      elementaryCoordinateInitialBank, elementaryCompilerHeader, hrg.eq_iff, hblock])
    (by intro i; simp [S₁, elementaryCompilerCoordinates, elementaryCoordinateFinalBank,
      elementaryCoordinateInitialBank, elementaryCompilerHeader, hrg.eq_iff,
      hblank (.header i) (by simp [elementaryCompilerInputs])]) hscratch
  have heRow : (S₁.R (rg (elementaryCompilerHeader .rowExp))).length =
      n - (target.val + (elementarySwapSpec target).w) := by
    simp [S₁, elementaryCompilerCoordinates, elementaryCoordinateFinalBank,
      elementaryCoordinateInitialBank, elementaryCompilerHeader, hrg.eq_iff]
  have heGap : (S₁.R (rg (elementaryCompilerHeader .gapExp))).length = target.val - 1 := by
    simp [S₁, elementaryCompilerCoordinates, elementaryCoordinateFinalBank,
      elementaryCoordinateInitialBank, elementaryCompilerHeader, hrg.eq_iff]
  have hgate : (S₁.R (rg (elementaryCompilerHeader .target))).head?.isSome = decide (target.val ≠ 0) := by
    have hw : S₁.R (rg (elementaryCompilerHeader .target)) = List.replicate target.val tick := by
      simp [S₁, elementaryCompilerCoordinates, elementaryCoordinateFinalBank,
        elementaryCoordinateInitialBank, elementaryCompilerHeader, hrg.eq_iff]
    rw [hw]
    cases target.val <;> simp
  have hwords : elementaryHeaderWords rowBits (S₁.R (rg (elementaryCompilerHeader .rowExp))).length
      (S₁.R (rg (elementaryCompilerHeader .gapExp))).length triple
      (S₁.R (rg (elementaryCompilerHeader .target))).head?.isSome = elementaryCompilerWords rowBits triple target := by
    rw [heRow, heGap, hgate]
    rfl
  rw [heRow, heGap] at hm₂
  have hr := Nat.sub_le n (target.val + (elementarySwapSpec target).w)
  have hg : target.val - 1 ≤ n := by have ht := target.isLt; omega
  refine ⟨triple, v₂, m₁ + m₂, hc, hv, hl, hu₂.trans hu₁, by omega, ?_⟩
  have he₂' : Exec body (elementaryHeaderProgram (fun r => rg (elementaryCompilerHeader r)))
      (mk v₁ S₁) m₂ (mk v₂ { S with R := elementaryCompilerHeaders S.R rg L target source rowBits triple }) := by
    rw [hwords] at he₂
    simpa only [S₁, elementaryCompilerHeaders] using he₂
  exact Exec.seq he₁ he₂'

end IntegerMultBounds.MathlibTM2.Routing
