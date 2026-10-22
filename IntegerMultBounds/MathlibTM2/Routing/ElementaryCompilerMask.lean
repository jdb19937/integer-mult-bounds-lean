module

public import IntegerMultBounds.MathlibTM2.Routing.ElementaryCompilerHeaders

/-! Complete preparation of all six instruction words from binary inputs. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host

theorem elementaryCompilerPrepare_exec {T Q A n : ℕ} {P U : Type}
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
        (6 * rowBits.length + 12 * n + 44 * Lb + 190) + (10 * n + 9) ∧
      Exec body (elementaryCompilerPrepare rg) (mk v S) m
        (mk v' { S with R := elementaryCompilerReady S.R rg L target source rowBits triple }) := by
  obtain ⟨triple, v₁, m₁, hc, hv, hl, hu₁, hm₁, he₁⟩ := elementaryCompilerHeaders_exec body rg hrg
    L Lb B hn hB target source hne rowBits v S hwidth htarget hsource hrows hblock hblank
  let S₁ : Stacks T A := { S with R := elementaryCompilerHeaders S.R rg L target source rowBits triple }
  have hcoord : (S₁.R (rg (.coordinate .coord))).length =
      ((elementarySwapSpec target).coordinate source).val := by
    simp [S₁, elementaryCompilerHeaders, elementaryHeaderBank, elementaryCompilerHeader,
      elementaryCompilerCoordinates, elementaryCoordinateFinalBank, elementaryCoordinateInitialBank, hrg.eq_iff]
  have hhigh : (S₁.R (rg (.coordinate .high))).length =
      n - (((elementarySwapSpec target).coordinate source).val + 1) := by
    simp [S₁, elementaryCompilerHeaders, elementaryHeaderBank, elementaryCompilerHeader,
      elementaryCompilerCoordinates, elementaryCoordinateFinalBank, elementaryCoordinateInitialBank, hrg.eq_iff]
  have hmask : S₁.R (rg .mask) = [] := by
    simp [S₁, elementaryCompilerHeaders, elementaryHeaderBank, elementaryCompilerHeader,
      elementaryCompilerCoordinates, elementaryCoordinateFinalBank, elementaryCoordinateInitialBank, hrg.eq_iff,
      hblank .mask (by simp [elementaryCompilerInputs])]
  have hscratch (i : Fin 7) : S₁.R (rg (.coordinate (.scratch i))) = [] := by
    simp [S₁, elementaryCompilerHeaders, elementaryHeaderBank, elementaryCompilerHeader,
      elementaryCompilerCoordinates, elementaryCoordinateFinalBank, elementaryCoordinateInitialBank, hrg.eq_iff,
      hblank (.coordinate (.scratch i)) (by simp [elementaryCompilerInputs])]
  obtain ⟨v₂, m₂, hu₂, hm₂, he₂⟩ := elementarySourceMask_exec body target source
    (rg (.coordinate .coord)) (rg (.coordinate .high)) (rg .mask)
    (rg (.coordinate (.scratch 3))) (rg (.coordinate (.scratch 4)))
    (by simp [List.nodup_cons, hrg.eq_iff]) v₁ S₁ hcoord hhigh hmask (hscratch 3) (hscratch 4)
  refine ⟨triple, v₂, m₁ + m₂, hc, hv, hl, hu₂.trans hu₁, by omega, ?_⟩
  have he₂' : Exec body (sourceMaskProgram (rg (.coordinate .coord)) (rg (.coordinate .high)) (rg .mask)
      (rg (.coordinate (.scratch 3))) (rg (.coordinate (.scratch 4)))) (mk v₁ S₁) m₂
      (mk v₂ { S with R := elementaryCompilerReady S.R rg L target source rowBits triple }) := by
    simpa only [S₁, elementaryCompilerReady] using he₂
  exact Exec.seq he₁ he₂'

end IntegerMultBounds.MathlibTM2.Routing
