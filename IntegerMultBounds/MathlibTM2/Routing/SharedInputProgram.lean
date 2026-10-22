module

public import IntegerMultBounds.MathlibTM2.Routing.SharedInputExec

/-! Executed shared-input preparation and cleanup around a stream-only router. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host

def sharedInputRoutingProgram {T Q A : ℕ} {P U : Type}
    (rg : SharedInputReg → Fin T) (route : Pr P T Q A U) : Pr P T Q A U :=
  .seq (sharedInputProgram rg) (.seq route (metadataClean (sharedInputPrivate rg)))

/-- A restored router can borrow the generated shared inputs. Both preparation
and cleanup are charged, and the final frame refers to the original bank. -/
theorem sharedInputRouting_exec {T Q A : ℕ} {P U : Type}
    (body : P → Pr P T Q A U) (rg : SharedInputReg → Fin T) (hrg : Function.Injective rg)
    (route : Pr P T Q A U) (L n rows : ℕ) (hn : n < 2 ^ L) (hn0 : 0 < n)
    (rowBits : List Bool) (hrowValue : Counter.value rowBits = rows)
    (v : HS T Q A U) (S : Stacks T A) (hwidth : S.R (rg .width) = binSyms L n)
    (hrows : S.R (rg .rows) = rowBits.map bitSymbol)
    (hfield : S.R (rg .field) = []) (hrecords : S.R (rg .records) = []) (hmask : S.R (rg .mask) = [])
    (hscratch : ∀ i, S.R (rg (.scratch i)) = [])
    (str : Fin T) (out : List (Fin (A + 4))) (hstr : str ∉ sharedInputPrivate rg) (cost : ℝ)
    (hroute : ∀ w : HS T Q A U, ∃ (w' : HS T Q A U) (m : ℕ), w'.user = w.user ∧ (m : ℝ) ≤ cost ∧
      Exec body route (mk w { S with R := sharedInputBank S.R rg n rows rowBits.length }) m
        (mk w' { S with R := Function.update (sharedInputBank S.R rg n rows rowBits.length) str out })) :
    ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧
      (m : ℝ) ≤ (L * (4 * n + 11) + 22 * n + 6 * rowBits.length + 46 : ℕ) + cost +
        (6 * n + 2 * rowBits.length + 7 : ℕ) ∧
      Exec body (sharedInputRoutingProgram rg route) (mk v S) m
        (mk v' { S with R := Function.update S.R str out }) := by
  obtain ⟨v₁, m₁, hu₁, hm₁, he₁⟩ := sharedInput_exec body rg hrg L n rows hn hn0
    rowBits hrowValue v S hwidth hrows hfield hrecords hmask hscratch
  obtain ⟨v₂, m₂, hu₂, hm₂, he₂⟩ := hroute v₁
  let bank := sharedInputBank S.R rg n rows rowBits.length
  let S₂ : Stacks T A := { S with R := Function.update bank str out }
  have hkeys : (sharedInputPrivate rg).Nodup := by
    simp [sharedInputPrivate, List.nodup_cons, hrg.eq_iff]
  obtain ⟨v₃, hu₃, he₃⟩ := metadataClean_exec body (sharedInputPrivate rg) hkeys v₂ S₂
  have hcost : metadataCleanCost S₂.R (sharedInputPrivate rg) = 6 * n + 2 * rowBits.length + 7 := by
    trans metadataCleanCost bank (sharedInputPrivate rg)
    · apply metadataCleanCost_congr
      intro j hj
      have hne : j ≠ str := by
        intro he
        subst j
        exact hstr hj
      exact Function.update_of_ne hne _ _
    · exact sharedInput_cleanCost S.R rg hrg n rows rowBits.length
  have hfinal : metadataCleared S₂.R (sharedInputPrivate rg) = Function.update S.R str out :=
    sharedInput_restore S.R rg hrg n rows rowBits.length str out hstr hrecords hfield hmask
  rw [hcost, hfinal] at he₃
  refine ⟨v₃, m₁ + (m₂ + (6 * n + 2 * rowBits.length + 7)),
    hu₃.trans (hu₂.trans hu₁), ?_, Exec.seq he₁ (Exec.seq he₂ he₃)⟩
  have hm₁' : (m₁ : ℝ) ≤ (L * (4 * n + 11) + 22 * n + 6 * rowBits.length + 46 : ℕ) := by
    exact_mod_cast hm₁
  push_cast
  push_cast at hm₁'
  linarith only [hm₁', hm₂]

end IntegerMultBounds.MathlibTM2.Routing
