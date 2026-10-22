module

public import IntegerMultBounds.MathlibTM2.Routing.BinaryTriple
public import IntegerMultBounds.MathlibTM2.Routing.BinaryScale

/-! The payload header for interval exchanges is three times the record width,
shifted by the lower interval offset. Both operands remain tape data. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host

inductive TripleScaleReg where
  | exponent | src | dst | triple | scratch (i : Fin 7)
  deriving DecidableEq

def binaryTripleScaleProgram {T Q A : ℕ} {P U : Type}
    (rg : TripleScaleReg → Fin T) : Pr P T Q A U :=
  .seq (binaryTripleProgram (rg .src) (rg .triple) (rg (.scratch 0)) (rg (.scratch 1))
    (rg (.scratch 2)) (rg (.scratch 3)) (rg (.scratch 4)) (rg (.scratch 5)) (rg (.scratch 6)))
    (.seq (binaryScaleProgram (rg .exponent) (rg .triple) (rg .dst) (rg (.scratch 1)) (rg (.scratch 2)))
      (bclear (rg .triple)))

/-- Generate the canonical shifted payload header and clear the intermediate
triple. Every input and scratch tape is restored. -/
theorem binaryTripleScale_exec {T Q A : ℕ} {P U : Type}
    (body : P → Pr P T Q A U) (rg : TripleScaleReg → Fin T) (hrg : Function.Injective rg)
    (L x : ℕ) (hx : x < 2 ^ L) (hx0 : 0 < x)
    (v : HS T Q A U) (S : Stacks T A) (hsrc : S.R (rg .src) = binSyms L x)
    (hdst : S.R (rg .dst) = []) (htriple : S.R (rg .triple) = [])
    (hscratch : ∀ i, S.R (rg (.scratch i)) = []) :
    ∃ (bs : List Bool) (v' : HS T Q A U) (m : ℕ),
      GrowingCounterData.Canonical bs ∧
      Counter.value bs = 2 ^ (S.R (rg .exponent)).length * (3 * x) ∧
      bs.length ≤ (S.R (rg .exponent)).length + L + 2 ∧ v'.user = v.user ∧
      m ≤ 52 * L + 6 * (S.R (rg .exponent)).length + 195 ∧
      Exec body (binaryTripleScaleProgram rg) (mk v S) m
        (mk v' { S with R := Function.update S.R (rg .dst) (bs.map bitSymbol) }) := by
  obtain ⟨triple, v₁, m₁, hc, hv, hl, hu₁, hm₁, he₁⟩ := binaryTriple_exec body
    (rg .src) (rg .triple) (rg (.scratch 0)) (rg (.scratch 1)) (rg (.scratch 2))
    (rg (.scratch 3)) (rg (.scratch 4)) (rg (.scratch 5)) (rg (.scratch 6))
    (by simp [List.nodup_cons, hrg.eq_iff]) (by simp [hrg.eq_iff]) (by simp [hrg.eq_iff])
    L x hx v S hsrc (hscratch 0) htriple (hscratch 1) (hscratch 2) (hscratch 3) (hscratch 4) (hscratch 5)
  let S₁ : Stacks T A := { S with R := Function.update S.R (rg .triple) (triple.map bitSymbol) }
  have htriple₁ : S₁.R (rg .triple) = triple.map bitSymbol := by simp [S₁]
  have hexp₁ : S₁.R (rg .exponent) = S.R (rg .exponent) := by simp [S₁, hrg.eq_iff]
  obtain ⟨v₂, hu₂, he₂⟩ := binaryScale_exec body (rg .exponent) (rg .triple) (rg .dst)
    (rg (.scratch 1)) (rg (.scratch 2)) (by simp [List.nodup_cons, hrg.eq_iff]) v₁ S₁
    (by simp [S₁, hrg.eq_iff, hdst]) (by simp [S₁, hrg.eq_iff, hscratch]) (by simp [S₁, hrg.eq_iff, hscratch])
  let bs := List.replicate (S.R (rg .exponent)).length false ++ triple
  have hword : List.replicate (S₁.R (rg .exponent)).length (bitSymbol (a := A) false) ++ S₁.R (rg .triple) =
      bs.map bitSymbol := by simp [bs, hexp₁, htriple₁]
  let S₂ : Stacks T A := { S₁ with R := Function.update S₁.R (rg .dst) (bs.map bitSymbol) }
  have he₂' : Exec body (binaryScaleProgram (rg .exponent) (rg .triple) (rg .dst) (rg (.scratch 1)) (rg (.scratch 2)))
      (mk v₁ S₁) (6 * (triple.length + (S.R (rg .exponent)).length) + 12) (mk v₂ S₂) := by
    rw [hword] at he₂
    simpa only [htriple₁, hexp₁, List.length_map] using he₂
  obtain ⟨v₃, hu₃, _, he₃⟩ := bclear_exec body (rg .triple) v₂ S₂
  have ht₂ : S₂.R (rg .triple) = triple.map bitSymbol := by simp [S₂, S₁, hrg.eq_iff]
  have hfinal : Function.update S₂.R (rg .triple) [] = Function.update S.R (rg .dst) (bs.map bitSymbol) := by
    funext j
    by_cases hj : j = rg .triple
    · subst j; simp [hrg.eq_iff, htriple]
    · by_cases hd : j = rg .dst
      · subst j; simp [S₂, hj]
      · simp [S₂, S₁, hj, hd]
  rw [ht₂, List.length_map, hfinal] at he₃
  have hne : triple ≠ [] := by intro he; simp [he, Counter.value] at hv; omega
  refine ⟨bs, v₃, m₁ + ((6 * (triple.length + (S.R (rg .exponent)).length) + 12) + (2 * triple.length + 2)),
    binaryScale_canonical _ triple hc hne, ?_, ?_, hu₃.trans (hu₂.trans hu₁), by omega,
    Exec.seq he₁ (Exec.seq he₂' he₃)⟩
  · exact (binaryScale_value _ triple).trans (by rw [hv])
  · simp only [bs, List.length_append, List.length_replicate]
    omega

end IntegerMultBounds.MathlibTM2.Routing
