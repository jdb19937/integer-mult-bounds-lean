module

public import IntegerMultBounds.MathlibTM2.Routing.ElementaryHeaderBank

/-! Actual generation of all five elementary headers on one fixed tape bank. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host

variable {T Q A : ℕ} {P U : Type}

/-- Every phase executes; only the five destinations change. Exponent tapes and
binary inputs are restored, and the seven scratch tapes end empty. -/
theorem elementaryHeader_exec (body : P → Pr P T Q A U)
    (rg : ElementaryHeaderReg → Fin T) (hrg : Function.Injective rg)
    (rowBits : List Bool) (L B : ℕ) (hB : B < 2 ^ L)
    (v : HS T Q A U) (S : Stacks T A)
    (hrows : S.R (rg .rows) = rowBits.map bitSymbol)
    (hblock : S.R (rg .block) = binSyms L B)
    (hheaders : ∀ i, S.R (rg (.header i)) = [])
    (hscratch : ∀ i, S.R (rg (.scratch i)) = []) :
    ∃ (triple : List Bool) (v' : HS T Q A U) (m : ℕ),
      GrowingCounterData.Canonical triple ∧ Counter.value triple = 3 * B ∧
      triple.length ≤ L + 2 ∧ v'.user = v.user ∧
      m ≤ 6 * (rowBits.length + (S.R (rg .rowExp)).length) +
        6 * (S.R (rg .gapExp)).length + 44 * L + 190 ∧
      Exec body (elementaryHeaderProgram rg) (mk v S) m
        (mk v' { S with R := elementaryHeaderBank S.R rg (elementaryHeaderWords rowBits (S.R (rg .rowExp)).length (S.R (rg .gapExp)).length triple (S.R (rg .target)).head?.isSome) }) := by
  let rowWord := (List.replicate (S.R (rg .rowExp)).length false ++ rowBits).map (bitSymbol (a := A))
  let gapWord := (binaryPowerBits (S.R (rg .gapExp)).length).map (bitSymbol (a := A))
  let S₁ : Stacks T A := { S with R := Function.update S.R (rg (.header 0)) rowWord }
  obtain ⟨v₁, hu₁, he₁⟩ := binaryScale_exec body (rg .rowExp) (rg .rows) (rg (.header 0))
    (rg (.scratch 1)) (rg (.scratch 2))
    (by simp [List.nodup_cons, hrg.eq_iff]) v S (hheaders 0) (hscratch 1) (hscratch 2)
  have he₁' : Exec body (binaryScaleProgram (rg .rowExp) (rg .rows) (rg (.header 0))
      (rg (.scratch 1)) (rg (.scratch 2))) (mk v S)
      (6 * (rowBits.length + (S.R (rg .rowExp)).length) + 12) (mk v₁ S₁) := by
    simpa only [hrows, List.length_map, List.map_append, List.map_replicate, S₁, rowWord] using he₁
  let S₂ : Stacks T A := { S₁ with R := Function.update S₁.R (rg (.header 1)) gapWord }
  obtain ⟨v₂, hu₂, he₂⟩ := binaryPower_exec body (rg .gapExp) (rg (.header 1))
    (rg (.scratch 1)) (rg (.scratch 2)) (by simp [List.nodup_cons, hrg.eq_iff]) v₁ S₁
    (by simp [S₁, hrg.eq_iff, hheaders]) (by simp [S₁, hrg.eq_iff, hscratch])
    (by simp [S₁, hrg.eq_iff, hscratch])
  have he₂' : Exec body (binaryPowerProgram (rg .gapExp) (rg (.header 1))
      (rg (.scratch 1)) (rg (.scratch 2))) (mk v₁ S₁)
      (6 * (S.R (rg .gapExp)).length + 7) (mk v₂ S₂) := by
    simpa only [S₁, Function.update_of_ne (by simp [hrg.eq_iff] : rg .gapExp ≠ rg (.header 0)),
      S₂, gapWord] using he₂
  obtain ⟨triple, v₃, m₃, hcanonical, hvalue, hlength, hu₃, hm₃, he₃⟩ := binaryTriple_exec body
    (rg .block) (rg (.header 2)) (rg (.scratch 0)) (rg (.scratch 1)) (rg (.scratch 2))
    (rg (.scratch 3)) (rg (.scratch 4)) (rg (.scratch 5)) (rg (.scratch 6))
    (by simp [List.nodup_cons, hrg.eq_iff]) (by simp [hrg.eq_iff]) (by simp [hrg.eq_iff])
    L B hB v₂ S₂
    (by simp [S₂, S₁, hrg.eq_iff, hblock])
    (by simp [S₂, S₁, hrg.eq_iff, hscratch])
    (by simp [S₂, S₁, hrg.eq_iff, hheaders])
    (by simp [S₂, S₁, hrg.eq_iff, hscratch])
    (by simp [S₂, S₁, hrg.eq_iff, hscratch])
    (by simp [S₂, S₁, hrg.eq_iff, hscratch])
    (by simp [S₂, S₁, hrg.eq_iff, hscratch])
    (by simp [S₂, S₁, hrg.eq_iff, hscratch])
  let S₃ : Stacks T A := { S₂ with R := Function.update S₂.R (rg (.header 2)) (triple.map bitSymbol) }
  let widthWord := (binaryNonemptyBits (S.R (rg .target)).head?.isSome).map (bitSymbol (a := A))
  let S₄ : Stacks T A := { S₃ with R := Function.update S₃.R (rg (.header 3)) widthWord }
  obtain ⟨v₄, hu₄, he₄⟩ := binaryNonempty_exec body (rg .target) (rg (.header 3)) v₃ S₃
    (by simp [S₃, S₂, S₁, hrg.eq_iff, hheaders])
  have he₄' : Exec body (binaryNonemptyProgram (rg .target) (rg (.header 3))) (mk v₃ S₃) 3 (mk v₄ S₄) := by
    simpa only [S₃, S₂, S₁, Function.update_of_ne (by simp [hrg.eq_iff] : rg .target ≠ rg (.header 0)),
      Function.update_of_ne (by simp [hrg.eq_iff] : rg .target ≠ rg (.header 1)),
      Function.update_of_ne (by simp [hrg.eq_iff] : rg .target ≠ rg (.header 2)), widthWord, S₄] using he₄
  obtain ⟨v₅, hu₅, he₅⟩ := binaryNonempty_exec body (rg .target) (rg (.header 4)) v₄ S₄
    (by simp [S₄, S₃, S₂, S₁, hrg.eq_iff, hheaders])
  have he₅' : Exec body (binaryNonemptyProgram (rg .target) (rg (.header 4))) (mk v₄ S₄) 3
      (mk v₅ { S with R := elementaryHeaderBank S.R rg (elementaryHeaderWords rowBits (S.R (rg .rowExp)).length (S.R (rg .gapExp)).length triple (S.R (rg .target)).head?.isSome) }) := by
    simpa [S₄, S₃, S₂, S₁, hrg.eq_iff, elementaryHeaderBank,
      elementaryHeaderWords, rowWord, gapWord, widthWord] using he₅
  refine ⟨triple, v₅, (6 * (rowBits.length + (S.R (rg .rowExp)).length) + 12) +
    ((6 * (S.R (rg .gapExp)).length + 7) + (m₃ + (3 + 3))), hcanonical, hvalue, hlength,
    hu₅.trans (hu₄.trans (hu₃.trans (hu₂.trans hu₁))), by omega, ?_⟩
  exact Exec.seq he₁' (Exec.seq he₂' (Exec.seq he₃ (Exec.seq he₄' he₅')))

end IntegerMultBounds.MathlibTM2.Routing
