module

public import IntegerMultBounds.MathlibTM2.Routing.ExchangeHeaderBank

/-! Actual generation of all five general interval-exchange headers. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host

variable {T Q A : ℕ} {P U : Type}

/-- Generate all five raw exchange headers, restoring the complete input and
scratch bank. The interval width is canonical binary input; exponent tapes
are unary inputs whose generation is a separate phase. -/
theorem exchangeHeader_exec (body : P → Pr P T Q A U)
    (bank : ExchangeHeaderReg → Fin T) (hbank : Function.Injective bank)
    (rowBits widthBits : List Bool) (L B : ℕ) (hB : B < 2 ^ L) (hB0 : 0 < B)
    (v : HS T Q A U) (S : Stacks T A)
    (hrows : S.R (bank (.base .rows)) = rowBits.map bitSymbol)
    (hblock : S.R (bank (.base .block)) = binSyms L B)
    (hwidth : S.R (bank (.base .target)) = widthBits.map bitSymbol)
    (hheaders : ∀ i, S.R (bank (.base (.header i))) = [])
    (hscratch : ∀ i, S.R (bank (.base (.scratch i))) = [])
    (htriple : S.R (bank .triple) = []) :
    ∃ (payload : List Bool) (v' : HS T Q A U) (m : ℕ),
      GrowingCounterData.Canonical payload ∧
      Counter.value payload = 2 ^ (S.R (bank .lowerExp)).length * (3 * B) ∧
      payload.length ≤ (S.R (bank .lowerExp)).length + L + 2 ∧ v'.user = v.user ∧
      m ≤ 6 * (rowBits.length + (S.R (bank (.base .rowExp))).length) +
        6 * (S.R (bank (.base .gapExp))).length + 52 * L +
        6 * (S.R (bank .lowerExp)).length + 12 * widthBits.length + 226 ∧
      Exec body (exchangeHeaderProgram bank) (mk v S) m
        (mk v' { S with R := elementaryHeaderBank S.R (fun r => bank (.base r)) (exchangeHeaderWords rowBits payload widthBits (S.R (bank (.base .rowExp))).length (S.R (bank (.base .gapExp))).length) }) := by
  let rg : ElementaryHeaderReg → Fin T := fun r => bank (.base r)
  have hrg : Function.Injective rg := hbank.comp (by intro i j h; exact ExchangeHeaderReg.base.inj h)
  change S.R (rg .rows) = rowBits.map bitSymbol at hrows
  change S.R (rg .block) = binSyms L B at hblock
  change S.R (rg .target) = widthBits.map bitSymbol at hwidth
  change ∀ i, S.R (rg (.header i)) = [] at hheaders
  change ∀ i, S.R (rg (.scratch i)) = [] at hscratch
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
  obtain ⟨payload, v₃, m₃, hcanonical, hvalue, hlength, hu₃, hm₃, he₃⟩ := binaryTripleScale_exec body
    (bank ∘ exchangeTripleReg) (hbank.comp exchangeTripleReg_injective) L B hB hB0 v₂ S₂
    (by simp [exchangeTripleReg, S₂, S₁, rg, hbank.eq_iff, show S.R (bank (.base .block)) = binSyms L B from hblock])
    (by simp [exchangeTripleReg, S₂, S₁, rg, hbank.eq_iff, show ∀ i, S.R (bank (.base (.header i))) = [] from hheaders])
    (by simp [exchangeTripleReg, S₂, S₁, rg, hbank.eq_iff, htriple])
    (by intro i; simp [exchangeTripleReg, S₂, S₁, rg, hbank.eq_iff, show ∀ i, S.R (bank (.base (.scratch i))) = [] from hscratch])
  have hlower : S₂.R (bank .lowerExp) = S.R (bank .lowerExp) := by
    simp [S₂, S₁, rg, hbank.eq_iff]
  change Counter.value payload = 2 ^ (S₂.R (bank .lowerExp)).length * (3 * B) at hvalue
  change payload.length ≤ (S₂.R (bank .lowerExp)).length + L + 2 at hlength
  change m₃ ≤ 52 * L + 6 * (S₂.R (bank .lowerExp)).length + 195 at hm₃
  rw [hlower] at hvalue hlength hm₃
  let S₃ : Stacks T A := { S₂ with R := Function.update S₂.R (rg (.header 2)) (payload.map bitSymbol) }
  let widthWord := widthBits.map (bitSymbol (a := A))
  let S₄ : Stacks T A := { S₃ with R := Function.update S₃.R (rg (.header 3)) widthWord }
  obtain ⟨v₄, hu₄, he₄⟩ := bcopy_exec body (a := rg .target) (c := rg (.header 3))
    (t₁ := rg (.scratch 1)) (t₂ := rg (.scratch 2)) (by simp [List.nodup_cons, hrg.eq_iff]) v₃ S₃
    (by simp [S₃, S₂, S₁, hrg.eq_iff, hscratch]) (by simp [S₃, S₂, S₁, hrg.eq_iff, hscratch])
  have he₄' : Exec body (bcopy (rg .target) (rg (.header 3)) (rg (.scratch 1)) (rg (.scratch 2)))
      (mk v₃ S₃) (6 * widthBits.length + 6) (mk v₄ S₄) := by
    simpa [S₃, S₂, S₁, hrg.eq_iff, hheaders, hwidth, widthWord] using he₄
  obtain ⟨v₅, hu₅, he₅⟩ := bcopy_exec body (a := rg .target) (c := rg (.header 4))
    (t₁ := rg (.scratch 1)) (t₂ := rg (.scratch 2)) (by simp [List.nodup_cons, hrg.eq_iff]) v₄ S₄
    (by simp [S₄, S₃, S₂, S₁, hrg.eq_iff, hscratch]) (by simp [S₄, S₃, S₂, S₁, hrg.eq_iff, hscratch])
  have he₅' : Exec body (bcopy (rg .target) (rg (.header 4)) (rg (.scratch 1)) (rg (.scratch 2)))
      (mk v₄ S₄) (6 * widthBits.length + 6)
      (mk v₅ { S with R := elementaryHeaderBank S.R rg (exchangeHeaderWords rowBits payload widthBits (S.R (rg .rowExp)).length (S.R (rg .gapExp)).length) }) := by
    simpa [S₄, S₃, S₂, S₁, hrg.eq_iff, elementaryHeaderBank, exchangeHeaderWords,
      rowWord, gapWord, widthWord, hheaders, hwidth] using he₅
  refine ⟨payload, v₅, (6 * (rowBits.length + (S.R (rg .rowExp)).length) + 12) +
    ((6 * (S.R (rg .gapExp)).length + 7) + (m₃ + ((6 * widthBits.length + 6) + (6 * widthBits.length + 6)))), hcanonical, hvalue, hlength,
    hu₅.trans (hu₄.trans (hu₃.trans (hu₂.trans hu₁))), by dsimp only [rg]; omega, ?_⟩
  exact Exec.seq he₁' (Exec.seq he₂' (Exec.seq he₃ (Exec.seq he₄' he₅')))

end IntegerMultBounds.MathlibTM2.Routing
