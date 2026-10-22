module

public import IntegerMultBounds.MathlibTM2.Routing.ElementaryHeaderValues

/-!
# Fixed register layout for elementary header generation

All dimensions remain tape data. A single bank supplies three unary coordinates,
two binary inputs, five generated header words and seven reusable scratch tapes.
-/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host

inductive ElementaryHeaderReg where
  | rowExp | gapExp | target | rows | block
  | header (i : Fin 5)
  | scratch (i : Fin 7)
  deriving DecidableEq

def elementaryHeaderBank {T A : ℕ} (R : Fin T → List (Fin (A + 4)))
    (rg : ElementaryHeaderReg → Fin T) (words : Fin 5 → List Bool) : Fin T → List (Fin (A + 4)) :=
  Function.update (Function.update (Function.update (Function.update (Function.update R
    (rg (.header 0)) ((words 0).map bitSymbol)) (rg (.header 1)) ((words 1).map bitSymbol))
    (rg (.header 2)) ((words 2).map bitSymbol)) (rg (.header 3)) ((words 3).map bitSymbol))
    (rg (.header 4)) ((words 4).map bitSymbol)

/-- The generator has fixed code and tapes, independent of dimensions and values. -/
def elementaryHeaderProgram {T Q A : ℕ} {P U : Type} (rg : ElementaryHeaderReg → Fin T) : Pr P T Q A U :=
  .seq (binaryScaleProgram (rg .rowExp) (rg .rows) (rg (.header 0)) (rg (.scratch 1)) (rg (.scratch 2)))
    (.seq (binaryPowerProgram (rg .gapExp) (rg (.header 1)) (rg (.scratch 1)) (rg (.scratch 2)))
      (.seq (binaryTripleProgram (rg .block) (rg (.header 2)) (rg (.scratch 0)) (rg (.scratch 1))
        (rg (.scratch 2)) (rg (.scratch 3)) (rg (.scratch 4)) (rg (.scratch 5)) (rg (.scratch 6)))
        (.seq (binaryNonemptyProgram (rg .target) (rg (.header 3)))
          (binaryNonemptyProgram (rg .target) (rg (.header 4))))))

/-- The five generated words are exactly the three arithmetic forms and two
identical zero-or-one widths. The triple is supplied by its executed generator. -/
def elementaryHeaderWords (rowBits : List Bool) (rowExp gapExp : ℕ)
    (triple : List Bool) (live : Bool) : Fin 5 → List Bool :=
  ![List.replicate rowExp false ++ rowBits, binaryPowerBits gapExp, triple,
    binaryNonemptyBits live, binaryNonemptyBits live]

theorem elementaryHeaderWords_valid (rowBits : List Bool) (rowExp gapExp : ℕ)
    (triple : List Bool) (live : Bool) (rows B : ℕ)
    (hrow : GrowingCounterData.Canonical rowBits) (hne : rowBits ≠ [])
    (hrows : Counter.value rowBits = rows) (htriple : GrowingCounterData.Canonical triple)
    (hB : Counter.value triple = 3 * B) :
    (∀ i, GrowingCounterData.Canonical (elementaryHeaderWords rowBits rowExp gapExp triple live i)) ∧
    (∀ i, Counter.value (elementaryHeaderWords rowBits rowExp gapExp triple live i) =
      ![2 ^ rowExp * rows, 2 ^ gapExp, 3 * B, live.toNat, live.toNat] i) := by
  constructor
  · intro i
    fin_cases i
    · exact binaryScale_canonical rowExp rowBits hrow hne
    · exact binaryPowerBits_canonical gapExp
    · exact htriple
    · exact binaryNonemptyBits_canonical live
    · exact binaryNonemptyBits_canonical live
  · intro i
    fin_cases i
    · exact (binaryScale_value rowExp rowBits).trans (by rw [hrows]; rfl)
    · exact binaryPowerBits_value gapExp
    · exact hB
    · exact binaryNonemptyBits_value live
    · exact binaryNonemptyBits_value live

/-- Generated words meet precisely the validity contract of the executed
instruction loader, once its live coordinate tapes have the required lengths. -/
theorem elementaryHeaderInstruction_valid {n A : ℕ} (t source : Fin n) (hneSource : source ≠ t)
    (rowBits triple : List Bool) (rowExp gapExp rows B : ℕ) (targetWord : List (Fin (A + 4)))
    (hrow : GrowingCounterData.Canonical rowBits) (hne : rowBits ≠ [])
    (hrows : Counter.value rowBits = rows) (htriple : GrowingCounterData.Canonical triple)
    (hB : Counter.value triple = 3 * B)
    (heRow : rowExp = n - (t.val + (elementarySwapSpec t).w))
    (heGap : gapExp = t.val - (elementarySwapSpec t).w) (htarget : targetWord.length = t.val) :
    (ElementaryInstruction.mk t source hneSource
      (elementaryHeaderWords rowBits rowExp gapExp triple targetWord.head?.isSome)).Valid rows B := by
  obtain ⟨hc, hv⟩ := elementaryHeaderWords_valid rowBits rowExp gapExp triple targetWord.head?.isSome
    rows B hrow hne hrows htriple hB
  have hw := elementaryWidthHeader_value t targetWord htarget
  rw [binaryNonemptyBits_value] at hw
  constructor
  · intro i
    change Counter.value (elementaryHeaderWords rowBits rowExp gapExp triple targetWord.head?.isSome i) = _
    rw [hv, elementarySwapValues_eq]
    rw [heRow, heGap, hw]
    congr 1
    exact Nat.mul_comm _ _
  · exact hc

end IntegerMultBounds.MathlibTM2.Routing
