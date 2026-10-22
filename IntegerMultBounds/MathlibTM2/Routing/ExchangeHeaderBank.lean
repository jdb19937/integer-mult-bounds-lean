module

public import IntegerMultBounds.MathlibTM2.Routing.ElementaryHeaderBank
public import IntegerMultBounds.MathlibTM2.Routing.ExchangeHeaderValues

/-! A fixed bank for general interval-exchange headers. The target input of the
base bank holds a canonical binary interval width, rather than a unary target. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host

inductive ExchangeHeaderReg where
  | base (r : ElementaryHeaderReg) | lowerExp | triple
  deriving DecidableEq

def exchangeTripleReg : TripleScaleReg → ExchangeHeaderReg
  | .exponent => .lowerExp
  | .src => .base .block
  | .dst => .base (.header 2)
  | .triple => .triple
  | .scratch i => .base (.scratch i)

theorem exchangeTripleReg_injective : Function.Injective exchangeTripleReg := by
  intro i j h
  cases i <;> cases j <;> simp_all [exchangeTripleReg]

def exchangeHeaderProgram {T Q A : ℕ} {P U : Type}
    (rg : ExchangeHeaderReg → Fin T) : Pr P T Q A U :=
  let base := fun r => rg (.base r)
  .seq (binaryScaleProgram (base .rowExp) (base .rows) (base (.header 0)) (base (.scratch 1)) (base (.scratch 2)))
    (.seq (binaryPowerProgram (base .gapExp) (base (.header 1)) (base (.scratch 1)) (base (.scratch 2)))
      (.seq (binaryTripleScaleProgram (rg ∘ exchangeTripleReg))
        (.seq (bcopy (base .target) (base (.header 3)) (base (.scratch 1)) (base (.scratch 2)))
          (bcopy (base .target) (base (.header 4)) (base (.scratch 1)) (base (.scratch 2))))))

def exchangeHeaderPrivate {T : ℕ} (rg : ExchangeHeaderReg → Fin T) : List (Fin T) :=
  [rg (.base (.header 0)), rg (.base (.header 1)), rg (.base (.header 2)),
    rg (.base (.header 3)), rg (.base (.header 4))]

theorem exchangeHeaderBank_keep {T A : ℕ} (R : Fin T → List (Fin (A + 4)))
    (rg : ExchangeHeaderReg → Fin T) (words : Fin 5 → List Bool) (j : Fin T)
    (hj : j ∉ exchangeHeaderPrivate rg) :
    elementaryHeaderBank R (fun r => rg (.base r)) words j = R j := by
  simp only [exchangeHeaderPrivate, List.mem_cons, List.not_mem_nil, or_false, not_or] at hj
  simp [elementaryHeaderBank, hj.1, hj.2.1, hj.2.2.1, hj.2.2.2.1, hj.2.2.2.2]

theorem exchangeHeaderBank_restore {T A : ℕ} (R : Fin T → List (Fin (A + 4)))
    (rg : ExchangeHeaderReg → Fin T) (words : Fin 5 → List Bool)
    (hempty : ∀ k, R (rg (.base (.header k))) = []) :
    metadataCleared (elementaryHeaderBank R (fun r => rg (.base r)) words) (exchangeHeaderPrivate rg) = R := by
  funext j
  by_cases hj : j ∈ exchangeHeaderPrivate rg
  · rw [metadataCleared_at _ _ j hj]
    simp only [exchangeHeaderPrivate, List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl | rfl | rfl | rfl <;> simp [hempty]
  · rw [metadataCleared_keep _ _ j hj, exchangeHeaderBank_keep R rg words j hj]

/-- Cleanup cost depends only on the generated words, not on other tape data. -/
theorem exchangeHeader_cleanCost {T A : ℕ} (R : Fin T → List (Fin (A + 4)))
    (rg : ExchangeHeaderReg → Fin T) (hrg : Function.Injective rg)
    (rowBits payload widthBits : List Bool) (rowExp gapExp : ℕ) :
    metadataCleanCost (elementaryHeaderBank R (fun r => rg (.base r))
      (exchangeHeaderWords rowBits payload widthBits rowExp gapExp)) (exchangeHeaderPrivate rg) =
      2 * (rowExp + rowBits.length + gapExp + 1 + payload.length + 2 * widthBits.length) + 11 := by
  simp [exchangeHeaderPrivate, metadataCleanCost, elementaryHeaderBank, exchangeHeaderWords,
    binaryPowerBits, hrg.eq_iff]
  omega

end IntegerMultBounds.MathlibTM2.Routing
