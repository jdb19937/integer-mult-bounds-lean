module

public import IntegerMultBounds.MathlibTM2.Routing.BlockExchangeExec
public import IntegerMultBounds.MathlibTM2.Routing.BinaryTripleScale
public import IntegerMultBounds.MathlibTM2.Routing.BinaryPower

/-! Arithmetic contract for all five headers of a general interval exchange. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.MathlibTM2.Host

def exchangeHeaderWords (rowBits payload widthBits : List Bool) (rowExp gapExp : ℕ) : Fin 5 → List Bool :=
  ![List.replicate rowExp false ++ rowBits, binaryPowerBits gapExp, payload, widthBits, widthBits]

/-- Unlike elementary swaps, general interval exchanges have a shifted payload
header and arbitrary binary widths. These are precisely the host's five values. -/
theorem exchangeHeaderWords_valid (n a b w rows B : ℕ) (hab : a + w ≤ b)
    (rowBits payload widthBits : List Bool)
    (hrow : GrowingCounterData.Canonical rowBits) (hrowNe : rowBits ≠ [])
    (hrows : Counter.value rowBits = rows)
    (hpayload : GrowingCounterData.Canonical payload) (hpayloadValue : Counter.value payload = 2 ^ a * (3 * B))
    (hwidth : GrowingCounterData.Canonical widthBits) (hwidthValue : Counter.value widthBits = w) :
    (∀ k, GrowingCounterData.Canonical
      (exchangeHeaderWords rowBits payload widthBits (n - (b + w)) (b - a - w) k)) ∧
    (∀ k, Counter.value (exchangeHeaderWords rowBits payload widthBits (n - (b + w)) (b - a - w) k) =
      swapValues (blockExchangeDimensions n a b w rows B).1
        (blockExchangeDimensions n a b w rows B).2.1
        (blockExchangeDimensions n a b w rows B).2.2 w w k) := by
  constructor
  · intro k
    fin_cases k
    · exact binaryScale_canonical _ rowBits hrow hrowNe
    · exact binaryPowerBits_canonical _
    · exact hpayload
    · exact hwidth
    · exact hwidth
  · rw [blockExchangeDimensions_eq n a b w rows B hab]
    intro k
    fin_cases k <;> simp [exchangeHeaderWords, swapValues, binaryScale_value, binaryPowerBits_value,
      hrows, hpayloadValue, hwidthValue, Nat.mul_comm]

end IntegerMultBounds.MathlibTM2.Routing
