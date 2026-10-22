module

public import IntegerMultBounds.MathlibTM2.Routing.BinaryScheduleCalls
public import IntegerMultBounds.MathlibTM2.Routing.BinaryReservoirPlacement

/-! Reservoir placement from one actual common input bank, rather than separate
per-call readiness assumptions. All three calls share headers and scratch. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.Networks.Shared50ModularControl (prime)

theorem commonBankReservoir_exec {t₀ T Q K n R B : ℕ} {U F : Type}
    (slot : BinaryScheduleReg t₀ 3 → Fin T) (hslot : Function.Injective slot)
    (hd : Fin 5 → Fin t₀) (pay : Fin t₀) (hhd : Function.Injective hd) (hpay : ∀ k, hd k ≠ pay)
    (hQ : swapStates hd pay hhd ≤ Q) (hT : swapT t₀ ≤ T)
    (H : ℕ) (hfit : 9 * H ≤ n) (w : ℕ) (hw : w ≤ H) (reservoir : Fin 3) (reverse : Bool)
    (hR : 0 < R) (hB : 0 < B) (rowBits : List Bool) (Lc L : ℕ) (hn : n < 2 ^ Lc) (hBin : B < 2 ^ L)
    (hrow : GrowingCounterData.Canonical rowBits) (hrowNe : rowBits ≠ []) (hrowValue : Counter.value rowBits = R)
    (bankWords : Fin (swapT t₀) → List (Fin (prime + K + 4)))
    (hpay0 : bankWords (reg pay) = [])
    (hpriv : ∀ j : Fin (swapT t₀), t₀ ≤ j.val → bankWords j = [])
    (hhdr0 : ∀ k, bankWords (reg (hd k)) = [])
    (hother : ∀ i, i ≠ pay → (∀ k, hd k ≠ i) →
      ∀ s ∈ bankWords (reg i), s ≠ blank ∧ s.val < prime + 4)
    (body : F → Pr F T Q (prime + K) U) (v : HS T Q (prime + K) U) (S : Stacks T (prime + K))
    (hL : ∀ j, S.L j = [])
    (l : List (List (Fin (prime + K + 4)))) (hl : l.length = R * 2 ^ n)
    (hlB : ∀ r ∈ l, r.length = B) (h8 : ∀ r ∈ l, ∀ s ∈ r, s.val < 8)
    (hinput : ∀ r, S.R (slot r) = binaryScheduleInputWords (reservoirExchangeSpecs n H hfit w hw reservoir)
      bankWords Lc L B rowBits l.flatten r) :
    let calls := binaryScheduleCalls slot hslot hd pay hhd hpay hQ hT
      (reservoirExchangeSpecs n H hfit w hw reservoir) hR hB rowBits Lc L hn hBin hrow hrowNe hrowValue
    ∃ (v' : HS T Q (prime + K) U) (m : ℕ), v'.user = v.user ∧
      (m : ℝ) ≤ binaryExchangeChainCost calls S (reservoirExchangeOrder reverse) ∧
      Exec body (binaryExchangeChain calls (reservoirExchangeOrder reverse)) (mk v S) m
        (mk v' { S with R := Function.update S.R (slot .str) (moveRecs (reservoirExchangeAction n H hfit w hw reservoir R reverse) l).flatten }) := by
  let spec := reservoirExchangeSpecs n H hfit w hw reservoir
  let calls := binaryScheduleCalls slot hslot hd pay hhd hpay hQ hT spec hR hB rowBits Lc L hn hBin hrow hrowNe hrowValue
  have hwords (r : BinaryScheduleReg t₀ 3) : S.R (slot r) = binaryScheduleInputWords spec bankWords Lc L B rowBits l.flatten r := hinput r
  have hready : ∀ j, (calls j).Ready S :=
    binaryScheduleCalls_ready slot hslot hd pay hhd hpay hQ hT spec hR hB rowBits Lc L hn hBin
      hrow hrowNe hrowValue bankWords hpay0 hpriv hhdr0 hother S hL l.flatten hwords
  exact binaryReservoirPlacement_exec H hfit w hw reservoir reverse body calls
    (binaryScheduleCalls_spec slot hslot hd pay hhd hpay hQ hT spec hR hB rowBits Lc L hn hBin hrow hrowNe hrowValue)
    v S hready l hl hlB h8 (hwords .str)

end IntegerMultBounds.MathlibTM2.Routing
