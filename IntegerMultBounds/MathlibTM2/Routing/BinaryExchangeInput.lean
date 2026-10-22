module

public import IntegerMultBounds.MathlibTM2.Routing.BinaryExchangeLayoutCall
public import IntegerMultBounds.MathlibTM2.Routing.BinaryExchangeSlots

/-! Initial input-bank construction for the common binary exchange layout.
Borrowed host words remain arbitrary subject to the host's normal frame contract. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.Networks.Shared50ModularControl (prime)

def binaryExchangeInputWords {t₀ A : ℕ} (bankWords : Fin (swapT t₀) → List (Fin (A + 4)))
    (Lc L n a b w B : ℕ) (rowBits : List Bool) (stream : List (Fin (A + 4))) :
    BinaryExchangeReg t₀ → List (Fin (A + 4))
  | .bank j => bankWords j
  | .width => binSyms Lc n
  | .lower => binSyms Lc a
  | .upper => binSyms Lc b
  | .span => binSyms Lc w
  | .rows => rowBits.map bitSymbol
  | .block => binSyms L B
  | .str => stream
  | _ => []

noncomputable def binaryExchangeInputBank {t₀ T A : ℕ} (slot : BinaryExchangeReg t₀ → Fin T)
    (bankWords : Fin (swapT t₀) → List (Fin (A + 4))) (Lc L n a b w B : ℕ)
    (rowBits : List Bool) (stream : List (Fin (A + 4))) : Fin T → List (Fin (A + 4)) :=
  Function.extend slot (binaryExchangeInputWords bankWords Lc L n a b w B rowBits stream) (fun _ => [])

theorem binaryExchangeInputBank_at {t₀ T A : ℕ} (slot : BinaryExchangeReg t₀ → Fin T)
    (hslot : Function.Injective slot) (bankWords : Fin (swapT t₀) → List (Fin (A + 4)))
    (Lc L n a b w B : ℕ) (rowBits : List Bool) (stream : List (Fin (A + 4))) (r : BinaryExchangeReg t₀) :
    binaryExchangeInputBank slot bankWords Lc L n a b w B rowBits stream (slot r) =
      binaryExchangeInputWords bankWords Lc L n a b w B rowBits stream r :=
  hslot.extend_apply _ _ r

theorem binaryExchangeLayoutCall_ready {t₀ T Q K n R B : ℕ}
    (slot : BinaryExchangeReg t₀ → Fin T) (hslot : Function.Injective slot)
    (hd : Fin 5 → Fin t₀) (pay : Fin t₀) (hhd : Function.Injective hd) (hpay : ∀ k, hd k ≠ pay)
    (hQ : swapStates hd pay hhd ≤ Q) (hT : swapT t₀ ≤ T)
    (spec : BlockExchangeSpec n) (hR : 0 < R) (hB : 0 < B)
    (rowBits : List Bool) (Lc L : ℕ) (hn : n < 2 ^ Lc) (hBin : B < 2 ^ L)
    (hrow : GrowingCounterData.Canonical rowBits) (hrowNe : rowBits ≠ []) (hrowValue : Counter.value rowBits = R)
    (bankWords : Fin (swapT t₀) → List (Fin (prime + K + 4)))
    (hpay0 : bankWords (reg pay) = [])
    (hpriv : ∀ j : Fin (swapT t₀), t₀ ≤ j.val → bankWords j = [])
    (hhdr0 : ∀ k, bankWords (reg (hd k)) = [])
    (hother : ∀ i, i ≠ pay → (∀ k, hd k ≠ i) →
      ∀ s ∈ bankWords (reg i), s ≠ blank ∧ s.val < prime + 4)
    (S : Stacks T (prime + K)) (hL : ∀ j, S.L j = []) (stream : List (Fin (prime + K + 4)))
    (hinput : ∀ r, S.R (slot r) = binaryExchangeInputWords bankWords Lc L n spec.a spec.b spec.w B rowBits stream r) :
    (binaryExchangeLayoutCall slot hslot hd pay hhd hpay hQ hT spec hR hB rowBits Lc L hn hBin hrow hrowNe hrowValue).Ready S := by
  constructor <;> (try simp only [binaryExchangeLayoutCall, Function.comp_def, binaryExchangeHeaderReg,
    binaryExchangeHeaderBase, binaryExchangeExponentReg, hinput, binaryExchangeInputWords, forall_const]) <;> assumption

end IntegerMultBounds.MathlibTM2.Routing
