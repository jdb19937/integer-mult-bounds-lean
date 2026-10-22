module

public import IntegerMultBounds.MathlibTM2.Routing.BlockExchangeIndex

/-!
# Executed equal-width interval exchange

Specialize the existing uniform host interchange to the explicit coordinate
exchange. Symbol conversion, payload movement, private scratch restoration and
all host steps are included. Canonical raw headers are still inputs: generating
and installing those headers is a later R3 setup obligation.
-/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.MathlibTM2.Layer.CompactDigits
open IntegerMultBounds.Networks.Shared50ModularControl (prime)

def blockExchangeDimensions (n a b w R B : ℕ) : ℕ × ℕ × ℕ :=
  swapDimsIdx (len := blockExchangeLen a b w) 1 3 w R n B

theorem blockExchangeDimensions_eq (n a b w R B : ℕ) (hab : a + w ≤ b) :
    blockExchangeDimensions n a b w R B =
      (R * 2 ^ (n - (b + w)), 2 ^ (b - a - w), 2 ^ a * (3 * B)) := by
  obtain ⟨ha, hb⟩ := blockExchange_off a b w hab
  simp only [blockExchangeDimensions, swapDimsIdx, ha, hb]

/-- Actual uniform interval interchange on an arbitrary rectangular record bank.
Only the stream changes, by the rank permutation whose bit action was proved in
`blockExchangeRank_bit`; all other stacks and the user state are restored. -/
theorem blockExchange_exec {t₀ T Q K : ℕ} {U F : Type}
    (body : F → Pr F T Q (prime + K) U)
    (hd : Fin 5 → Fin t₀) (pay : Fin t₀) (hhd : Function.Injective hd)
    (hQ : swapStates hd pay hhd ≤ Q)
    (bank : Fin (swapT t₀) → Fin T) (hbank : Function.Injective bank) (hT : swapT t₀ ≤ T)
    (str tmp : Fin T) (hst : str ≠ tmp)
    (hstr : ∀ j, bank j ≠ str) (htmp : ∀ j, bank j ≠ tmp)
    (n a b w : ℕ) (hab : a + w ≤ b) (hb : b + w ≤ n)
    {R B : ℕ} (hR : 0 < R) (hB : 0 < B)
    (l : List (List (Fin (prime + K + 4)))) (hl : l.length = R * 2 ^ n)
    (hlB : ∀ r ∈ l, r.length = B) (h8 : ∀ r ∈ l, ∀ s ∈ r, s.val < 8)
    (hs : Fin 5 → List Bool)
    (hv : ∀ k, Counter.value (hs k) = swapValues
      (blockExchangeDimensions n a b w R B).1
      (blockExchangeDimensions n a b w R B).2.1
      (blockExchangeDimensions n a b w R B).2.2 w w k)
    (hc : ∀ k, GrowingCounterData.Canonical (hs k))
    (v : HS T Q (prime + K) U) (S : Stacks T (prime + K))
    (hL : ∀ j, S.L j = []) (hsrc : S.R str = l.flatten) (htmp0 : S.R tmp = [])
    (hpay0 : S.R (bank (reg pay)) = [])
    (hpriv : ∀ j : Fin (swapT t₀), t₀ ≤ j.val → S.R (bank j) = [])
    (hhdr : ∀ k, S.R (bank (reg (hd k))) = separator :: (hs k).map bitSymbol)
    (hother : ∀ i, i ≠ pay → (∀ k, hd k ≠ i) →
      ∀ s ∈ S.R (bank (reg i)), s ≠ blank ∧ s.val < prime + 4) :
    ∃ (v' : HS T Q (prime + K) U) (m : ℕ), v'.user = v.user ∧
      (m : ℝ) ≤ 3 * swapConst * (T + 12 * swapT t₀ + 5 : ℕ) *
        (R * 2 ^ n * B : ℕ) * ((max 1 w : ℕ) : ℝ) ^ Parameters.tau +
        (6 * ∑ j, (S.R (bank j)).length + 34 * (R * 2 ^ n * B) +
          2 * T + 6 * swapT t₀ + 23 : ℕ) ∧
      Exec body (swapPass hd pay hhd hQ bank hbank hT str tmp) (mk v S) m
        (mk v' { S with R := Function.update S.R str (moveRecs (blockExchangeRank n a b w R hab hb) l).flatten }) := by
  have ho := (blockExchange_off a b w hab).2
  exact cxSwap_exec (len := blockExchangeLen a b w) (w := w) body hd pay hhd hQ bank hbank hT
    str tmp hst hstr htmp (by decide : (1 : Fin 4) < 3) rfl rfl hR (by omega)
    (blockExchangeRank n a b w R hab hb) (fun _ => rfl) hB l hl hlB h8 hs hv hc
    v S hL hsrc htmp0 hpay0 hpriv hhdr hother

end IntegerMultBounds.MathlibTM2.Routing
