module

public import IntegerMultBounds.MathlibTM2.Routing.BinaryExchangeChain
public import IntegerMultBounds.MathlibTM2.Routing.ReservoirExchangeSchedule

/-! Concrete forward and reverse reservoir placement with all metadata generated
from binary coordinates and restored after each actual host interchange. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.Networks.Shared50ModularControl (prime)

theorem binaryReservoirPlacement_exec {t₀ T Q K n R B : ℕ} {str tmp : Fin T} {U F : Type}
    (H : ℕ) (hfit : 9 * H ≤ n) (w : ℕ) (hw : w ≤ H) (reservoir : Fin 3) (reverse : Bool)
    (body : F → Pr F T Q (prime + K) U)
    (calls : Fin 3 → BinaryExchangeCall t₀ T Q n R B str tmp)
    (hspec : ∀ j, (calls j).spec = reservoirExchangeSpecs n H hfit w hw reservoir j)
    (v : HS T Q (prime + K) U) (S : Stacks T (prime + K)) (hready : ∀ j, (calls j).Ready S)
    (l : List (List (Fin (prime + K + 4)))) (hl : l.length = R * 2 ^ n)
    (hlB : ∀ r ∈ l, r.length = B) (h8 : ∀ r ∈ l, ∀ s ∈ r, s.val < 8)
    (hsrc : S.R str = l.flatten) :
    ∃ (v' : HS T Q (prime + K) U) (m : ℕ), v'.user = v.user ∧
      (m : ℝ) ≤ binaryExchangeChainCost calls S (reservoirExchangeOrder reverse) ∧
      Exec body (binaryExchangeChain calls (reservoirExchangeOrder reverse)) (mk v S) m
        (mk v' { S with R := Function.update S.R str (moveRecs (reservoirExchangeAction n H hfit w hw reservoir R reverse) l).flatten }) := by
  obtain ⟨v', m, hu, hm, he⟩ := binaryExchangeChain_exec body calls (reservoirExchangeOrder reverse)
    v S hready l hl hlB h8 hsrc
  have hs : (fun j => (calls j).spec) = reservoirExchangeSpecs n H hfit w hw reservoir := funext hspec
  rw [hs, reservoirExchangeChainData_direction n H hfit w hw reservoir R reverse l hl] at he
  exact ⟨v', m, hu, hm, he⟩

end IntegerMultBounds.MathlibTM2.Routing
