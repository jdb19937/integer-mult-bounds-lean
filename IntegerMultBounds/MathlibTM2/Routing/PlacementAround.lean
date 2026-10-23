module

public import IntegerMultBounds.MathlibTM2.Routing.BinaryReservoirPlacement

/-! Surround any verified record permutation by forward and inverse placement.
The structural composition preserves all nonstream tapes and charges all phases. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.Networks.Shared50ModularControl (prime)

theorem placementAround_exec {t₀ T Q K W R B : ℕ} {P U : Type}
    (body : P → Pr P T Q (prime + K) U) (src tmp : Fin T) (H : ℕ) (hfit : 9 * H ≤ W)
    (w : ℕ) (hw : w ≤ H) (reservoir : Fin 3)
    (calls : Fin 3 → BinaryExchangeCall t₀ T Q W R B src tmp)
    (hspec : ∀ j, (calls j).spec = reservoirExchangeSpecs W H hfit w hw reservoir j)
    (v : HS T Q (prime + K) U) (S : Stacks T (prime + K)) (hready : ∀ j, (calls j).Ready S)
    (l : List (List (Fin (prime + K + 4)))) (hl : l.length = R * 2 ^ W)
    (hlen : ∀ r ∈ l, r.length = B ∧ ∀ a ∈ r, a.val < 8) (hsrc : S.R src = l.flatten)
    (repair : Pr P T Q (prime + K) U) (π : Equiv.Perm (Fin (R * 2 ^ W))) (C : ℝ)
    (hrepair : ∀ u : HS T Q (prime + K) U,
      let forward := reservoirExchangeAction W H hfit w hw reservoir R false
      let l₁ := moveRecs forward l
      let S₁ : Stacks T (prime + K) := { S with R := Function.update S.R src l₁.flatten }
      ∃ (u' : HS T Q (prime + K) U) (k : ℕ), u'.user = u.user ∧ (k : ℝ) ≤ C ∧
        Exec body repair (mk u S₁) k
          (mk u' { S₁ with R := Function.update S₁.R src (moveRecs π l₁).flatten })) :
    let forward := reservoirExchangeAction W H hfit w hw reservoir R false
    let backward := reservoirExchangeAction W H hfit w hw reservoir R true
    ∃ (v' : HS T Q (prime + K) U) (steps : ℕ), v'.user = v.user ∧
      (steps : ℝ) ≤ binaryExchangeChainCost calls S (reservoirExchangeOrder false) + C +
        binaryExchangeChainCost calls S (reservoirExchangeOrder true) ∧
      Exec body (.seq (binaryExchangeChain calls (reservoirExchangeOrder false))
        (.seq repair (binaryExchangeChain calls (reservoirExchangeOrder true))))
        (mk v S) steps (mk v' { S with R := Function.update S.R src (moveRecs backward (moveRecs π (moveRecs forward l))).flatten }) := by
  let forward := reservoirExchangeAction W H hfit w hw reservoir R false
  let backward := reservoirExchangeAction W H hfit w hw reservoir R true
  let l₁ := moveRecs forward l
  let S₁ : Stacks T (prime + K) := { S with R := Function.update S.R src l₁.flatten }
  obtain ⟨v₁, m₁, hu₁, hm₁, he₁⟩ := binaryReservoirPlacement_exec H hfit w hw reservoir false body calls hspec
    v S hready l hl (fun r hr => (hlen r hr).1) (fun r hr => (hlen r hr).2) hsrc
  obtain ⟨v₂, m₂, hu₂, hm₂, he₂⟩ := hrepair v₁
  have hl₁ : l₁.length = R * 2 ^ W := length_moveRecs _ _
  have hmem₁ : ∀ r ∈ l₁, r ∈ l := fun r hr => mem_moveRecs _ hl hr
  let l₂ := moveRecs π l₁
  let S₂ : Stacks T (prime + K) := { S₁ with R := Function.update S₁.R src l₂.flatten }
  have hl₂ : l₂.length = R * 2 ^ W := length_moveRecs _ _
  have hmem₂ : ∀ r ∈ l₂, r ∈ l := fun r hr => hmem₁ r (mem_moveRecs _ hl₁ hr)
  have hready₂ : ∀ j, (calls j).Ready S₂ := fun j =>
    BinaryExchangeCall.Ready.updateStream (calls j) S₁
      (BinaryExchangeCall.Ready.updateStream (calls j) S (hready j) l₁.flatten) l₂.flatten
  obtain ⟨v₃, m₃, hu₃, hm₃, he₃⟩ := binaryReservoirPlacement_exec H hfit w hw reservoir true body calls hspec
    v₂ S₂ hready₂ l₂ hl₂ (fun r hr => (hlen r (hmem₂ r hr)).1)
    (fun r hr => (hlen r (hmem₂ r hr)).2) (by simp [S₂])
  have hcost : binaryExchangeChainCost calls S₂ (reservoirExchangeOrder true) =
      binaryExchangeChainCost calls S (reservoirExchangeOrder true) := by
    rw [binaryExchangeChainCost_updateStream calls S₁ l₂.flatten,
      binaryExchangeChainCost_updateStream calls S l₁.flatten]
  rw [hcost] at hm₃
  refine ⟨v₃, m₁ + (m₂ + m₃), hu₃.trans (hu₂.trans hu₁), ?_, ?_⟩
  · simp only [Nat.cast_add]
    linarith only [hm₁, hm₂, hm₃]
  · dsimp only [S₁] at he₂
    simp only [Function.update_idem] at he₂
    dsimp only [S₂, S₁] at he₃
    simp only [Function.update_idem] at he₃
    exact Exec.seq he₁ (Exec.seq he₂ he₃)

end IntegerMultBounds.MathlibTM2.Routing
