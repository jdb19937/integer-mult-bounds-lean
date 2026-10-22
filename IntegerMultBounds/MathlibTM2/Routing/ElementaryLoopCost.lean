module

public import IntegerMultBounds.MathlibTM2.Routing.ElementaryCost
public import IntegerMultBounds.MathlibTM2.Routing.ElementaryRouting

/-!
# A closed cost bound for the complete uniform elementary router

The fixed bank is restored between calls, so its original size is charged once
per call, not once per archived frame. The final bound is linear in instruction
count times record volume, plus total raw configuration length and fixed-bank
cost. Shared setup and raw configuration generation are separate obligations.
-/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.MathlibTM2.Fast
open IntegerMultBounds.Networks.Shared50ModularControl (prime)

noncomputable def elementaryBaseCost {t₀ T K : ℕ} (rg : LayReg t₀ → Fin T)
    (n rows B : ℕ) (S : Stacks T (prime + K)) : ℝ :=
  (6 * swapConst * (T + 12 * swapT t₀ + 5 : ℕ) + 176) * (rows * 2 ^ n * B : ℕ) +
    (12 * ∑ j, (S.R (rg (.sw j))).length + 4 * T + 12 * swapT t₀ + 60 : ℕ)

theorem elementaryBaseCost_nonneg {t₀ T K : ℕ} (rg : LayReg t₀ → Fin T)
    (n rows B : ℕ) (S : Stacks T (prime + K)) : 0 ≤ elementaryBaseCost rg n rows B S := by
  have h := swapConst_pos
  unfold elementaryBaseCost
  positivity

private theorem elementaryLoopCost_algebra (k F L a f x y : ℝ)
    (hx : x ≤ a + f * F) (hy : y ≤ k * (a + 2) + f * L + 1) :
    x + 2 + y ≤ (k + 1) * (a + 2) + f * (F + L) + 1 := by
  nlinarith only [hx, hy]

theorem elementaryStepPrice_le_base {t₀ T K n : ℕ} (rg : LayReg t₀ → Fin T)
    (hd : Fin 5 → Fin t₀) (config saved : Fin T)
    (hconfig : ∀ r, config ≠ rg r) (hsaved : ∀ r, saved ≠ rg r)
    (rows B : ℕ) (hrows : 0 < rows) (hB : 1 ≤ B) (hn : n ≤ B)
    (S : Stacks T (prime + K)) (hempty : ∀ key, S.R (elementaryConfigTarget rg hd key) = [])
    (d : ElementaryInstruction n) (rest : List (Fin (prime + K + 4))) :
    elementaryStepPrice rg hd config saved rows B S d rest ≤ elementaryBaseCost rg n rows B S +
      (12 * swapT t₀ + 18 : ℕ) * (d.frame : List (Fin (prime + K + 4))).length := by
  have h := elementaryStepPrice_le rg hd config saved hconfig hsaved rows B hrows hB hn S hempty d rest
  refine h.trans (le_of_eq ?_)
  simp only [elementaryBaseCost, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  ring

/-- Sum the actual recursive ledger without accumulating archived-prefix costs. -/
theorem elementaryLoopCost_le {t₀ T K n : ℕ} (rg : LayReg t₀ → Fin T) (hrg : Function.Injective rg)
    (hd : Fin 5 → Fin t₀) (config saved : Fin T)
    (hconfig : ∀ r, config ≠ rg r) (hsaved : ∀ r, saved ≠ rg r)
    (rows B : ℕ) (hrows : 0 < rows) (hB : 1 ≤ B) (hn : n ≤ B)
    (ds : List (ElementaryInstruction n)) (S : Stacks T (prime + K))
    (hempty : ∀ key, S.R (elementaryConfigTarget rg hd key) = [])
    (l : List (List (Fin (prime + K + 4)))) :
    elementaryLoopCost rg hd config saved rows B S ds l ≤
      (ds.length : ℝ) * (elementaryBaseCost rg n rows B S + 2) +
        (12 * swapT t₀ + 18 : ℕ) * (elementaryFrames (A := prime + K) ds).length + 1 := by
  induction ds generalizing S l with
  | nil => simp [elementaryLoopCost, elementaryFrames]
  | cons d ds ih =>
    let S₁ : Stacks T (prime + K) :=
      { S with R := elementaryStepBank S.R rg config saved d rows (elementaryFrames ds) l }
    let l₁ := moveRecs (d.rank rows) l
    have hkeep (r : LayReg t₀) (hr : r ≠ .str) : S₁.R (rg r) = S.R (rg r) :=
      elementaryStepBank_keep S.R rg hrg config saved hconfig hsaved d rows _ l r hr
    have hempty₁ : ∀ key, S₁.R (elementaryConfigTarget rg hd key) = [] := by
      intro key
      have hk := hempty key
      rcases elementaryConfigTarget_role rg hd key with ⟨j, hj⟩ | hj
      · rw [hj] at hk ⊢
        rw [hkeep _ (by simp)]
        exact hk
      · rw [hj] at hk ⊢
        rw [hkeep _ (by simp)]
        exact hk
    have hbank : (∑ j, (S₁.R (rg (.sw j))).length) = ∑ j, (S.R (rg (.sw j))).length := by
      apply Finset.sum_congr rfl
      intro j _
      rw [hkeep _ (by simp)]
    have hbase : elementaryBaseCost rg n rows B S₁ = elementaryBaseCost rg n rows B S := by
      simp only [elementaryBaseCost, hbank]
    have hi := ih S₁ hempty₁ l₁
    rw [hbase] at hi
    have hs := elementaryStepPrice_le_base rg hd config saved hconfig hsaved rows B hrows hB hn S hempty d
      (elementaryFrames ds)
    simp only [elementaryLoopCost, List.length_cons, elementaryFrames, List.length_append]
    simp only [Nat.cast_add, Nat.cast_one] at hs hi ⊢
    exact elementaryLoopCost_algebra _ _ _ _ _ _ _ hs hi

/-- Includes initial loop setup and restoration of the complete raw input. -/
theorem elementaryRoutingCost_le {t₀ T K n : ℕ} (rg : LayReg t₀ → Fin T) (hrg : Function.Injective rg)
    (hd : Fin 5 → Fin t₀) (config saved : Fin T)
    (hconfig : ∀ r, config ≠ rg r) (hsaved : ∀ r, saved ≠ rg r)
    (rows B : ℕ) (hrows : 0 < rows) (hB : 1 ≤ B) (hn : n ≤ B)
    (ds : List (ElementaryInstruction n)) (S : Stacks T (prime + K))
    (hempty : ∀ key, S.R (elementaryConfigTarget rg hd key) = [])
    (l : List (List (Fin (prime + K + 4)))) :
    1 + elementaryLoopCost rg hd config saved rows B S ds l +
        (2 * (elementaryFrames (A := prime + K) ds).length + 2 : ℕ) ≤
      (ds.length : ℝ) * (elementaryBaseCost rg n rows B S + 2) +
        (12 * swapT t₀ + 20 : ℕ) * (elementaryFrames (A := prime + K) ds).length + 4 := by
  have h := elementaryLoopCost_le rg hrg hd config saved hconfig hsaved rows B hrows hB hn ds S hempty l
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at h ⊢
  nlinarith only [h]

variable {t₀ T Q K : ℕ} {U P : Type}

/-- The actual fixed router with a closed total bound, including metadata loading,
all elementary updates, cleanup, loop guards and full raw-input restoration. -/
theorem elementaryRouting_exec_le {n rows B : ℕ}
    (body : P → Pr P T Q (prime + K) U) (rg : LayReg t₀ → Fin T) (hrg : Function.Injective rg)
    (hd : Fin 5 → Fin t₀) (pay : Fin t₀) (hhd : Function.Injective hd) (hpay : ∀ j, hd j ≠ pay)
    (hQ : swapStates hd pay hhd ≤ Q) (hT : swapT t₀ ≤ T)
    (config saved : Fin T) (hcs : config ≠ saved)
    (hconfig : ∀ r, config ≠ rg r) (hsaved : ∀ r, saved ≠ rg r)
    (hrows : 0 < rows) (hB : 1 ≤ B) (hn : n ≤ B) (ds : List (ElementaryInstruction n))
    (hvalid : ∀ d ∈ ds, d.Valid rows B)
    (v : HS T Q (prime + K) U) (S : Stacks T (prime + K))
    (hL : ∀ j, S.L j = []) (hready : ElementaryLoopReady rg hd pay S.R n rows B)
    (harchive : S.R saved = [])
    (l : List (List (Fin (prime + K + 4)))) (hl : l.length = rows * 2 ^ n)
    (hlB : ∀ r ∈ l, r.length = B) (h8 : ∀ r ∈ l, ∀ x ∈ r, x.val < 8)
    (hstream : S.R (rg .str) = l.flatten) (hinput : S.R config = elementaryFrames ds) :
    ∃ (v' : HS T Q (prime + K) U) (m : ℕ), v'.user = v.user ∧
      (m : ℝ) ≤ (ds.length : ℝ) * (elementaryBaseCost rg n rows B S + 2) +
        (12 * swapT t₀ + 20 : ℕ) * (elementaryFrames (A := prime + K) ds).length + 4 ∧
      Exec body (elementaryRoutingProgram rg hrg hd pay hhd hQ hT config saved) (mk v S) m
        (mk v' { S with R := Function.update S.R (rg .str) (moveRecs (elementaryInstructionsRank rows ds) l).flatten }) := by
  obtain ⟨v', m, hu, hm, he⟩ := elementaryRouting_exec body rg hrg hd pay hhd hpay hQ hT
    config saved hcs hconfig hsaved hrows hB ds hvalid v S hL hready harchive
    l hl hlB h8 hstream hinput
  exact ⟨v', m, hu, hm.trans (elementaryRoutingCost_le rg hrg hd config saved hconfig hsaved
    rows B hrows hB hn ds S hready.empty l), he⟩

end IntegerMultBounds.MathlibTM2.Routing
