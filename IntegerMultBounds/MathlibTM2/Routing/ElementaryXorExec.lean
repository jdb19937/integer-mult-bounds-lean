module

public import IntegerMultBounds.MathlibTM2.Routing.ElementaryXor
public import IntegerMultBounds.MathlibTM2.Routing.LowBitXorExec

/-!
# Executed elementary XOR at an arbitrary coordinate

Two width-at-most-one host interchanges surround the row-general lowest-bit
scan. The same interchange headers are reused on the way back. All operations
restore their private banks, leaving only the requested record permutation.
Configuration generation and installation are still caller obligations.
-/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.MathlibTM2.Fast
open IntegerMultBounds.Networks.Shared50ModularControl (prime)

noncomputable def elementaryXorProgram {t₀ T Q K : ℕ} {U P : Type}
    (rg : LayReg t₀ → Fin T) (hrg : Function.Injective rg)
    (hd : Fin 5 → Fin t₀) (pay : Fin t₀) (hhd : Function.Injective hd)
    (hQ : swapStates hd pay hhd ≤ Q) (hT : swapT t₀ ≤ T) : Pr P T Q (prime + K) U :=
  let bank := fun j => rg (.sw j)
  have hi : Function.Injective bank := fun _ _ h => LayReg.sw.inj (hrg h)
  .seq (swapPass hd pay hhd hQ bank hi hT (rg .str) (rg .tmp))
    (.seq (lowBitXorProgram rg) (swapPass hd pay hhd hQ bank hi hT (rg .str) (rg .tmp)))

noncomputable def elementaryXorCost {t₀ T K n : ℕ} (rg : LayReg t₀ → Fin T)
    (t : Fin n) (R B : ℕ) (S : Stacks T (prime + K)) : ℝ :=
  2 * exchangeStepCost (fun _ : Unit => elementarySwapSpec t)
    (fun _ j => rg (.sw j)) R B S () + elementaryScanCost n (R * 2 ^ n) B

/-- Three actual host calls implement exactly one arbitrary coordinate XOR. -/
theorem elementaryXor_exec {t₀ T Q K n R B : ℕ} {U P : Type}
    (body : P → Pr P T Q (prime + K) U) (rg : LayReg t₀ → Fin T)
    (hrg : Function.Injective rg) (hd : Fin 5 → Fin t₀) (pay : Fin t₀)
    (hhd : Function.Injective hd) (hQ : swapStates hd pay hhd ≤ Q) (hT : swapT t₀ ≤ T)
    (t s : Fin n) (hne : s ≠ t) (hR : 0 < R) (hB : 1 ≤ B)
    (hs : Fin 5 → List Bool)
    (hv : ∀ k, Counter.value (hs k) = swapValues
      (blockExchangeDimensions n (elementarySwapSpec t).a (elementarySwapSpec t).b
        (elementarySwapSpec t).w R B).1
      (blockExchangeDimensions n (elementarySwapSpec t).a (elementarySwapSpec t).b
        (elementarySwapSpec t).w R B).2.1
      (blockExchangeDimensions n (elementarySwapSpec t).a (elementarySwapSpec t).b
        (elementarySwapSpec t).w R B).2.2 (elementarySwapSpec t).w (elementarySwapSpec t).w k)
    (hc : ∀ k, GrowingCounterData.Canonical (hs k))
    (v : HS T Q (prime + K) U) (S : Stacks T (prime + K))
    (hL : ∀ j, S.L j = [])
    (hcfg : ElementaryCfg rg S.R n (R * 2 ^ n) B 0 ((elementarySwapSpec t).coordinate s).val)
    (hpay0 : S.R (rg (.sw (reg pay))) = [])
    (hpriv : ∀ j : Fin (swapT t₀), t₀ ≤ j.val → S.R (rg (.sw j)) = [])
    (hhdr : ∀ k, S.R (rg (.sw (reg (hd k)))) = separator :: (hs k).map bitSymbol)
    (hother : ∀ i, i ≠ pay → (∀ k, hd k ≠ i) →
      ∀ x ∈ S.R (rg (.sw (reg i))), x ≠ blank ∧ x.val < prime + 4)
    (l : List (List (Fin (prime + K + 4)))) (hl : l.length = R * 2 ^ n)
    (hlB : ∀ r ∈ l, r.length = B) (h8 : ∀ r ∈ l, ∀ x ∈ r, x.val < 8)
    (hsrc : S.R (rg .str) = l.flatten) :
    ∃ (v' : HS T Q (prime + K) U) (m : ℕ), v'.user = v.user ∧
      (m : ℝ) ≤ elementaryXorCost rg t R B S ∧
      Exec body (elementaryXorProgram rg hrg hd pay hhd hQ hT) (mk v S) m
        (mk v' { S with R := Function.update S.R (rg .str) (moveRecs (elementaryXorRank t s hne R) l).flatten }) := by
  let spec := elementarySwapSpec t
  let bank := fun j => rg (.sw j)
  have hbank : Function.Injective bank := fun _ _ h => LayReg.sw.inj (hrg h)
  have hst : rg .str ≠ rg .tmp := by simp [hrg.eq_iff]
  have hstr (j) : bank j ≠ rg .str := by simp [bank, hrg.eq_iff]
  have htmp (j) : bank j ≠ rg .tmp := by simp [bank, hrg.eq_iff]
  let π := spec.rank R
  let χ := lowBitXorPerm n (spec.coordinate s).val R (by have := t.isLt; omega)
    (elementarySource_pos t s hne)
  let l₁ := moveRecs π l
  let l₂ := moveRecs χ l₁
  let S₁ : Stacks T (prime + K) := { S with R := Function.update S.R (rg .str) l₁.flatten }
  let S₂ : Stacks T (prime + K) := { S with R := Function.update S.R (rg .str) l₂.flatten }
  have hl₁ : l₁.length = R * 2 ^ n := length_moveRecs _ _
  have hl₂ : l₂.length = R * 2 ^ n := length_moveRecs _ _
  have hm₁ : ∀ r ∈ l₁, r ∈ l := fun r hr => mem_moveRecs _ hl hr
  have hm₂ : ∀ r ∈ l₂, r ∈ l := fun r hr => hm₁ r (mem_moveRecs _ hl₁ hr)
  obtain ⟨v₁, m₁, hu₁, hc₁, he₁⟩ := blockExchange_exec body hd pay hhd hQ bank hbank hT
    (rg .str) (rg .tmp) hst hstr htmp n spec.a spec.b spec.w spec.separate spec.fits
    hR (by omega) l hl hlB h8 hs hv hc v S hL hsrc hcfg.tmp hpay0 hpriv hhdr hother
  obtain ⟨v₂, m₂, hu₂, hc₂, he₂⟩ := lowBitXor_exec body hrg (by have := t.isLt; omega)
    (elementarySource_pos t s hne) (spec.coordinate s).isLt hB l₁ hl₁
    (fun r hr => hlB r (hm₁ r hr)) v₁ S₁ (by simp [S₁]) (hcfg.update_stream hrg _)
  have he₂' : Exec body (lowBitXorProgram rg) (mk v₁ S₁) m₂ (mk v₂ S₂) := by
    simpa only [S₁, S₂, Function.update_idem] using he₂
  have hkeep (j) : S₂.R (bank j) = S.R (bank j) := Function.update_of_ne (hstr j) _ _
  obtain ⟨v₃, m₃, hu₃, hc₃, he₃⟩ := blockExchange_exec body hd pay hhd hQ bank hbank hT
    (rg .str) (rg .tmp) hst hstr htmp n spec.a spec.b spec.w spec.separate spec.fits
    hR (by omega) l₂ hl₂ (fun r hr => hlB r (hm₂ r hr)) (fun r hr => h8 r (hm₂ r hr))
    hs hv hc v₂ S₂ hL (by simp [S₂])
    (by dsimp [S₂]; rw [Function.update_of_ne hst.symm]; exact hcfg.tmp)
    (by rw [hkeep]; exact hpay0)
    (by intro j hj; rw [hkeep]; exact hpriv j hj)
    (by intro k; rw [hkeep]; exact hhdr k)
    (by intro i hi hh; rw [hkeep]; exact hother i hi hh)
  have hcost₃ : (m₃ : ℝ) ≤ exchangeStepCost (fun _ : Unit => spec) (fun _ => bank) R B S () := by
    simpa only [exchangeStepCost, hkeep] using hc₃
  have hcost₁ : (m₁ : ℝ) ≤ exchangeStepCost (fun _ : Unit => spec) (fun _ => bank) R B S () := hc₁
  have hdata : moveRecs π l₂ = moveRecs (elementaryXorRank t s hne R) l := by
    rw [elementaryXorRank, moveRecs_trans _ _ l hl, moveRecs_trans _ _ l₁ hl₁]
  have hdata' : moveRecs (blockExchangeRank n spec.a spec.b spec.w R spec.separate spec.fits) l₂ =
      moveRecs (elementaryXorRank t s hne R) l := hdata
  have he₃' : Exec body (swapPass hd pay hhd hQ bank hbank hT (rg .str) (rg .tmp))
      (mk v₂ S₂) m₃
      (mk v₃ { S with R := Function.update S.R (rg .str) (moveRecs (elementaryXorRank t s hne R) l).flatten }) := by
    simpa only [S₂, Function.update_idem, hdata'] using he₃
  refine ⟨v₃, m₁ + (m₂ + m₃), hu₃.trans (hu₂.trans hu₁), ?_, Exec.seq he₁ (Exec.seq he₂' he₃')⟩
  rw [Nat.cast_add, Nat.cast_add]
  change (m₁ : ℝ) + ((m₂ : ℝ) + (m₃ : ℝ)) ≤
    2 * exchangeStepCost (fun _ : Unit => spec) (fun _ => bank) R B S () +
      (elementaryScanCost n (R * 2 ^ n) B : ℝ)
  have hcost₂ : (m₂ : ℝ) ≤ (elementaryScanCost n (R * 2 ^ n) B : ℝ) := by exact_mod_cast hc₂
  linarith only [hcost₁, hcost₂, hcost₃]

end IntegerMultBounds.MathlibTM2.Routing
