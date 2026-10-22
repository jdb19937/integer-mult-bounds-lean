module

public import IntegerMultBounds.MathlibTM2.Routing.ElementaryLoopCost
public import IntegerMultBounds.MathlibTM2.Routing.ElementaryInstructionSemantics

/-!
# Terminal routing cost in the shared geometry

The complete elementary execution ledger, including input rewind, has fewer
than 131G calls. Configuration length remains explicit: generating those words
and the shared counters is a separate part of the full router.
-/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
open IntegerMultBounds.Networks.Shared50ModularControl (prime)

/-- Specialize the fully charged routing ledger to the terminal suffix. -/
theorem routerTerminalCost_le {t₀ T K n G : ℕ}
    (rg : LayReg t₀ → Fin T) (hrg : Function.Injective rg)
    (hd : Fin 5 → Fin t₀) (config saved : Fin T)
    (hconfig : ∀ r, config ≠ rg r) (hsaved : ∀ r, saved ≠ rg r)
    (hG : 0 < G) (hn : 64 * G ≤ n)
    (rows B : ℕ) (hrows : 0 < rows) (hB : 1 ≤ B)
    (hwidth : routerTargetWidth n (64 * G) G ≤ B)
    (targets : Finset (Fin (routerTargetWidth n (64 * G) G)))
    (ds : List (ElementaryInstruction (routerTargetWidth n (64 * G) G)))
    (htargets : (ds.map ElementaryInstruction.target).reverse =
      (routerTerminalTargets n (64 * G) G targets).toList)
    (S : Stacks T (prime + K))
    (hempty : ∀ key, S.R (elementaryConfigTarget rg hd key) = [])
    (l : List (List (Fin (prime + K + 4)))) :
    1 + elementaryLoopCost rg hd config saved rows B S ds l +
        (2 * (elementaryFrames (A := prime + K) ds).length + 2 : ℕ) ≤
      (131 * G : ℕ) * (elementaryBaseCost rg (routerTargetWidth n (64 * G) G) rows B S + 2) +
        (12 * swapT t₀ + 20 : ℕ) * (elementaryFrames (A := prime + K) ds).length + 4 := by
  have hc : (ds.length : ℝ) ≤ (131 * G : ℕ) := by
    exact_mod_cast (routerTerminalInstruction_count n G hG hn targets ds htargets).le
  have hb : 0 ≤ elementaryBaseCost rg (routerTargetWidth n (64 * G) G) rows B S + 2 :=
    add_nonneg (elementaryBaseCost_nonneg _ _ _ _ _) (by norm_num)
  have hm := mul_le_mul_of_nonneg_right hc hb
  have h := elementaryRoutingCost_le rg hrg hd config saved hconfig hsaved rows B
    hrows hB hwidth ds S hempty l
  linarith only [h, hm]

end IntegerMultBounds.MathlibTM2.Routing
