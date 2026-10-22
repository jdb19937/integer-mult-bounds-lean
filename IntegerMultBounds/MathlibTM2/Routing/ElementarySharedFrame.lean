module

public import IntegerMultBounds.MathlibTM2.Routing.ElementarySharedSetup
public import IntegerMultBounds.MathlibTM2.Routing.ElementaryLoop

/-!
# The shared setup preserves the complete elementary loop frame

Only four persistent words are installed. In particular, raw instruction tapes,
record streams, per-call destinations and every interchange register are framed.
-/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
open IntegerMultBounds.Networks.Shared50ModularControl (prime)

theorem elementarySharedSetup_keep {t₀ T A : ℕ} (rg : LayReg t₀ → Fin T)
    (cfg : Fin 4 → Fin T) (wb wm B M : ℕ) (R : Fin T → List (Fin (A + 4)))
    (k : Fin T) (hk : ∀ key, k ≠ elementarySharedTarget rg key) :
    metadataInstalled R (elementarySharedJobs rg cfg wb wm B M) k = R k := by
  apply metadataInstalled_keep
  intro hx
  obtain ⟨job, hj, he⟩ := List.mem_map.mp hx
  obtain ⟨key, _, rfl⟩ := List.mem_map.mp hj
  exact hk key ((elementarySharedJob_dst rg cfg wb wm B M key).symm.trans he).symm

/-- Four installed words suffice; all interchange side conditions survive setup. -/
theorem elementarySharedSetup_ready {t₀ T A : ℕ} (rg : LayReg t₀ → Fin T)
    (hrg : Function.Injective rg) (hd : Fin 5 → Fin t₀) (pay : Fin t₀)
    (cfg : Fin 4 → Fin T) (wb wm n rows B : ℕ) (R : Fin T → List (Fin (A + 4)))
    (data : ElementarySharedData cfg wb wm n B (rows * 2 ^ n) R)
    (hblank : ∀ r : LayReg t₀, r ≠ .ctrB → r ≠ .cnt → r ≠ .fld → r ≠ .mA →
      r ≠ .str → r ≠ .mB → (∀ j, r ≠ .sw j) → R (rg r) = [])
    (hempty : ∀ key, R (elementaryConfigTarget rg hd key) = [])
    (hpay : R (rg (.sw (reg pay))) = [])
    (hprivate : ∀ j : Fin (swapT t₀), t₀ ≤ j.val → R (rg (.sw j)) = [])
    (hother : ∀ i, i ≠ pay → (∀ k, hd k ≠ i) →
      ∀ x ∈ R (rg (.sw (reg i))), x ≠ blank ∧ x.val < prime + 4) :
    ElementaryLoopReady rg hd pay
      (metadataInstalled R (elementarySharedJobs rg cfg wb wm B (rows * 2 ^ n))) n rows B := by
  have hsw (j : Fin (swapT t₀)) :
      metadataInstalled R (elementarySharedJobs rg cfg wb wm B (rows * 2 ^ n)) (rg (.sw j)) =
        R (rg (.sw j)) := by
    apply elementarySharedSetup_keep
    intro key
    fin_cases key <;> simp [elementarySharedTarget, hrg.eq_iff]
  have hmask :
      metadataInstalled R (elementarySharedJobs rg cfg wb wm B (rows * 2 ^ n)) (rg .mB) = R (rg .mB) := by
    apply elementarySharedSetup_keep
    intro key
    fin_cases key <;> simp [elementarySharedTarget, hrg.eq_iff]
  refine ⟨elementarySharedSetup_prepared rg hrg cfg wb wm n B (rows * 2 ^ n) R data hblank,
    ?_, ?_, ?_, ?_⟩
  · intro key
    rcases elementaryConfigTarget_role rg hd key with ⟨j, hj⟩ | hj
    · rw [hj, hsw]
      simpa only [hj] using hempty key
    · rw [hj, hmask]
      simpa only [hj] using hempty key
  · rw [hsw]
    exact hpay
  · intro j hj
    rw [hsw]
    exact hprivate j hj
  · intro i hi hk
    rw [hsw]
    exact hother i hi hk

/-- After routing, clearing shared metadata restores every initial word except
for the output stream. Binary configuration sources are restored as well. -/
theorem elementarySharedSetup_restore {t₀ T A : ℕ} (rg : LayReg t₀ → Fin T)
    (hrg : Function.Injective rg) (cfg : Fin 4 → Fin T) (wb wm B M : ℕ)
    (R : Fin T → List (Fin (A + 4))) (out : List (Fin (A + 4)))
    (hempty : ∀ key, R (elementarySharedTarget rg key) = []) :
    metadataCleared
      (Function.update (metadataInstalled R (elementarySharedJobs rg cfg wb wm B M)) (rg .str) out)
      ((elementarySharedJobs rg cfg wb wm B M).map MetadataJob.dst) =
        Function.update R (rg .str) out := by
  rw [metadataCleared_update]
  · rw [metadataClean_restore]
    intro job hj
    obtain ⟨key, _, rfl⟩ := List.mem_map.mp hj
    rw [elementarySharedJob_dst]
    exact hempty key
  · intro hx
    obtain ⟨job, hj, he⟩ := List.mem_map.mp hx
    obtain ⟨key, _, rfl⟩ := List.mem_map.mp hj
    rw [elementarySharedJob_dst] at he
    fin_cases key <;> simp_all [elementarySharedTarget, hrg.eq_iff]

/-- Clearing the two unary counters and two address words has a linear price. -/
theorem elementarySharedSetup_cleanCost {t₀ T A : ℕ} (rg : LayReg t₀ → Fin T)
    (hrg : Function.Injective rg) (cfg : Fin 4 → Fin T) (wb wm n B M : ℕ)
    (R : Fin T → List (Fin (A + 4))) (data : ElementarySharedData cfg wb wm n B M R) :
    metadataCleanCost (metadataInstalled R (elementarySharedJobs rg cfg wb wm B M))
      ((elementarySharedJobs rg cfg wb wm B M).map MetadataJob.dst) =
        2 * B + 2 * M + 4 * n + 9 := by
  simp [elementarySharedJobs, List.finRange_succ, elementarySharedJob,
    metadataCleanCost, metadataInstalled, MetadataJob.dst, MetadataJob.contents,
    hrg.eq_iff, data.width, data.mask]
  omega

end IntegerMultBounds.MathlibTM2.Routing
