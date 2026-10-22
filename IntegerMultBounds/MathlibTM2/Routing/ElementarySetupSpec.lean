module

public import IntegerMultBounds.MathlibTM2.Routing.ElementarySetupBank

/-! # The six-word loader establishes the actual elementary program preconditions -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.MathlibTM2.Fast

variable {t₀ T A : ℕ}
variable (R : Fin T → List (Fin (A + 4))) (rg : LayReg t₀ → Fin T)
  (hrg : Function.Injective rg) (hd : Fin 5 → Fin t₀) (src saved : Fin T)
  (hsrc : ∀ r, src ≠ rg r) (hsaved : ∀ r, saved ≠ rg r)
  (n source : ℕ) (headers : Fin 5 → List Bool) (rest : List (Fin (A + 4)))

include hrg hsrc hsaved

/-- Every register outside the mutable metadata bank and loader scratch survives. -/
theorem elementaryLoaded_keep (r : LayReg t₀) (hrt : r ≠ .tmp) (hrm : r ≠ .mB)
    (hrsw : ∀ j, r ≠ .sw j) :
    elementaryLoaded R rg hd src saved n source headers rest (rg r) = R (rg r) := by
  apply configurationBatchLoaded_keep
  · exact (hsrc r).symm
  · exact fun he => hrt (hrg he)
  · exact (hsaved r).symm
  · intro hm
    obtain ⟨slot, hs, he⟩ := List.mem_map.mp hm
    obtain ⟨key, rfl⟩ := List.mem_ofFn.mp hs
    rcases elementaryConfigTarget_role rg hd key with ⟨j, hj⟩ | hj
    · have he' : rg (.sw j) = rg r := hj.symm.trans he
      exact hrsw j (hrg he').symm
    · have he' : rg .mB = rg r := hj.symm.trans he
      exact hrm (hrg he').symm

theorem elementaryLoaded_tmp (htmp : R (rg .tmp) = []) :
    elementaryLoaded R rg hd src saved n source headers rest (rg .tmp) = [] := by
  apply configurationBatchLoaded_tmp
  · exact (hsaved .tmp).symm
  · simp
  · intro slot hs
    exact (elementaryConfigSlots_separate rg hrg hd src saved hsrc hsaved slot hs).2.1
  · exact htmp

/-- Persistent counters and masks retain their exact representation. -/
theorem elementaryLoaded_shared {M B a : ℕ} (hcfg : ElementarySharedCfg rg R n M B a) :
    ElementarySharedCfg rg (elementaryLoaded R rg hd src saved n source headers rest) n M B a := by
  apply hcfg.congr
  intro r _ hrm hrsw
  by_cases hrt : r = .tmp
  · subst r
    rw [elementaryLoaded_tmp R rg hrg hd src saved hsrc hsaved n source headers rest hcfg.tmp, hcfg.tmp]
  · exact elementaryLoaded_keep R rg hrg hd src saved hsrc hsaved n source headers rest r hrt hrm hrsw

/-- Interchange registers outside the five header destinations survive setup. -/
theorem elementaryLoaded_sw (j : Fin (swapT t₀)) (hj : ∀ k, j ≠ reg (hd k)) :
    elementaryLoaded R rg hd src saved n source headers rest (rg (.sw j)) = R (rg (.sw j)) := by
  apply configurationBatchLoaded_keep
  · exact (hsrc (.sw j)).symm
  · simp [hrg.eq_iff]
  · exact (hsaved (.sw j)).symm
  · intro hm
    obtain ⟨slot, hs, he⟩ := List.mem_map.mp hm
    obtain ⟨key, rfl⟩ := List.mem_ofFn.mp hs
    change elementaryConfigTarget rg hd key = rg (.sw j) at he
    unfold elementaryConfigTarget at he
    split_ifs at he with hk
    · exact hj ⟨key.val, hk⟩ (LayReg.sw.inj (hrg he)).symm
    · have h := hrg he
      cases h

variable (hhd : Function.Injective hd)
include hhd

theorem elementaryLoaded_header (j : Fin 5) :
    elementaryLoaded R rg hd src saved n source headers rest (rg (.sw (reg (hd j)))) =
      separator :: (headers j).map bitSymbol := by
  have h := elementaryLoaded_at R rg hrg hd hhd src saved hsrc hsaved n source headers rest
    ⟨j.val, by have := j.isLt; omega⟩
  simpa [elementaryConfigTarget, elementaryConfigWord, j.isLt] using h

theorem elementaryLoaded_mask :
    elementaryLoaded R rg hd src saved n source headers rest (rg .mB) = binSyms n (2 ^ source) := by
  have h := elementaryLoaded_at R rg hrg hd hhd src saved hsrc hsaved n source headers rest (5 : Fin 6)
  simpa [elementaryConfigTarget, elementaryConfigWord] using h

/-- The full scan precondition follows from shared setup and the executed mask load. -/
theorem elementaryLoaded_cfg {M B a : ℕ} (hcfg : ElementarySharedCfg rg R n M B a) :
    ElementaryCfg rg (elementaryLoaded R rg hd src saved n source headers rest) n M B a source :=
  ⟨elementaryLoaded_shared R rg hrg hd src saved hsrc hsaved n source headers rest hcfg,
    elementaryLoaded_mask R rg hrg hd src saved hsrc hsaved n source headers rest hhd⟩

end IntegerMultBounds.MathlibTM2.Routing
