module

public import IntegerMultBounds.MathlibTM2.Routing.ElementarySetupSpec

/-!
# Executed six-word elementary setup

The raw framed configuration is read by one fixed program. The theorem supplies
actual scan masks and interchange headers, preserves the shared counters, and
charges every input symbol. Raw-word generation and shared-counter construction
remain separate R3 obligations.
-/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.MathlibTM2.Fast

variable {t₀ T Q A : ℕ} {P U : Type}

noncomputable def elementarySetup (rg : LayReg t₀ → Fin T) (hd : Fin 5 → Fin t₀)
    (src saved : Fin T) : Pr P T Q A U :=
  configurationBatch src (rg .tmp) saved configurationIsBit (List.ofFn (elementaryConfigSlot rg hd))

/-- Executed installation supplies all per-call elementary metadata. -/
theorem elementarySetup_exec (body : P → Pr P T Q A U) (rg : LayReg t₀ → Fin T)
    (hrg : Function.Injective rg) (hd : Fin 5 → Fin t₀) (hhd : Function.Injective hd)
    (src saved : Fin T) (hss : src ≠ saved)
    (hsrc : ∀ r, src ≠ rg r) (hsaved : ∀ r, saved ≠ rg r)
    (n M B a source : ℕ) (headers : Fin 5 → List Bool) (rest : List (Fin (A + 4)))
    (v : HS T Q A U) (S : Stacks T A)
    (hcfg : ElementarySharedCfg rg S.R n M B a)
    (hempty : ∀ key, S.R (elementaryConfigTarget rg hd key) = [])
    (hinput : S.R src = configurationWords (List.ofFn (elementaryConfigWord n source headers)) ++ rest) :
    let installed := elementaryLoaded S.R rg hd src saved n source headers rest
    ∃ v', v'.user = v.user ∧
      Exec body (elementarySetup rg hd src saved) (mk v S)
        (configurationBatchCost (List.ofFn (elementaryConfigWord n source headers : Fin 6 → List (Fin (A + 4)))))
        (mk v' { S with R := installed }) ∧
      ElementaryCfg rg installed n M B a source ∧
      ∀ j, installed (rg (.sw (reg (hd j)))) = separator :: (headers j).map bitSymbol := by
  dsimp only
  obtain ⟨v', hu, he⟩ := configurationBatch_exec body src (rg .tmp) saved (hsrc .tmp) hss
    (hsaved .tmp).symm configurationIsBit configurationIsBit_separator
    (List.ofFn (elementaryConfigSlot rg hd)) (elementaryConfigSlots_nodup rg hrg hd hhd)
    (elementaryConfigSlots_separate rg hrg hd src saved hsrc hsaved)
    (List.ofFn (elementaryConfigWord n source headers)) (by simp)
    (by
      intro word hw
      obtain ⟨key, rfl⟩ := List.mem_ofFn.mp hw
      exact elementaryConfigWord_bits n source headers key)
    rest v S hinput hcfg.tmp
    (by
      intro slot hs
      obtain ⟨key, rfl⟩ := List.mem_ofFn.mp hs
      exact hempty key)
  exact ⟨v', hu, he,
    elementaryLoaded_cfg S.R rg hrg hd src saved hsrc hsaved n source headers rest hhd hcfg,
    elementaryLoaded_header S.R rg hrg hd src saved hsrc hsaved n source headers rest hhd⟩

end IntegerMultBounds.MathlibTM2.Routing
