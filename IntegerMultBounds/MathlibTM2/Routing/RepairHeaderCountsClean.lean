module

public import IntegerMultBounds.MathlibTM2.Routing.RepairHeaderCounts
public import IntegerMultBounds.MathlibTM2.Routing.MetadataClean

/-! Erase generated header shift counts, preserving every other tape.
The original bank may already contain newly generated canonical headers. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2.Layer.CompactDigits
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget

theorem repairHeaderCountsClean_exec {T Q A : ℕ} {P U : Type}
    (body : P → Pr P T Q A U) (p : Par) (X : ℕ) (rg : HeaderCountReg → Fin T)
    (hrg : Function.Injective rg) (c : Fin 2) (v : HS T Q A U) (S : Stacks T A)
    (hwidth : ∀ f, (S.R (rg (.field f))).length = selectiveLen p X f)
    (hrow : S.R (rg .row) = []) (hgap : S.R (rg .gap) = []) :
    ∃ v', v'.user = v.user ∧
      Exec body (metadataClean [rg .row, rg .gap]) (mk v { S with R := repairHeaderCountBank rg c S.R })
        (2 * (p.wc + p.wy + X) + 5) (mk v' S) := by
  let S₁ : Stacks T A := { S with R := repairHeaderCountBank rg c S.R }
  obtain ⟨v', hu, he⟩ := metadataClean_exec body [rg .row, rg .gap]
    (by simp [hrg.eq_iff]) v S₁
  have hc : metadataCleanCost S₁.R [rg .row, rg .gap] = 2 * (p.wc + p.wy + X) + 5 := by
    fin_cases c <;> simp [metadataCleanCost, S₁, repairHeaderCountBank, repairHeaderRowFields,
      repairHeaderGapFields, hrg.eq_iff, hwidth, selectiveLen] <;> omega
  have hf : metadataCleared S₁.R [rg .row, rg .gap] = S.R := by
    funext i
    by_cases hr : i = rg .row
    · subst i; simp [metadataCleared, hrow]
    · by_cases hg : i = rg .gap
      · subst i; simp [metadataCleared, hrg.eq_iff, hgap]
      · simp [metadataCleared, S₁, repairHeaderCountBank, hr, hg]
  rw [hc, hf] at he
  exact ⟨v', hu, he⟩

end IntegerMultBounds.MathlibTM2.Routing
