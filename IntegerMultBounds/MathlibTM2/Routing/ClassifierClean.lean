module

public import IntegerMultBounds.MathlibTM2.Routing.ClassifierPair
public import IntegerMultBounds.MathlibTM2.Routing.MetadataClean

/-! Erase both generated classifier words after repair, retaining the changed
record stream and restoring the original blank classifier destinations. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget

theorem classifierClean_exec {T Q A : ℕ} {P U : Type}
    (body : P → Pr P T Q A U) (p : Par) (rp : Fin 5 → Fin T) (hrp : Function.Injective rp)
    (src : Fin T) (htemporary : rp 3 ≠ src) (hphase : rp 4 ≠ src)
    (v : HS T Q A U) (S : Stacks T A) (records : List (Fin (A + 4)))
    (hblankTemporary : S.R (rp 3) = []) (hblankPhase : S.R (rp 4) = []) :
    ∃ v', v'.user = v.user ∧
      Exec body (metadataClean [rp 3, rp 4])
        (mk v { S with R := Function.update (classifierPairBank p rp S.R) src records })
        (4 * (p.wy + 1) + 5)
        (mk v' { S with R := Function.update S.R src records }) := by
  have houtputs : rp 3 ≠ rp 4 := hrp.ne (by decide)
  let S₁ : Stacks T A := { S with R := Function.update (classifierPairBank p rp S.R) src records }
  obtain ⟨v', hu, he⟩ := metadataClean_exec body [rp 3, rp 4]
    (by simp [houtputs]) v S₁
  have hcost : metadataCleanCost S₁.R [rp 3, rp 4] = 4 * (p.wy + 1) + 5 := by
    simp [metadataCleanCost, S₁, classifierPairBank, htemporary, hphase, houtputs]
    omega
  have hf : metadataCleared S₁.R [rp 3, rp 4] = Function.update S.R src records := by
    funext j
    by_cases ht : j = rp 3
    · subst j; simp [metadataCleared, htemporary, hblankTemporary]
    · by_cases hp : j = rp 4
      · subst j; simp [metadataCleared, hphase, hblankPhase, houtputs.symm]
      · by_cases hs : j = src
        · subst j; simp [metadataCleared, S₁, ht, hp]
        · simp [metadataCleared, S₁, classifierPairBank, ht, hp, hs]
  rw [hcost, hf] at he
  exact ⟨v', hu, he⟩

end IntegerMultBounds.MathlibTM2.Routing
