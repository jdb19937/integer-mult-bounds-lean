module

public import IntegerMultBounds.MathlibTM2.Fast.ResampBCore

/-!
# Extra registers

A contract of a program on the registers `R` lifts to a larger register set `R ⊕ X`:
the extra registers keep their contents, since a run changes nothing outside the
registers of `R`. This gives the banded drivers storage registers beyond `RsbR`.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Fast

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host

variable {T Q A : ℕ} {U : Type} {P : Type} {body : P → Pr P T Q A U} {ι : Fin 64 → Fin T}
  {R X : Type}

/-- **Lift to extra registers.** -/
theorem RsbRuns.lift {rg : R ⊕ X → Fin T} (hrg : Function.Injective rg) {p : Pr P T Q A U}
    {ρ ρ' : R → List (Fin (A + 4))} {b : ℕ}
    (h : RsbRuns body (rg ∘ Sum.inl) ι p ρ ρ' b) (τ : X → List (Fin (A + 4))) :
    RsbRuns body rg ι p (Sum.elim ρ τ) (Sum.elim ρ' τ) b := by
  intro v S hc hs
  obtain ⟨v', S', n, hu, hn, he, hh, hfr⟩ := h v S hc (fun r => hs (.inl r))
  refine ⟨v', S', n, hu, hn, he, fun r => ?_, ⟨hfr.1, hfr.2.1, hfr.2.2.1, fun k hk => ?_⟩⟩
  · cases r with
    | inl r => exact hh r
    | inr x =>
      rw [hfr.2.2.2 (rg (.inr x)) (fun r e => by
        have := hrg e; cases this)]
      exact hs (.inr x)
  · exact hfr.2.2.2 k (fun r e => hk (.inl r) e)

end IntegerMultBounds.MathlibTM2.Fast
