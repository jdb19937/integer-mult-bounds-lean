module

public import IntegerMultBounds.MathlibTM2.Fast.CompactTopPlaced

/-! Sequential composition for actual placed call-free round stages. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.LayerMachine
open IntegerMultBounds.MathlibTM2.Node hiding LReg
noncomputable section
variable {Q A : ℕ} {U P : Type}

private theorem compactEmbExt_override {T T' : ℕ} {β : Type} (e : Fin T → Fin T')
    (f g : Fin T → β) (h : Fin T' → β) :
    embExt e f (embExt e g h)=embExt e f h := by
  funext j
  unfold embExt
  cases embInv e j <;> rfl

private theorem compactPlacedOverwrite_left {T T' : ℕ} (e : Fin T → Fin T')
    (S : Stacks T' A) (R : Fin T → List (Fin (A+4))) :
    (embOvr e ({embStk e S with R:=R}.get) S).L=S.L := by
  exact embExt_comp S.L

private theorem compactPlacedOverwrite_right {T T' : ℕ} (e : Fin T → Fin T')
    (he : Function.Injective e) (S : Stacks T' A) (R : Fin T → List (Fin (A+4))) :
    (embOvr e ({embStk e S with R:=R}.get) S).R ∘ e=R :=
  embExt_comp_e he R S.R

private theorem compactPlacedOverwrite_comp {T T' : ℕ} (e : Fin T → Fin T')
    (he : Function.Injective e) (S : Stacks T' A) (R₁ R₂ : Fin T → List (Fin (A+4))) :
    let S₁ := embOvr e ({embStk e S with R:=R₁}.get) S
    embOvr e ({embStk e S₁ with R:=R₂}.get) S₁=
      embOvr e ({embStk e S with R:=R₂}.get) S := by
  dsimp only
  simp only [embOvr,embStk,Stacks.get,embExt_comp,embExt_comp_e he,compactEmbExt_override]

/-- Compose concrete placed executions without losing the untouched compact bank. -/
theorem CompactPlacedRuns.seq
    {body : P → Pr P (nT CompactHostBReg) Q A U}
    {p q : Pr P (nT CompactHostBReg) Q A U}
    {R₀ R₁ R₂ : Fin (nT SXReg) → List (Fin (A+4))} {c₁ c₂ : ℕ}
    (h₁ : CompactPlacedRuns body p R₀ R₁ c₁)
    (h₂ : CompactPlacedRuns body q R₁ R₂ c₂) :
    CompactPlacedRuns body (.seq p q) R₀ R₂ (c₁+c₂) := by
  intro v S hL hR
  obtain ⟨v₁,k₁,hu₁,hc₁,e₁⟩ := h₁ v S hL hR
  let S₁ := embOvr compactLegacyReg ({embStk compactLegacyReg S with R:=R₁}.get) S
  obtain ⟨v₂,k₂,hu₂,hc₂,e₂⟩ := h₂ v₁ S₁
    (by intro i; rw [compactPlacedOverwrite_left]; exact hL i)
    (compactPlacedOverwrite_right compactLegacyReg compactLegacyReg_injective S R₁)
  refine ⟨v₂,k₁+k₂,hu₂.trans hu₁,Nat.add_le_add hc₁ hc₂,?_⟩
  exact Exec.cast (Exec.seq e₁ e₂) rfl
    (congrArg (mk v₂) (compactPlacedOverwrite_comp compactLegacyReg compactLegacyReg_injective S R₁ R₂))

end
end IntegerMultBounds.MathlibTM2.Fast
