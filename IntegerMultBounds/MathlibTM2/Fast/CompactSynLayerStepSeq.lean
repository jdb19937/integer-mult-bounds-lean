module

public import IntegerMultBounds.MathlibTM2.Fast.Layout

/-! Exact reassociation for assembling separately verified round stages. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Stack
variable {K : Type} {Γ : K → Type} {σ P : Type} [DecidableEq K]

 theorem compactExec_seq_assoc {body : P → Prog P Γ σ} {p q r : Prog P Γ σ}
    {s t : Store Γ σ} {n : ℕ} (h : Exec body (.seq (.seq p q) r) s n t) :
    Exec body (.seq p (.seq q r)) s n t := by
  cases h with
  | seq hpq hr =>
    cases hpq with
    | seq hp hq => simpa only [Nat.add_assoc] using Exec.seq hp (Exec.seq hq hr)

 theorem compactExec_seq_assoc_rev {body : P → Prog P Γ σ} {p q r : Prog P Γ σ}
    {s t : Store Γ σ} {n : ℕ} (h : Exec body (.seq p (.seq q r)) s n t) :
    Exec body (.seq (.seq p q) r) s n t := by
  cases h with
  | seq hp hqr =>
    cases hqr with
    | seq hq hr => simpa only [Nat.add_assoc] using Exec.seq (Exec.seq hp hq) hr

end IntegerMultBounds.MathlibTM2.Stack
namespace IntegerMultBounds.MathlibTM2.Fast
open IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
variable {T Q A : ℕ} {U P : Type}

theorem LayRuns.compact_seq_assoc {body : P → Pr P T Q A U} {p q r : Pr P T Q A U}
    {R₀ R₁ : Fin T → List (Fin (A+4))} {c : ℕ}
    (h : LayRuns body (.seq (.seq p q) r) R₀ R₁ c) :
    LayRuns body (.seq p (.seq q r)) R₀ R₁ c := by
  intro v S hL hR
  obtain ⟨v',n,hu,hc,he⟩ := h v S hL hR
  exact ⟨v',n,hu,hc,compactExec_seq_assoc he⟩

theorem LayRuns.compact_seq_assoc_rev {body : P → Pr P T Q A U} {p q r : Pr P T Q A U}
    {R₀ R₁ : Fin T → List (Fin (A+4))} {c : ℕ}
    (h : LayRuns body (.seq p (.seq q r)) R₀ R₁ c) :
    LayRuns body (.seq (.seq p q) r) R₀ R₁ c := by
  intro v S hL hR
  obtain ⟨v',n,hu,hc,he⟩ := h v S hL hR
  exact ⟨v',n,hu,hc,compactExec_seq_assoc_rev he⟩

end IntegerMultBounds.MathlibTM2.Fast
