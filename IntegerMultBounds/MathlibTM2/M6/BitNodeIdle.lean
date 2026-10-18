module

public import IntegerMultBounds.MathlibTM2.M6.BitNodeSteps

/-!
# Idles and bridges keep the frame bookkeeping

* `idle_step`: at idle `i`, a role of its pair holds the line, the prefix of `7a` positions and all
  of its copy's hosted slots, the prefix of `7a + 8k` positions; the remainder child adds the rest
  of the pending interval, up to `7b`.
* `bridge_step`: the two roles a bridge joins are in equal frames, with nothing pending, so the
  sum of their streams is the sum of their logical streams.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M6.BitNode

open IntegerMultBounds.Networks.Certificates.PR589
open IntegerMultBounds.Networks.Certificates.PR589.Nine
open IntegerMultBounds.MathlibTM2.M6.BitHosting
open Matrix

theorem idlePos_le : ∀ i < 10, idlePos i + 1 ≤ 29 := by
  decide +kernel

theorem idle_nine_slots : ∀ σ ∈ slots, σ.idle < 9 := fun σ hσ => (slot_fits σ hσ).1

theorem copyCount_nine (c : ℕ) : copyCount 9 c = 0 := by
  simp [copyCount, copyCounts, BitOccurrences.patterns]

theorem idle_levels_le : ∀ i < 10, idleSource i ≤ idleTarget i ∧ idleTarget i ≤ 9 := by
  decide +kernel

/-- The frame of a role of idle `i`'s pair, at the idle. -/
theorem frame_at_idle (i : ℕ) (hi : i < 10) (ρ : Role) (hρ : ρ.bank.val / 2 = pairOf i) :
    frameAt (idlePos i) ρ =
      sidePart ρ + (port ρ.port.val).span 0 (7 * idleSource i + 8 * copyCount i (roleCopy ρ)) := by
  have hif := idle_facts i hi
  have hsum : pendingSum (idlePos i) ρ =
      (slots.map fun σ => if σ.idle = i ∧ σ.copy = roleCopy ρ then slotSpan ρ σ else 0).sum := by
    rw [pendingSum]
    apply sum_ite_congr
    intro σ hσ
    constructor
    · rintro ⟨⟨hp, hc⟩, hpend⟩
      exact ⟨((idle_pending σ hσ i hi).1 (hp.trans hρ)).mp hpend, hc⟩
    · rintro ⟨rfl, hc⟩
      exact ⟨⟨hρ.symm, hc⟩, ((idle_pending σ hσ _ hi).1 rfl).mpr rfl⟩
  rw [frameAt, hρ, hif.1, hsum, add_assoc]
  congr 1
  rcases Nat.lt_or_ge i 9 with h9 | h9
  · rw [idle_slot_sum ρ i h9, PortCertificate.span_add (Nat.zero_le _) (by omega)]
  · have : i = 9 := by omega
    subst this
    rw [sum_ite_none _ _ _ (fun σ hσ h => absurd h.1 (by have := idle_nine_slots σ hσ; omega)),
      copyCount_nine, add_zero, mul_zero, add_zero]

theorem idle_step (i : ℕ) (hi : i < 10) (X L : State) (h : Inv (idlePos i) X L) :
    Inv (idlePos i + 1) ((Piece.remainder i).run X) L := by
  intro ρ
  have hif := idle_facts i hi
  have hq : ρ.bank.val / 2 < 4 := by have := ρ.bank.isLt; omega
  simp only [Piece.run]
  by_cases hρ : ρ.bank.val / 2 = pairOf i
  · rw [ite_eq_left hρ, h, frame_at_idle i hi ρ hρ]
    have hk : 7 * idleSource i + 8 * copyCount i (roleCopy ρ) ≤ 7 * idleTarget i := by
      rcases Nat.lt_or_ge i 9 with h9 | h9
      · exact ((copyCount_fit i h9).2 _ (roleCopy_lt ρ)).2 |> fun h' => by
          have := ((copyCount_fit i h9).2 _ (roleCopy_lt ρ)).1; omega
      · have : i = 9 := by omega
        subst this
        rw [copyCount_nine]
        have := idle_levels_le 9 (by norm_num)
        omega
    have horth : (sidePart ρ + (port ρ.port.val).span 0 (7 * idleSource i + 8 * copyCount i (roleCopy ρ))) *
        remainderSpan i ρ = 0 := by
      rw [remainderSpan, Matrix.add_mul, sidePart_mul_span, zero_add]
      exact PortCertificate.span_mul_disjoint (port_ok ρ) le_rfl
    rw [along_frame_add _ _ horth, remainderSpan, add_assoc,
      PortCertificate.span_add (Nat.zero_le _) hk]
    have hnone : pendingSum (idlePos i + 1) ρ = 0 := by
      apply pendingSum_none
      intro σ hσ hf hp
      have hp' := (idle_pending σ hσ i hi).2.mp hp
      exact hp'.2 (((idle_pending σ hσ i hi).1 (hf.1.trans hρ)).mp hp'.1)
    rw [frameAt, hnone, add_zero, hρ, hif.2.1]
  · have hlev := hif.2.2 _ hq hρ
    have hpend : pendingSum (idlePos i + 1) ρ = pendingSum (idlePos i) ρ := by
      rw [pendingSum, pendingSum]
      apply sum_ite_congr
      intro σ hσ
      rw [(idle_pending σ hσ i hi).2]
      constructor
      · exact fun ⟨hf, hp, _⟩ => ⟨hf, hp⟩
      · rintro ⟨hf, hp⟩
        refine ⟨hf, hp, ?_⟩
        rintro rfl
        exact hρ hf.1.symm
    have hframe : frameAt (idlePos i + 1) ρ = frameAt (idlePos i) ρ := by
      rw [frameAt, frameAt, hlev, hpend]
    rw [ite_eq_right hρ, h, hframe]

/-! ### Bridges -/

theorem bridge_step (τ : ℕ) (hτ : τ < 29) (d s : ℕ) (hb : bridgeAt τ = some (d, s)) (X L : State)
    (h : Inv τ X L) : Inv (τ + 1) ((Piece.bridge d s).run X) (logicalStep (.bridge d s) L) := by
  intro ρ
  obtain ⟨hd, hs⟩ := bridge_pairs τ hτ _ hb
  obtain ⟨hds, hlev, hlev'⟩ := bridge_facts τ hτ d hd s hs hb
  have hτ' : τ + 1 ≤ 29 := hτ
  have hframe : ∀ ρ' : Role, frameAt (τ + 1) ρ' = frameAt τ ρ' := by
    intro ρ'
    have hq : ρ'.bank.val / 2 < 4 := by have := ρ'.bank.isLt; omega
    have hpend : pendingSum (τ + 1) ρ' = pendingSum τ ρ' := by
      rw [pendingSum, pendingSum]
      apply sum_ite_congr
      intro σ hσ
      rw [(bridge_pending σ hσ τ hτ _ hb).2]
    rw [frameAt, frameAt, hlev' _ hq, hpend]
  have hjoin : ∀ ρ₁ ρ₂ : Role, ρ₁.port = ρ₂.port → ρ₁.bank.val % 2 = ρ₂.bank.val % 2 →
      (ρ₁.bank.val / 2 = d ∨ ρ₁.bank.val / 2 = s) → (ρ₂.bank.val / 2 = d ∨ ρ₂.bank.val / 2 = s) →
      frameAt τ ρ₁ = frameAt τ ρ₂ := by
    intro ρ₁ ρ₂ hp hside h1 h2
    have hn : ∀ ρ' : Role, (ρ'.bank.val / 2 = d ∨ ρ'.bank.val / 2 = s) →
        ∀ σ ∈ slots, OfFamily ρ' σ → ¬Pending τ σ := by
      intro ρ' h' σ hσ hf
      apply (bridge_pending σ hσ τ hτ _ hb).1
      rcases h' with h' | h'
      · exact Or.inl (hf.1.trans h')
      · exact Or.inr (hf.1.trans h')
    rw [frameAt_level τ ρ₁ (hn ρ₁ h1), frameAt_level τ ρ₂ (hn ρ₂ h2), hp, hside]
    have : levelAt τ (ρ₁.bank.val / 2) = levelAt τ (ρ₂.bank.val / 2) := by
      rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> rw [h1, h2] <;> first | rfl | exact hlev | exact hlev.symm
    rw [this]
  simp only [Piece.run, logicalStep]
  rw [hframe]
  split_ifs with h2d h2s
  · obtain ⟨hb', hp', -, -⟩ := withBank_other ρ (2 * s) (by omega)
    rw [h, h (withBank ρ (2 * s)), hjoin (withBank ρ (2 * s)) ρ hp' (by omega) (by omega) (by omega),
      map_add]
  · obtain ⟨hb', hp', -, -⟩ := withBank_other ρ (2 * d + 1) (by omega)
    rw [h, h (withBank ρ (2 * d + 1)),
      hjoin (withBank ρ (2 * d + 1)) ρ hp' (by omega) (by omega) (by omega), map_add]
  · exact h ρ

end IntegerMultBounds.MathlibTM2.M6.BitNode
