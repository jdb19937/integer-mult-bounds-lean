module

public import IntegerMultBounds.MathlibTM2.Routing.RepairHeaderSourceFrame

/-! Erase prepared canonical row/width sources, retaining the generated headers
and every other tape. Source widths give a closed erasure bound. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host

theorem repairHeaderSourcesClean_exec {T Q A : ℕ} {P U : Type}
    (body : P → Pr P T Q A U) (bank : RepairHeaderReg → Fin T) (hbank : Function.Injective bank)
    (Lr Lw R w : ℕ) (hR : R < 2 ^ Lr) (hw : w < 2 ^ Lw)
    (v : HS T Q A U) (S : Stacks T A)
    (hrows : S.R (bank (.exchange (.base .rows))) = [])
    (htarget : S.R (bank (.exchange (.base .target))) = []) :
    ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧ m ≤ 2 * Lr + 2 * Lw + 5 ∧
      Exec body (metadataClean [bank (.exchange (.base .rows)), bank (.exchange (.base .target))])
        (mk v { S with R := repairHeaderSourceBank bank R w S.R }) m (mk v' S) := by
  let S₁ : Stacks T A := { S with R := repairHeaderSourceBank bank R w S.R }
  obtain ⟨v', hu, he⟩ := metadataClean_exec body
    [bank (.exchange (.base .rows)), bank (.exchange (.base .target))] (by simp [hbank.eq_iff]) v S₁
  have hc : metadataCleanCost S₁.R [bank (.exchange (.base .rows)), bank (.exchange (.base .target))] ≤
      2 * Lr + 2 * Lw + 5 := by
    have hr := canonicalHeader_length_le Lr R hR
    have hw' := canonicalHeader_length_le Lw w hw
    simp [metadataCleanCost, S₁, repairHeaderSourceBank, hbank.eq_iff]
    omega
  have hf : metadataCleared S₁.R [bank (.exchange (.base .rows)), bank (.exchange (.base .target))] = S.R := by
    funext i
    by_cases hr : i = bank (.exchange (.base .rows))
    · subst i; simp [metadataCleared, hrows]
    · by_cases hw' : i = bank (.exchange (.base .target))
      · subst i; simp [metadataCleared, hbank.eq_iff, htarget]
      · simp [metadataCleared, S₁, repairHeaderSourceBank, hr, hw']
  rw [hf] at he
  exact ⟨v', _, hu, hc, he⟩

end IntegerMultBounds.MathlibTM2.Routing
