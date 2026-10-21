module

public import IntegerMultBounds.MathlibTM2.M8.RevMachine.SemFamily
public import IntegerMultBounds.MathlibTM2.M8.RevMachine.RevBudget

/-!
# The stage-2 PR97 family computes the reversed interchange

`rev97_family_spec`: there is one constant `C` such that, at every atom width `b₀` and for every
`L` at least `1`, the binary length of `b₀` and `max(1, b₀)^τ`, every served frame of `n ≥ 1`
atoms with input bits `x` on `io` runs to its return address within
`(C/(1-q₁) n + C/(1-q_τ) n^τ* L)` times its volume, and exits with bits `y` on `io` that are the
reversed interchange of `x` (`RevT`).

The bound is `RevBudget`'s; the data come from the block invariants with data
(`SemFamily.semInv`), whose costs are the cost-only invariants' (`ownCost_eq`).
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8.RevMachine.RevSemantics

noncomputable section
open IntegerMultBounds.Machine
open Networks
open Networks.Shared50ModularControl (prime)
open FlatCoordinateSchedule (bits)
open RecursiveInterchangeLayout (Descriptor volume)
open Family (Frame inv)
open RevHalf (pcs Ok)
open RevBudget (ownK Meas own_le coreCost_le)
open Stage2Moments (q₁ qτ saving q₁_lt_one qτ_nonneg qτ_lt_one)

variable {k : ℕ}

/-- The program of the stage-2 PR97 family. -/
abbrev machine [M8.Machine.Net] (capacity : Fintype.card (Graph.PC (pcs rev97m).length) ≤ 2^k) :=
  Graph.program (pcs rev97m) capacity (Family.pcSlot (T := NodeBank.tapes rev97m)) Family.pcSlot_pos (impl97 k)

/-- The frames' own budgets, at one constant for every atom width. -/
theorem budget97 [M8.Machine.Net] (capacity : Fintype.card (Graph.PC (pcs rev97m).length) ≤ 2^k) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ b₀ : ℕ, ∀ L : ℝ, 1 ≤ L → ((bits b₀).length : ℝ) ≤ L →
      ((max 1 b₀ : ℕ) : ℝ) ^ M8.Machine.BudgetBound.tau ≤ L →
      (∀ σ : Frame (pcs rev97m) capacity, Ok rev97m b₀ σ → 1 ≤ σ.n → σ.n < 529 →
        (inv (Rev97Node.leafCore rev97m) Rev97Node.width97_pos (Rev97Node.half97 b₀ capacity)).ownCost σ ≤
          C * L * volume prime σ.v) ∧
      (∀ σ : Frame (pcs rev97m) capacity, Ok rev97m b₀ σ → 529 ≤ σ.n →
        (inv (Rev97Node.leafCore rev97m) Rev97Node.width97_pos (Rev97Node.half97 b₀ capacity)).ownCost σ ≤
          (C * σ.n + C * L) * volume prime σ.v) := by
  set K : ℝ := ((ownK rev97m k : ℕ) : ℝ)
  set D : ℝ := |LeafCore.C|
  have hK : 0 ≤ K := Nat.cast_nonneg _
  have hD : 0 ≤ D := abs_nonneg _
  refine ⟨530 * K + 529 * D, by positivity, fun b₀ L hL hℓ hτ => ?_⟩
  have key : ∀ σ : Frame (pcs rev97m) capacity, Ok rev97m b₀ σ → 1 ≤ σ.n →
      (inv (Rev97Node.leafCore rev97m) Rev97Node.width97_pos (Rev97Node.half97 b₀ capacity)).ownCost σ ≤
        K * ((σ.n + 1) * volume prime σ.v + L * volume prime σ.v) + 529 * D * L * volume prime σ.v := by
    intro σ hok hn
    have h := own_le runs_rev97m Rev97Node.rk97 b₀ Rev97Node.width97_pos σ hok hn
    have hw : (rev97m.width : ℝ) = 529 := by exact_mod_cast (rfl : rev97m.width = 529)
    have hc := coreCost_le (volume prime σ.v) σ.b (L := L) (by rw [hok.b]; exact hτ)
    have hV : (0 : ℝ) ≤ volume prime σ.v := Nat.cast_nonneg _
    have hM : (Meas rev97m σ : ℝ) ≤ (σ.n + 1) * volume prime σ.v + L * volume prime σ.v := by
      unfold Meas
      push_cast
      rw [hok.b]
      nlinarith
    rw [hw] at h
    calc _ ≤ _ := h
      _ ≤ _ := by nlinarith
  have hV : ∀ σ : Frame (pcs rev97m) capacity, (0 : ℝ) ≤ volume prime σ.v := fun _ => Nat.cast_nonneg _
  refine ⟨fun σ hok hn hlt => ?_, fun σ hok hn => ?_⟩
  · refine (key σ hok hn).trans ?_
    have h1 : ((σ.n : ℝ) + 1) ≤ 529 * L := by
      have : (σ.n : ℝ) + 1 ≤ 529 := by exact_mod_cast hlt
      linarith
    have := hV σ
    have h2 : ((σ.n : ℝ) + 1) * volume prime σ.v ≤ 529 * L * volume prime σ.v := mul_le_mul_of_nonneg_right h1 this
    nlinarith
  · have hn1 : 1 ≤ σ.n := le_trans (by norm_num) hn
    refine (key σ hok hn1).trans ?_
    have := hV σ
    have hLV : (volume prime σ.v : ℝ) ≤ L * volume prime σ.v := by nlinarith
    have e1 := mul_le_mul_of_nonneg_left hLV hK
    have e2 : 0 ≤ K * (L * volume prime σ.v) := by positivity
    have e3 : 0 ≤ D * (σ.n * volume prime σ.v) := by positivity
    have e4 : 0 ≤ K * (σ.n * volume prime σ.v) := by positivity
    have e5 : 0 ≤ D * (L * volume prime σ.v) := by positivity
    nlinarith

/-- **The stage-2 PR97 family computes the reversed interchange**, within the family's bound. -/
theorem rev97_family_spec [M8.Machine.Net] (capacity : Fintype.card (Graph.PC (pcs rev97m).length) ≤ 2^k) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ b₀ : ℕ, ∀ L : ℝ, 1 ≤ L → ((bits b₀).length : ℝ) ≤ L →
      ((max 1 b₀ : ℕ) : ℝ) ^ M8.Machine.BudgetBound.tau ≤ L →
      ∀ σ : Frame (pcs rev97m) capacity, Ok rev97m b₀ σ → 1 ≤ σ.n →
      ∀ x : Fin (volume prime σ.v) → ZMod 2, ∃ y : Fin (volume prime σ.v) → ZMod 2,
        RevT prime b₀ σ.n σ.v (ext x) (ext y) ∧
        ∃ s : ℕ, (s : ℝ) ≤ (C / (1 - q₁) * σ.n + C / (1 - qτ) * ((σ.n : ℝ) ^ (1 - (saving : ℝ)) * L)) *
            volume prime σ.v ∧
          run (machine capacity) s
            (Graph.entryConfig (pcs rev97m) capacity (Family.pcSlot (T := NodeBank.tapes rev97m)) Family.pcSlot_pos
              (impl97 k) .prepare (σ.at (rolesOf rev97m x) (Prepare.rest b₀ 529))) =
            some (Graph.entryConfig (pcs rev97m) capacity (Family.pcSlot (T := NodeBank.tapes rev97m))
              Family.pcSlot_pos (impl97 k) σ.ret (σ.exitAt (rolesOf rev97m y) 529)) := by
  obtain ⟨C, hC, hb⟩ := budget97 capacity
  refine ⟨C, hC, fun b₀ L hL hℓ hτ σ hok hn x => ?_⟩
  obtain ⟨hleaf, hnode⟩ := hb b₀ L hL hℓ hτ
  have hr := Schedule.ranks_schedule97
  have hcon := GraphExists.contract (ht := Family.pcSlot_pos) (semInv (capacity := capacity) b₀)
    (τ := 1 - (saving : ℝ)) (q₁ := q₁) (qτ := qτ) (C := C) (L := L)
    (show 2 ≤ 529 by norm_num) (show 0 < 108516254 by norm_num)
    (fun r h => ranks97_pos (hr ▸ h)) (fun r h => ranks97_lt (hr ▸ h))
    (by norm_num [saving]) hC (by linarith) (by exact_mod_cast q₁_lt_one) (by exact_mod_cast qτ_nonneg)
    (by exact_mod_cast qτ_lt_one) (by rw [hr]; exact_mod_cast moment₁_ranks97)
    (by rw [hr]; exact_mod_cast momentτ_ranks97)
    (fun S _ hx h1 h2 => (ownCost_eq b₀ S).le.trans (hleaf S.σ hx.1 h1 h2))
    (fun S _ hx h => (ownCost_eq b₀ S).le.trans (hnode S.σ hx.1 h)) σ.n hn ⟨σ, x⟩
    (σ.at (rolesOf rev97m x) (Prepare.rest σ.b rev97m.width)) rfl ⟨hok, rfl⟩
  obtain ⟨z, ⟨y, rfl, hT⟩, s, hs, hrun⟩ := hcon
  refine ⟨y, hok.b ▸ hT, s, hs, ?_⟩
  rw [← hok.b]
  exact hrun

end
end IntegerMultBounds.MathlibTM2.M8.RevMachine.RevSemantics
