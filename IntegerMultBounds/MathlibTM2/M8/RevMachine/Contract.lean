module

public import IntegerMultBounds.MathlibTM2.M8.RevMachine.Budget

/-!
# The contract of the reversed family

The recursive machine proves a contract `P n B`: on every field of `n` atoms the fixed graph
realizes the reversed interchange within `B` per unit volume. Two physical facts drive it. Below the
cutoff the leaf calls cost at most `C L` (`leaf`). Above it, a node whose block children of
`r ⌊n/m⌋` atoms meet their contracts at costs `T` meets its own at the node recurrence
(`node`). `family_contract` closes them by strong induction on the atom count: every field meets
the contract at `C/(1-q₁) n + C/(1-q_τ) n^τ L`. The cost is the recursive budget `budget`, which
obeys the recurrence with equality, so `RevMachine.family_closed` bounds it.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8.RevMachine

/-- The recursive budget: `C L` below the cutoff, the node recurrence above it. -/
noncomputable def budget (m W : ℕ) (ranks : List ℕ) (C L : ℝ) (n : ℕ) : ℝ :=
  if n < m then C * L
  else (ranks.map fun r => if r * (n / m) < n then budget m W ranks C L (r * (n / m)) / W else 0).sum +
    C * n + C * L
termination_by n
decreasing_by assumption

theorem budget_lt {m W : ℕ} {ranks : List ℕ} {C L : ℝ} {n : ℕ} (h : n < m) :
    budget m W ranks C L n = C * L := by
  rw [budget]; simp [h]

theorem budget_node {m W : ℕ} {ranks : List ℕ} {C L : ℝ} {n : ℕ} (hm : 2 ≤ m) (h : m ≤ n)
    (hle : ∀ r ∈ ranks, r < m) :
    budget m W ranks C L n =
      (ranks.map fun r : ℕ => budget m W ranks C L (r * (n / m)) / W).sum + C * n + C * L := by
  rw [budget]
  simp only [show ¬ n < m by omega, ite_false]
  congr 3
  refine List.map_congr_left fun r hr => ?_
  have hrm := hle r hr
  have h1 : 1 ≤ n / m := (Nat.one_le_div_iff (by omega)).mpr h
  have h2 : m * (n / m) ≤ n := Nat.mul_div_le _ _
  have h3 : r * (n / m) + n / m ≤ m * (n / m) := by
    rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hrm
  simp [show r * (n / m) < n by omega]

/-- **The contract of the family.** A contract that is monotone in its budget, holds below the
cutoff at `C L` and passes from the block children to the node, holds for every atom count at
`C/(1-q₁) n + C/(1-q_τ) n^τ L`. -/
theorem family_contract (P : ℕ → ℝ → Prop) (mono : ∀ n B B', P n B → B ≤ B' → P n B')
    (m W : ℕ) (hm : 2 ≤ m) (hW : 0 < W) (ranks : List ℕ)
    (hpos : ∀ r ∈ ranks, 1 ≤ r) (hle : ∀ r ∈ ranks, r < m)
    {τ q₁ qτ C L : ℝ} (hτ : 0 ≤ τ) (hC : 0 ≤ C) (hL : 0 ≤ L)
    (hq₁ : q₁ < 1) (hqτ0 : 0 ≤ qτ) (hqτ : qτ < 1)
    (hmom₁ : (ranks.map fun r : ℕ => (1 / (W : ℝ)) * ((r : ℝ) / m)).sum ≤ q₁)
    (hmomτ : (ranks.map fun r : ℕ => (1 / (W : ℝ)) * ((r : ℝ) / m) ^ τ).sum ≤ qτ)
    (leaf : ∀ n, 1 ≤ n → n < m → P n (C * L))
    (node : ∀ n, m ≤ n → ∀ T : ℕ → ℝ, (∀ r ∈ ranks, P (r * (n / m)) (T (r * (n / m)))) →
      P n ((ranks.map fun r : ℕ => T (r * (n / m)) / W).sum + C * n + C * L)) :
    ∀ n, 1 ≤ n → P n (C / (1 - q₁) * n + C / (1 - qτ) * ((n : ℝ) ^ τ * L)) := by
  have hbudget : ∀ n, 1 ≤ n → P n (budget m W ranks C L n) := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro hn
      by_cases hnm : n < m
      · rw [budget_lt hnm]; exact leaf n hn hnm
      · have h := not_lt.mp hnm
        rw [budget_node hm h hle]
        refine node n h _ fun r hr => ?_
        have hrm := hle r hr
        have h1 : 1 ≤ n / m := (Nat.one_le_div_iff (by omega)).mpr h
        have h2 : m * (n / m) ≤ n := Nat.mul_div_le _ _
        have h3 : r * (n / m) + n / m ≤ m * (n / m) := by
          rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hrm
        exact ih _ (by omega) (Nat.one_le_iff_ne_zero.mpr
          (Nat.mul_ne_zero (by have := hpos r hr; omega) (by omega)))
  have hclosed := family_closed m W hm hW ranks hpos hle (budget m W ranks C L) hτ hC hL hq₁ hqτ0
    hqτ (fun n _ hn => (budget_lt hn).le) (fun n hn => (budget_node hm hn hle).le) hmom₁ hmomτ
  intro n hn
  exact mono n _ _ (hbudget n hn) (hclosed n hn)

end IntegerMultBounds.MathlibTM2.M8.RevMachine
