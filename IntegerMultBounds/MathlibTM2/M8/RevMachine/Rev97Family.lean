module

public import IntegerMultBounds.MathlibTM2.M8.RevMachine.Family
public import IntegerMultBounds.MathlibTM2.M8.RevMachine.Schedule

/-!
# The stage-2 PR97 family on the machine

The control graph of `rev97m`'s schedule, with the family's concrete preparation, test, leaves
and finish, runs every frame of `n ≥ 1` atoms within `C/(1-q₁) n + C/(1-q_τ) n^τ* L` of its
volume, at `τ* = 1 - 969/10⁷` (`rev97_family`). The call ranks of the schedule are `ranks97`
(`Schedule.ranks_schedule97`), so the moment gaps are `Rev97Ranks`'. The leaf core, the node's
blocks and the frames' own budgets remain hypotheses.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8.RevMachine.Rev97Family

noncomputable section
open IntegerMultBounds.Machine
open Networks.Shared50ModularControl (prime)
open RecursiveInterchangeLayout (Descriptor volume)
open Schedule (schedule Seg Call ranks_schedule97)
open Family (count Frame LeafCore NodeBlocks NodeHalf inv)
open Global.Branching97 (roleCount)
open Stage2Moments (q₁ qτ saving q₁_lt_one qτ_nonneg qτ_lt_one)

/-- The schedule of the stage-2 PR97 node. -/
abbrev pieces97 := schedule rev97m.control

variable {T k : ℕ} {capacity : Fintype.card (Graph.PC pieces97.length) ≤ 2^k}
  {core : Graph.Block (count T) prime} {Good : Descriptor → Tapes T prime → Prop} {coreCost : ℕ → ℕ → ℕ}
  (hcore : LeafCore core Good coreCost) {N : NodeBlocks T k (Seg (rev97m.World ⊕ rev97m.Temp) 529)
    (Call (rev97m.World ⊕ rev97m.Temp))}
  (H : NodeHalf (pieces := pieces97) (capacity := capacity) N 529 roleCount Prod.snd Good)

/-- **The stage-2 PR97 family on the machine.** -/
theorem rev97_family {C L : ℝ} (hC : 0 ≤ C) (hL : 0 ≤ L)
    (hleaf : ∀ σ, H.Ok σ → σ.n < 529 → (inv hcore (by norm_num) H).ownCost σ ≤ C * L * volume prime σ.v)
    (hnode : ∀ σ, H.Ok σ → 529 ≤ σ.n →
      (inv hcore (by norm_num) H).ownCost σ ≤ (C * σ.n + C * L) * volume prime σ.v) :
    ∀ n, 1 ≤ n → GraphExists.Contract (ht := Family.pcSlot_pos) (inv hcore (by norm_num) H) n
      (C / (1 - q₁) * n + C / (1 - qτ) * ((n : ℝ) ^ (1 - (saving : ℝ)) * L)) := by
  have hr := ranks_schedule97
  refine GraphExists.contract (ht := Family.pcSlot_pos) (inv hcore (by norm_num) H) (by norm_num)
    (by norm_num [roleCount]) (fun r h => ranks97_pos (hr ▸ h)) (fun r h => ranks97_lt (hr ▸ h))
    (by norm_num [saving]) hC hL (by exact_mod_cast q₁_lt_one) (by exact_mod_cast qτ_nonneg)
    (by exact_mod_cast qτ_lt_one) ?_ ?_ (fun σ _ hx => hleaf σ hx.1) (fun σ _ hx => hnode σ hx.1)
  · rw [hr]; exact_mod_cast moment₁_ranks97
  · rw [hr]; exact_mod_cast momentτ_ranks97

end
end IntegerMultBounds.MathlibTM2.M8.RevMachine.Rev97Family
