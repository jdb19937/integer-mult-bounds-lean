module

public import IntegerMultBounds.MathlibTM2.M8.RevMachine.RevHalf
public import IntegerMultBounds.MathlibTM2.M8.RevMachine.LeafCore
public import IntegerMultBounds.MathlibTM2.M8.RevMachine.Rev97Family

/-!
# The stage-2 PR97 family with its node half

The node half of a reversed network (`half`) from `RevHalf`, the stage-1 leaf core on the I/O
role (`leafCore`), and for `rev97m` the family's contract with only the frames' own budgets as
hypotheses (`rev97_node`).
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8.RevMachine.Rev97Node

noncomputable section
open IntegerMultBounds.Machine
open Networks
open Networks.Shared50ModularControl (prime)
open SharedPlacementAlphabet (setTape)
open GraphContract (Runs ranks)
open CommonBank (bank K)
open Routines (hdr)
open RecursiveInterchangeLayout (Descriptor volume)
open NodeBank (tapes io)
open NodePark (childRoles)
open Family (Frame LeafCore NodeHalf inv)
open RevHalf (pcs Rk Ok NodeS)
open M8.Machine.ArbitraryWidthHighExchangeShared (sourceWord)

variable (N : RevNetwork)

/-- **The node half** of a reversed network. -/
def half (hR : RevRuns N) (hRk : ∀ r ∈ Rk N, 1 ≤ r ∧ r < N.width) (b₀ : ℕ) {k : ℕ}
    (capacity : Fintype.card (Graph.PC (pcs N).length) ≤ 2^k) :
    NodeHalf (pieces := pcs N) (capacity := capacity) (RevNode.blocks N k) N.width N.roleCount Prod.snd
      (RevNode.Good N) where
  Ok := Ok N b₀
  Node := NodeS N
  cSplit σ := NodeSplit.splitCost (N := N) σ.v σ.b σ.n
  cMerge σ := NodeSplit.mergeCost (N := N) σ.v σ.b σ.n
  cSeg := RevHalf.segCost N
  cCall := RevHalf.callCost N
  split σ rr hok hm hg := RevHalf.half_split σ rr hok hm hg
  seg σ y hok hm i s hi hy := RevHalf.half_seg hR σ y hok hm i s hi hy
  call σ y hok hm i c hi hy := RevHalf.half_call hRk σ y hok hm i c hi hy
  merge σ y hok hm hy := RevHalf.half_merge σ y hok hm hy

/-- **The leaf core** keeps the frames' role streams. -/
theorem leafCore [M8.Machine.Net] : LeafCore (LeafCore.core (io N)) (RevNode.Good N) LeafCore.coreCost := by
  refine ⟨Blocks.place_leading _ _ _ _, ?_⟩
  intro v u b _ hub hvol hs hhs roles f p node scalar c st hg
  obtain ⟨hpos, x, rfl⟩ := hg
  subst hhs hub
  have hupos : u.Positive := LeafCore.positive_of_volume
    (hvol ▸ RecursiveAffinePrepare.volume_positive Networks.Shared50ModularControl.prime_prime.two_le v hpos)
  set y : Fin (volume prime u) → ZMod 2 := fun i => x (Fin.cast hvol i)
  have hy : (childRoles N (RecursiveShiftRoleBank.source (Shared50RecursiveNodeSemantics.encoded x))).tape (io N) =
      sourceWord y := by
    simp only [childRoles, setTape, Function.update_self]
    exact (LeafCore.sourceWord_cast hvol x).symm
  have hh : (childRoles N (RecursiveShiftRoleBank.source (Shared50RecursiveNodeSemantics.encoded x))).head (io N) = 0 := by
    simp [childRoles, setTape]
  set z := Shared50RecursiveNodeRows.transpose (one_dvd u.rows) y
  refine ⟨_, ⟨hpos, fun i => z (Fin.cast hvol.symm i), ?_⟩,
    Blocks.runs_mono (LeafCore.core_runs _ f p node scalar c st (io N) hupos y hh hy) ?_⟩
  · simp only [childRoles, SharedPlacementAlphabet.setTape_setTape]
    congr 1
    exact (LeafCore.sourceWord_cast hvol.symm z).symm
  · rw [← hvol]
    exact LeafCore.cost_le hupos

/-! ### The stage-2 PR97 family -/

theorem rk97 : ∀ r ∈ Rk rev97m, 1 ≤ r ∧ r < rev97m.width := by
  intro r hr
  have h : Rk rev97m = ranks97 := Schedule.ranks_schedule97
  rw [h] at hr
  exact ⟨ranks97_pos hr, ranks97_lt hr⟩

theorem width97_pos : 0 < rev97m.width := by change 0 < 529; norm_num

/-- The node half of the stage-2 PR97 node at atom width `b₀`. -/
abbrev half97 (b₀ : ℕ) {k : ℕ} (capacity : Fintype.card (Graph.PC (pcs rev97m).length) ≤ 2^k) :=
  half rev97m runs_rev97m rk97 b₀ capacity

/-- **The stage-2 PR97 family with its node half**: every frame of atom width `b₀` runs within
`C/(1-q₁) n + C/(1-q_τ) n^τ* L` of its volume, given the frames' own budgets. -/
theorem rev97_node [M8.Machine.Net] (b₀ : ℕ) {k : ℕ}
    (capacity : Fintype.card (Graph.PC (pcs rev97m).length) ≤ 2^k) {C L : ℝ} (hC : 0 ≤ C) (hL : 0 ≤ L)
    (hleaf : ∀ σ, (half97 b₀ capacity).Ok σ → σ.n < 529 →
      (inv (leafCore rev97m) width97_pos (half97 b₀ capacity)).ownCost σ ≤ C * L * volume prime σ.v)
    (hnode : ∀ σ, (half97 b₀ capacity).Ok σ → 529 ≤ σ.n →
      (inv (leafCore rev97m) width97_pos (half97 b₀ capacity)).ownCost σ ≤ (C * σ.n + C * L) * volume prime σ.v) :
    ∀ n, 1 ≤ n → GraphExists.Contract (ht := Family.pcSlot_pos) (inv (leafCore rev97m) width97_pos (half97 b₀ capacity)) n
      (C / (1 - Stage2Moments.q₁) * n + C / (1 - Stage2Moments.qτ) * ((n : ℝ) ^ (1 - (Stage2Moments.saving : ℝ)) * L)) :=
  Rev97Family.rev97_family (leafCore rev97m) (half97 b₀ capacity) hC hL hleaf hnode

end
end IntegerMultBounds.MathlibTM2.M8.RevMachine.Rev97Node
