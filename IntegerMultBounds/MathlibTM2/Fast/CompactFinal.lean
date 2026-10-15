module

public import IntegerMultBounds.MathlibTM2.Fast.CompactMainInputDistribution
public import IntegerMultBounds.MathlibTM2.Fast.CompactMainOutput
public import IntegerMultBounds.MathlibTM2.Fast.CompactMainChainEntry
public import IntegerMultBounds.MathlibTM2.Fast.CompactMainPrefixCost

/-! The complete concrete compact multiplier at the stronger dyadic saving. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast.Main
open IntegerMultBounds IntegerMultBounds.MathlibTM2 Filter
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
open Computability
noncomputable section

/-- Input, retuned distribution, complete arithmetic chain and canonical output. -/
def compactRetunedPrefix : CompactMnPr CompactMainProc (prime+mnKa) :=
  .seq (compactMainInputDist mn_postParam_bd) (.seq compactMainChain compactMainOutput)

/-- Exact multiplication prefix on all sufficiently long input pairs. -/
theorem compactRetunedPrefix_exec : ∀ᶠ n in atTop, ∀ x y, (pairEnc (x,y)).length=n →
    ∃ m v S, m ≤ compactRetunedPreTime 16 n ∧
      Exec (compactCompletedTable compactRetunedPrefix) compactRetunedPrefix
        (Store.only compactMainV₀ .inp (pairEnc (x,y))) m (mk v S) ∧
      S.inp=[] ∧ S.out=encodingNatBool.encode (x*y) ∧ ∀ k,S.L k=[] := by
  filter_upwards [compactMainInputDist_exec_eventually mn_postParam_bd,
    compactRetunedChain_entry_eventually,compactMainOutput_exec_eventually]
    with n hinput hchain houtput
  intro x y hxy
  have hlen := length_pairEnc x y
  have hsx : Nat.size x≤n := by omega
  have hsy : Nat.size y≤n := by omega
  let main := compactCompletedMain compactRetunedPrefix
  obtain ⟨v₁,S₁,m₁,hm₁,he₁,hi₁,ho₁,hs₁,hd₁,hmiddle⟩ := hinput main x y hxy
  obtain ⟨v₂,S₂,m₂,hm₂,he₂,hi₂,ho₂,hL₂,hdat,hframe⟩ :=
    hchain main x y hsx hsy v₁ S₁ hs₁ hd₁ hmiddle
  obtain ⟨v₃,S₃,he₃,hi₃,ho₃,hL₃⟩ :=
    houtput (compactCompletedTable compactRetunedPrefix) x y hsx hsy S₁ hd₁ hmiddle v₂ S₂ hdat hframe
  refine ⟨_,v₃,S₃,?_,he₁.seq (he₂.seq he₃),hi₃.trans (hi₂.trans hi₁),?_,?_⟩
  · have h := compactRetuned_prefix_cost_le hm₁ hm₂
    simpa only [Nat.add_assoc] using h
  · rw [ho₃,ho₂,ho₁,List.append_nil]
  · intro k
    rw [hL₃,hL₂]
    exact hs₁.1 k

/-- One fixed finite Mathlib machine multiplies every pair in worst-case time
`O(n (log n)^(1-2^-34))`. All stage costs and execution premises are discharged. -/
theorem compact_mulInTime : MulInTime ((2^34:ℝ)⁻¹) :=
  compactCompleted_mulInTime compactRetunedPrefix 16 compactRetunedPrefix_exec

end
end IntegerMultBounds.MathlibTM2.Fast.Main
