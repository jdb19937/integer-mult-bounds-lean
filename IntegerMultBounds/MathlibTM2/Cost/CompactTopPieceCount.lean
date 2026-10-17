module

import IntegerMultBounds.MathlibTM2.Cost.MatchSynPcs
public import IntegerMultBounds.MathlibTM2.Fast.CompactTopSelection
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Log.Base

/-! The actual compact top emits at most one back-reservation record plus
one record per nonzero base-m digit. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
open IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.LayerMachine
open IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast

/-- The actual reserved record count is logarithmic in original dimension,
even when there are no active digits or no back reservation. -/
theorem compactTopPcs_length_log (d g K D o R₂ : ℕ) (hd : 1≤d) (hD : D≤d) :
    ((compactTopPcs d g K D o R₂).length:ℝ) ≤ 2+Real.logb (m:ℝ) d := by
  let active := compactReservationActive d g K D
  let J := CompactGlobalRowPadding.depth m d
  have ha : active≤d := by
    dsimp only [active,compactReservationActive]
    omega
  have hlen := mrP_length_synPcs_le K 0 active (o+K*CompactGadgetReservationCapacity.backChunks d g K) J active
  have hlog := mrP_synJ_le (D := active) (dd := (d:ℝ)) (by exact_mod_cast ha) (by exact_mod_cast hd)
  have hback : (compactReservedPcs K 0 o (CompactGadgetReservationCapacity.backChunks d g K)
      (o+K*CompactGadgetReservationCapacity.backChunks d g K) J active).length ≤
      1+(synPcs K 0 active (o+K*CompactGadgetReservationCapacity.backChunks d g K) J active).length := by
    unfold compactReservedPcs
    split_ifs <;> simp only [List.length_append,List.length_nil,List.length_cons] <;> omega
  have hn : (compactTopPcs d g K D o R₂).length≤1+synJ active active := by
    unfold compactTopPcs
    rw [List.length_map]
    exact hback.trans (Nat.add_le_add_left hlen 1)
  have hr : ((compactTopPcs d g K D o R₂).length:ℝ)≤1+(synJ active active:ℝ) := by
    exact_mod_cast hn
  linarith only [hr,hlog]

end IntegerMultBounds.MathlibTM2.Cost
