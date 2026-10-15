module

public import IntegerMultBounds.MathlibTM2.Fast.CompactDyadicParamStageCore
public import IntegerMultBounds.MathlibTM2.Fast.CompactParameterWidth
public import IntegerMultBounds.MathlibTM2.Mult.CompactDyadicRootRoom

/-! Widened-word contract for the independent dyadic parameter stage. -/
@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Fast.TableVM

open IntegerMultBounds.MathlibTM2.Mult
open IntegerMultBounds.MathlibTM2.Mult.Sizes

variable {A W w : ℕ}

/-- The widened allocation supplies both fit conditions without assumptions on the dimension. -/
theorem compactDyadicParamStage_width32 (n : ℕ) (s : TblSt pmNV A)
    (hb : s.val 1 = b n) :
    TblDo A (compactParameterWidth n) w compactDyadicParamStage s
      (fun z => z.val = compactDyadicParamVals s.val (b n) ∧ z.acc = s.acc)
      (compactDyadicParamAtoms (b n)) := by
  have hW : 4 * b n + 32 ≤ compactParameterWidth n := by
    have := pm_b_le_size n
    unfold compactParameterWidth
    omega
  apply compactDyadicParamStage_do s hb
  · exact (CompactDyadicRootRoom.squared_ninth_cap_lt (b n)).trans_le
      (Nat.pow_le_pow_right (by omega) hW)
  · have h32 : 32 ≤ compactParameterWidth n := by unfold compactParameterWidth; omega
    exact (by norm_num : 6 < 2 ^ 32).trans_le (Nat.pow_le_pow_right (by omega) h32)

end IntegerMultBounds.MathlibTM2.Fast.TableVM
