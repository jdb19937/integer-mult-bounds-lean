module

public import IntegerMultBounds.MathlibTM2.Fast.ParamSub

/-!
# Ninth power for the compact dimension parameter

The program preserves its input in variable `0` and computes its ninth power in variable `1`.
Three squarings and a final multiplication follow one copy, for five table atoms. The explicit
word-fit premise keeps this helper independent of the eventual parameter-word allocation.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Fast.TableVM

variable {A W w : ℕ}

/-- Preserve `x` in `0` and place `x^9` in `1`. -/
def compactDimensionPowerC : TblCode 2 :=
  tblBlock 2 [.copy 0 1, .mul 1 1 1, .mul 1 1 1, .mul 1 1 1] (.mul 1 0 1)

/-- The complete input/output frame and charged execution of the ninth-power helper. -/
theorem compactDimensionPowerC_do (st : TblSt 2 A) {x : ℕ}
    (hx : st.val 0 = x) (hW : x ^ 9 < 2 ^ W) :
    TblDo A W w compactDimensionPowerC st
      (fun s => s.val 0 = x ∧ s.val 1 = x ^ 9 ∧ s.acc = st.acc) 5 := by
  have hp (k : ℕ) (hk : 1 ≤ k) (hk9 : k ≤ 9) : x ^ k < 2 ^ W := by
    by_cases hx0 : x = 0
    · simp [hx0, Nat.ne_of_gt hk]
    · exact (Nat.pow_le_pow_right (by omega : 1 ≤ x) hk9).trans_lt hW
  have h2 := hp 2 (by omega) (by omega)
  have h4 := hp 4 (by omega) (by omega)
  have h8 := hp 8 (by omega) (by omega)
  have e2 : x * x = x ^ 2 := by ring
  have e4 : x ^ 2 * x ^ 2 = x ^ 4 := by ring
  have e8 : x ^ 4 * x ^ 4 = x ^ 8 := by ring
  have e9 : x ^ 8 * x = x ^ 9 := by ring
  refine TblDo.block _ _ ?_ ?_
  · simp [tblFitsList, TblIns.fits, TblIns.exact, hx, e2, e4, e8, e9,
      h2, h4, h8, hW]
  · simp [tblExactList, TblIns.exact, hx, e2, e4, e8, e9]

end IntegerMultBounds.MathlibTM2.Fast.TableVM
