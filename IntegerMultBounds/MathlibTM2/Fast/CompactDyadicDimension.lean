module

public import IntegerMultBounds.MathlibTM2.Fast.CompactDimensionPower

/-!
# Executable dyadic dimension

Compute the sixty-fourth integer root of the ninth power, retaining the original input.
This standalone program leaves global sizing and parameter-word allocation unchanged.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Fast.TableVM

open IntegerMultBounds.MathlibTM2.Mult.Sizes

variable {A W w : ℕ}

/-- Input `0`, ninth power `1`, dimension `2`, and root-search scratch `3` through `6`. -/
def compactDyadicDimensionC : TblCode 7 :=
  compactDimensionPowerC.rename ![0, 1] ;; (pmIrootC 6).rename ![1, 2, 3, 4, 5, 6]

/-- Five power atoms plus the existing sixty-fourth-root search budget. -/
def compactDyadicDimensionAtoms (b : ℕ) : ℕ := 58 + 44 * iroot 64 (b ^ 9)

/-- Charged dimension computation, preserving the input and accumulator. -/
theorem compactDyadicDimensionC_do (st : TblSt 7 A) {b : ℕ}
    (hb : st.val 0 = b) (hW : (b ^ 9 + 1) ^ 2 < 2 ^ W) (hkW : 6 < 2 ^ W) :
    TblDo A W w compactDyadicDimensionC st
      (fun s => s.val 0 = b ∧ s.val 1 = b ^ 9 ∧
        s.val 2 = iroot 64 (b ^ 9) ∧ s.acc = st.acc)
      (compactDyadicDimensionAtoms b) := by
  have hp : b ^ 9 < 2 ^ W := by nlinarith
  have hpower := (compactDimensionPowerC_do (W := W) (w := w)
    (st.restrict ![0, 1]) (by simpa [TblSt.restrict] using hb) hp).rename
      (f := ![0, 1]) (by decide)
  refine (hpower.seq (K₂ := 53 + iroot 64 (b ^ 9) * 44)
    (fun s hs => ?_)).mono (fun _ h => h) ?_
  · have hroot := (pmIrootC_do 6 (W := W) (w := w)
      (s.restrict ![1, 2, 3, 4, 5, 6]) (by simpa [TblSt.restrict] using hs.1.2.1)
      (by simpa [sq] using hW) hkW).rename
        (f := ![1, 2, 3, 4, 5, 6]) (by decide)
    exact hroot.mono (fun z hz => ⟨
      (hz.2 0 (by decide)).trans (by simpa [TblSt.restrict] using hs.1.1),
      by simpa [TblSt.restrict] using hz.1.1,
      by simpa [TblSt.restrict] using hz.1.2.1,
      hz.1.2.2.trans hs.1.2.2⟩) le_rfl
  · simp [compactDyadicDimensionAtoms]
    omega

end IntegerMultBounds.MathlibTM2.Fast.TableVM
