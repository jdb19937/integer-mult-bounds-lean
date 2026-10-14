module

public import IntegerMultBounds.Resampling.TensorDriver

/-! Explicit cost bounds for the expansion record: one line of the `Ã`
loop costs at most `t (2m+1)` window steps of two fast multiplies and linear
work (`lineBoundF_le`). -/

@[expose] public section

namespace IntegerMultBounds.Resampling.ExpandCost
noncomputable section

open Machine Schoenhage

theorem lineBoundF_le (s t m p w W Lt : ℕ) (hwW : w ≤ W) (hst : s ≤ t) :
    LineApply.lineBoundF s t m p w W Lt ≤
      t * (2 * m + 1) * (2 * fmTime w + 300 * (W + Lt + 1)) + 300 * (t + m + 1) * (W + 1) + 4 * Lt + 500 := by
  simp only [LineApply.lineBoundF, LineApply.restBound, GaussianLine.outerBoundF, GaussianLine.bodyBoundF,
    GaussianLine.partABound, GaussianLine.rewindBodyBound]
  have h1 : t * m * w ≤ t * m * W := Nat.mul_le_mul_left _ hwW
  have h2 : t * w ≤ t * W := Nat.mul_le_mul_left _ hwW
  have h3 : s * W ≤ t * W := Nat.mul_le_mul_right _ hst
  nlinarith [Nat.zero_le (t * m * fmTime w), Nat.zero_le (t * fmTime w), Nat.zero_le (t * m * Lt),
    Nat.zero_le (t * Lt), Nat.zero_le (m * W), Nat.zero_le (t * m * W), Nat.zero_le (t * W), Nat.zero_le (t * m)]

open OrderedSelect (flat)
open GaussianLine (wordRecs)

/-- The `Ã` loop's cost on `L` lines with tables and words of the stated widths. -/
theorem progBound_le (wt arr : List (List Bool)) (s t m p w W L : ℕ) (sW tW : List Bool) (hwW : w ≤ W)
    (hst : s ≤ t) (hwt : ∀ x ∈ wt, x.length = w) (hwtl : wt.length = t * (2 * m + 1))
    (harr : arr.length = 2 * s * L) (harrw : ∀ x ∈ arr, x.length = w) :
    LineAPrim.progBound wt arr s t m p w W L sW tW ≤
      L * (t * (2 * m + 1) * (2 * fmTime w + 300 * (W + tW.length + 1)) + 300 * (t + m + 1) * (W + 1) +
        4 * tW.length + 600) +
      400 * (t * L * (W + 1)) + 20 * (t * (2 * m + 1) * (w + 1)) +
      40 * (p + W + m + s + sW.length + tW.length + L) + 1000 := by
  have hO := LineApply.outs_length wt arr s t m p w W L
  have hOw := LineAPrim.outs_width wt arr s t m p w W hwW L
  have hline := lineBoundF_le s t m p w W tW.length hwW hst
  have c1 : clen wt = t * (2 * m + 1) * (w + 1) := by rw [AxisStep.clen_uniform w wt hwt, hwtl]
  have c2 : clen arr = 2 * s * L * (w + 1) := by rw [AxisStep.clen_uniform w arr harrw, harr]
  have c3 : clen (LineApply.outs wt arr s t m p w W L) = 2 * t * L * (W + 1) := by
    rw [AxisStep.clen_uniform W _ hOw, hO]
  have f1 : (flat (wordRecs (a := 0) arr)).length = 2 * s * L * (w + 1) := by
    rw [NeumannStep.flat_wordRecs_length arr w harrw, harr]
  have f2 : (flat (wordRecs (a := 0) wt)).length = t * (2 * m + 1) * (w + 1) := by
    rw [NeumannStep.flat_wordRecs_length wt w hwt, hwtl]
  have f3 : (flat (wordRecs (a := 0) (LineApply.outs wt arr s t m p w W L))).length = 2 * t * L * (W + 1) := by
    rw [NeumannStep.flat_wordRecs_length _ W hOw, hO]
  have f4 : (msbArray (LineApply.outs wt arr s t m p w W L)).length = 2 * t * L * W := by
    rw [msbArray, List.length_flatten, List.map_map,
      List.map_congr_left (g := fun _ => W) (fun x hx => by simp [hOw x hx])]
    simp [hO]
  simp only [LineAPrim.progBound, LineAPrim.preBound, LineAPrim.postBound, LineAPrim.parLen, c1, c2, c3, f1, f2,
    f3, f4, hO]
  have hsL : s * L ≤ t * L := Nat.mul_le_mul_right _ hst
  have hsLw : s * L * w ≤ t * L * W := Nat.mul_le_mul hsL hwW
  have hsm : s - m ≤ s := Nat.sub_le _ _
  nlinarith [Nat.zero_le (L * (t * (2 * m + 1) * (2 * fmTime w + 300 * (W + tW.length + 1)))),
    Nat.mul_le_mul_left L hline, Nat.zero_le (t * L * W), Nat.zero_le (t * L), Nat.zero_le (s * L * W)]

end
end IntegerMultBounds.Resampling.ExpandCost
