module

public import IntegerMultBounds.Networks.Certificates.PR589.Nine.Flag
public import IntegerMultBounds.Networks.Certificates.PR589.Nine.Invocation

/-!
# Coordinate charts of data registers and hosted helpers

A register of an invocation reads its parent stream through a coordinate chart.

* **Data.** At stage `n` a data register of port `t` uses the stage route `stageRoute n`: the
  identity at stage `0` and `route (n - 1)` after. It is a symmetric involution
  (`stageRoute_mul_self`, `stageRoute_transpose`), and the window frames it conjugates are the
  lifted frames (`stageLift_eq`).
* **Hosted helpers.** The port chart `fullChart` is the orthonormal basis of the parent axes made of
  half the port's line and the flag basis, upstream's `A_q` (`fullChart_orthonormal`). The helper
  on the slot at flag position `x` uses `helperChart x`, the port chart with its columns permuted by
  `slotPerm x`: local axis `j` goes to flag position `x + j` and the other axes keep their order. It
  is orthogonal (`helperChart_orthonormal`, `helperChart_mul_transpose`), restricts to the slot
  chart on the local axes (`helperChart_local`), and carries the full local frame to the slot
  projector (`helperChart_slot`).
-/

@[expose] public section

namespace IntegerMultBounds.Networks.Certificates.PR589.Nine

open Matrix

/-! ### Chart positions -/

/-- A position of the port chart: the line, or a flag position. -/
abbrev ChartAxis := Fin 1 ⊕ Pending

/-- Chart positions in order: the line, then the flag positions. -/
def chartIndex : ChartAxis → ℕ
  | .inl _ => 0
  | .inr p => 1 + pendingIndex p

def chartAt (k : Fin 64) : ChartAxis :=
  if h : k.val = 0 then .inl 0 else .inr (pendingAt ⟨k.val - 1, by omega⟩)

theorem chartIndex_chartAt : ∀ k : Fin 64, chartIndex (chartAt k) = k.val := by
  decide +kernel

theorem chartIndex_lt : ∀ a : ChartAxis, chartIndex a < 64 := by
  decide +kernel

theorem chartIndex_injective : Function.Injective chartIndex := by
  decide +kernel

theorem axisIndex_lt' : ∀ a : Axis, axisIndex a < 64 := by
  decide +kernel

/-- The column order of the helper chart on slot position `x`: local axis `j` at `1 + x + j`, the
other axes in increasing order. -/
def slotOrder (x j : ℕ) : ℕ := if j < 8 then 1 + x + j else if j < 9 + x then j - 8 else j

theorem slotOrder_lt {x j : ℕ} (hx : x ≤ 55) (hj : j < 64) : slotOrder x j < 64 := by
  unfold slotOrder
  split_ifs <;> omega

theorem slotOrder_injective {x j j' : ℕ} (hx : x ≤ 55) (hj : j < 64) (hj' : j' < 64)
    (h : slotOrder x j = slotOrder x j') : j = j' := by
  unfold slotOrder at h
  split_ifs at h <;> omega

/-- The chart position of each parent axis in the helper chart on slot position `x`. -/
def slotPerm (x : ℕ) (hx : x ≤ 55) (a : Axis) : ChartAxis :=
  chartAt ⟨slotOrder x (axisIndex a), slotOrder_lt hx (axisIndex_lt' a)⟩

theorem slotPerm_injective (x : ℕ) (hx : x ≤ 55) : Function.Injective (slotPerm x hx) := by
  intro a b h
  have h1 := congrArg chartIndex h
  simp only [slotPerm, chartIndex_chartAt] at h1
  exact axisIndex_injective (slotOrder_injective hx (axisIndex_lt' a) (axisIndex_lt' b) h1)

theorem slotPerm_local (x : ℕ) (hx : x ≤ 55) (j : Fin 8) :
    slotPerm x hx (.inl j) = .inr (pendingAt ⟨x + j.val, by omega⟩) := by
  simp only [slotPerm, axisIndex, slotOrder, j.isLt, ite_true, chartAt]
  simp [show 1 + x + j.val - 1 = x + j.val by omega]

namespace PortCertificate

variable {c : PortCertificate}

/-- Half the port's line on the parent axes. -/
def halfLine (c : PortCertificate) : Axis → ℚ :=
  Sum.elim (fun i => (c.line i : ℚ) / 2) 0

/-- The port chart: half the line, then the flag basis. -/
def fullChart (c : PortCertificate) : Matrix Axis ChartAxis ℚ :=
  of fun a b => Sum.elim (fun _ => c.halfLine a) (fun p => c.flag a p) b

theorem fullChart_orthonormal (h : c.Checked) : c.fullChartᵀ * c.fullChart = 1 := by
  have hn := congrArg (Int.cast : ℤ → ℚ) h.1
  push_cast at hn
  have hq : ∀ k : Fin 7, ∑ i : Fin 8, (c.line i : ℚ) * c.twiceComplement i k = 0 := by
    intro k
    have := congrArg (Int.cast : ℤ → ℚ) (h.2.2.2 k)
    push_cast at this
    exact this
  have hf := flag_orthonormal h
  ext (u | p) (v | q)
  · simp only [mul_apply, transpose_apply, fullChart, of_apply, Sum.elim_inl, Sum.elim_inr,
      halfLine, Fintype.sum_sum_type, Pi.zero_apply, mul_zero, Finset.sum_const_zero, add_zero,
      one_apply, Subsingleton.elim u v, ite_true]
    calc ∑ i : Fin 8, (c.line i : ℚ) / 2 * ((c.line i : ℚ) / 2)
        = 1 / 4 * ∑ i : Fin 8, (c.line i : ℚ) * c.line i := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ => by ring
      _ = 1 := by rw [hn]; norm_num
  · simp only [mul_apply, transpose_apply, fullChart, of_apply, Sum.elim_inl, Sum.elim_inr,
      halfLine, Fintype.sum_sum_type, Pi.zero_apply, zero_mul, Finset.sum_const_zero, add_zero,
      one_apply, reduceCtorEq, ite_false]
    rcases q with k | x
    · simp only [flag, fromBlocks_apply₁₁, complement, of_apply]
      calc ∑ i : Fin 8, (c.line i : ℚ) / 2 * ((c.twiceComplement i k : ℚ) / 2)
          = 1 / 4 * ∑ i : Fin 8, (c.line i : ℚ) * c.twiceComplement i k := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun i _ => by ring
        _ = 0 := by rw [hq k]; norm_num
    · simp [flag]
  · simp only [mul_apply, transpose_apply, fullChart, of_apply, Sum.elim_inl, Sum.elim_inr,
      halfLine, Fintype.sum_sum_type, Pi.zero_apply, mul_zero, Finset.sum_const_zero, add_zero,
      one_apply, reduceCtorEq, ite_false]
    rcases p with k | x
    · simp only [flag, fromBlocks_apply₁₁, complement, of_apply]
      calc ∑ i : Fin 8, (c.twiceComplement i k : ℚ) / 2 * ((c.line i : ℚ) / 2)
          = 1 / 4 * ∑ i : Fin 8, (c.line i : ℚ) * c.twiceComplement i k := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun i _ => by ring
        _ = 0 := by rw [hq k]; norm_num
    · simp [flag]
  · have := congrFun (congrFun hf p) q
    simp only [mul_apply, transpose_apply] at this
    simp only [mul_apply, transpose_apply, fullChart, of_apply, Sum.elim_inr, one_apply,
      Sum.inr.injEq]
    rw [this, one_apply]

/-- The helper chart on slot position `x`. -/
def helperChart (c : PortCertificate) (x : ℕ) (hx : x ≤ 55) : Matrix Axis Axis ℚ :=
  of fun a b => c.fullChart a (slotPerm x hx b)

theorem helperChart_orthonormal (h : c.Checked) (x : ℕ) (hx : x ≤ 55) :
    (c.helperChart x hx)ᵀ * c.helperChart x hx = 1 := by
  ext b b'
  have := congrFun (congrFun (fullChart_orthonormal h) (slotPerm x hx b)) (slotPerm x hx b')
  simp only [mul_apply, transpose_apply] at this
  simp only [mul_apply, transpose_apply, helperChart, of_apply, this, one_apply,
    (slotPerm_injective x hx).eq_iff]

theorem helperChart_mul_transpose (h : c.Checked) (x : ℕ) (hx : x ≤ 55) :
    c.helperChart x hx * (c.helperChart x hx)ᵀ = 1 :=
  mul_eq_one_comm.mp (helperChart_orthonormal h x hx)

theorem helperChart_local (x : ℕ) (hx : x ≤ 55) :
    c.helperChart x hx * localChart = c.slotChart x := by
  ext a j
  simp only [mul_apply, helperChart, localChart, of_apply, Fintype.sum_sum_type, Sum.elim_inl,
    Sum.elim_inr, mul_zero, Finset.sum_const_zero, add_zero, mul_ite, mul_one]
  rw [Finset.sum_ite_eq']
  simp only [Finset.mem_univ, ite_true, slotPerm_local, fullChart, of_apply, Sum.elim_inr,
    slotChart, pick]
  rw [mul_apply, Fintype.sum_eq_single (pendingAt ⟨x + j.val, by omega⟩)]
  · simp [pendingIndex_pendingAt]
  · intro p hp
    have hne : pendingIndex p ≠ x + j.val := by
      intro e
      apply hp
      apply pendingIndex_injective
      rw [pendingIndex_pendingAt]
      exact e
    simp [hne]

/-- The helper chart carries the full local frame to the slot projector. -/
theorem helperChart_slot (x : ℕ) (hx : x ≤ 55) :
    c.helperChart x hx * fromBlocks 1 0 0 0 * (c.helperChart x hx)ᵀ = c.span x (x + 8) := by
  rw [← localChart_conj, ← Matrix.mul_assoc, ← Matrix.mul_assoc, helperChart_local,
    Matrix.mul_one, Matrix.mul_assoc, ← transpose_mul, helperChart_local, slotChart_proj]

/-! ### Stage routes -/

/-- The route of a data register at stage `n`. -/
def stageRoute (c : PortCertificate) (n : Fin 9) : Matrix Axis Axis ℚ :=
  if h : n.val = 0 then 1 else c.route ⟨n.val - 1, by omega⟩

theorem stageRoute_mul_self (h : c.Checked) (n : Fin 9) : c.stageRoute n * c.stageRoute n = 1 := by
  unfold stageRoute
  split_ifs
  · exact Matrix.one_mul 1
  · exact route_mul_self h _

theorem stageRoute_transpose (n : Fin 9) : (c.stageRoute n)ᵀ = c.stageRoute n := by
  unfold stageRoute
  split_ifs
  · exact transpose_one
  · exact route_transpose _

/-- The route conjugates the window frames to the lifted frames. -/
theorem stageLift_eq (n : Fin 9) (U : Matrix (Fin 8) (Fin 8) ℚ) :
    c.stageLift n U = c.stageRoute n * windowProj n U * c.stageRoute n := by
  rcases n with ⟨_ | m, hm⟩
  · simp [stageLift, stageRoute, windowProj, lower_zero]
  · simp [stageLift, stageRoute, windowProj, lift]

end PortCertificate

end IntegerMultBounds.Networks.Certificates.PR589.Nine
