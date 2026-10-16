module

public import IntegerMultBounds.Resampling.TabledMaps
public import IntegerMultBounds.MathlibTM2.Fast.CMulArith
public import IntegerMultBounds.Resampling.RowSelect

/-!
# Integer line maps of `B̃₀`

Grid values `rsbGrid p N = N / 2^p` and their rounded products (`rhoC_mul_rsbGrid`), real
Gaussian integers `rsbReal`, the window offsets `rsbHs m`, the row selection and halving
`rsbHalf`, the integer Horner steps `rsbStep`, `rsbIter`, `rsbLineNum`, the row mask
`rsbMask` (`rsb_filter_mask`) and arrays as lists `rsbArr`.

The identification with the Neumann map `resampB₀NumK` (`rsb_resampB₀NumK`,
`rsbLineNum_eq_numer`, `rsb_iter_ball`) was removed with the Neumann `B̃₀`; restore from
`1cb2723b`.
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2.Fast

open IntegerMultBounds IntegerMultBounds.NLogN
open IntegerMultBounds.Resampling.OffDiagSum (offTermW)
open IntegerMultBounds.Resampling.TabledMaps (diagW)

noncomputable section

/-- The grid value `N / 2^p`. -/
def rsbGrid (p : ℕ) (N : GaussianInt) : ℂ := GaussianInt.toComplex N / 2 ^ p

/-- The real Gaussian integer `x + 0 i`. -/
def rsbReal (x : ℤ) : GaussianInt := ⟨x, 0⟩

/-- The off-diagonal window offsets `-m, …, -1, 1, …, m`, in increasing order. -/
def rsbHs (m : ℕ) : List ℤ :=
  (List.range m).map (fun i : ℕ => (i : ℤ) - m) ++ (List.range m).map (fun i : ℕ => (i : ℤ) + 1)

/-! ### Grid values -/

/-- The rounded product of two grid values. -/
lemma rhoC_mul_rsbGrid (p : ℕ) (a b : GaussianInt) :
    rhoC p (rsbGrid p a * rsbGrid p b) = rsbGrid p (tdivN p (a * b)) :=
  rhoC_mul_grid p a b

/-! ### The integer line map -/

variable {s t : ℕ} [NeZero s] [NeZero t]

/-- Row selection and halving: `tdivN 1 (N (rowIndex s t ℓ))`. -/
def rsbHalf (N : ZMod t → GaussianInt) : ZMod s → GaussianInt :=
  fun ℓ => tdivN 1 (N (rowIndex s t ℓ))

/-- One integer Horner step `V ↦ H - Ẽ V`. -/
def rsbStep (p m : ℕ) (E : ZMod s → ℤ → ℤ) (H V : ZMod s → GaussianInt) : ZMod s → GaussianInt :=
  fun ℓ => H ℓ - ((rsbHs m).map fun h : ℤ => tdivN p (V (ℓ + (h : ZMod s)) * rsbReal (E ℓ h))).sum

/-- `k` integer Horner steps from `H`. -/
def rsbIter (p m : ℕ) (E : ZMod s → ℤ → ℤ) (H : ZMod s → GaussianInt) :
    ℕ → ZMod s → GaussianInt
  | 0 => H
  | k + 1 => rsbStep p m E H (rsbIter p m E H k)

/-- The numerators of `B̃₀` on one line. -/
def rsbLineNum (p K m : ℕ) (E : ZMod s → ℤ → ℤ) (D : ZMod s → ℤ) (N : ZMod t → GaussianInt) :
    ZMod s → GaussianInt :=
  fun ℓ => tdivN p (rsbIter p m E (rsbHalf N) K ℓ * rsbReal (D ℓ))

/-! ### The selection mask -/

/-- Bit `j < t`: `j` is the row index of some `ℓ < s`. -/
def rsbMask (s t : ℕ) : List Bool :=
  (List.range t).map fun j : ℕ => decide (∃ ℓ < s, Resampling.RowSelect.q s t ℓ = j)

omit [NeZero s] [NeZero t] in
lemma length_rsbMask (s t : ℕ) : (rsbMask s t).length = t := by simp [rsbMask]

/-- The array `V` as the list of its entries `0, …, n - 1`. -/
def rsbArr {n : ℕ} {α : Type*} (V : ZMod n → α) : List α :=
  (List.range n).map fun i : ℕ => V (i : ZMod n)

omit [NeZero s] [NeZero t] in
lemma length_rsbArr {n : ℕ} {α : Type*} (V : ZMod n → α) : (rsbArr V).length = n := by
  simp [rsbArr]

omit [NeZero t] in
/-- The selected entries of a line are the row-selected ones. -/
theorem rsb_filter_mask (hst : s < t) {α : Type*} (N : ZMod t → α) :
    (((rsbArr N).zip (rsbMask s t)).filter (·.2)).map (·.1) =
      rsbArr fun ℓ : ZMod s => N (rowIndex s t ℓ) := by
  have hs : 0 < s := Nat.pos_of_ne_zero (NeZero.ne s)
  have hz : (rsbArr N).zip (rsbMask s t) =
      (List.range t).map fun j : ℕ =>
        (N (j : ZMod t), decide (∃ ℓ < s, Resampling.RowSelect.q s t ℓ = j)) := by
    apply List.ext_getElem (by simp [rsbArr, rsbMask])
    intro i h1 h2
    simp [rsbArr, rsbMask]
  rw [hz, List.filter_map, List.map_map]
  have hf := Resampling.RowSelect.filter_range_eq_map (Resampling.RowSelect.q s t) s t
    (fun j k hjk _ => Resampling.RowSelect.q_strictMono s t j k hs hst hjk)
    (fun j hj => Resampling.RowSelect.q_lt s t j hs hst hj)
  have e : ((fun x : α × Bool => x.2) ∘ fun j : ℕ =>
      (N (j : ZMod t), decide (∃ ℓ < s, Resampling.RowSelect.q s t ℓ = j))) =
      fun j : ℕ => decide (∃ ℓ < s, Resampling.RowSelect.q s t ℓ = j) := rfl
  rw [e, hf, List.map_map, rsbArr]
  apply List.map_congr_left
  intro ℓ hℓ
  rw [List.mem_range] at hℓ
  simp only [Function.comp_apply, rowIndex]
  rw [Resampling.RowSelect.rowIndexNat_eq s t ℓ hs hℓ]


end

end IntegerMultBounds.MathlibTM2.Fast
