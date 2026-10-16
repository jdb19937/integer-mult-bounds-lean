module

public import IntegerMultBounds.MathlibTM2.Mult.BandSolveList

/-! The transpose of the pivot rows into backward-pass columns, as a sliding
window. Pivots are processed in increasing order; the window holds `B` blocks of
`B` entries, block `d` holding the not yet used entries `d, d+1, …` of the row `d`
pivots back, padded with zeros. Each step emits the heads of the blocks as the
column of the current pivot, shifts the blocks, and opens a new first block with
entries `1, …, B` of the current pivot row. The emitted columns are `ucolZ`. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.BandFactor

/-- One transpose step: the column, and the next window. -/
def tStep (W : List (List ℤ)) (u : List ℤ) : List ℤ × List (List ℤ) :=
  (W.map (·.headD 0), u :: (W.dropLast.map fun blk => blk.tail++[0]))

/-- The transpose run over the row parts `us`. -/
def tRun : List (List ℤ) → List (List ℤ) → List (List ℤ)
  | _, [] => []
  | W, u :: us => (tStep W u).1 :: tRun (tStep W u).2 us

variable (B : ℕ) (Ur : List (List ℤ))

/-- The window before pivot `m`. -/
def tWin (m : ℕ) : List (List ℤ) :=
  (List.range' 1 B).map fun d => (List.range' d B).map fun e =>
    if d ≤ m ∧ e ≤ B then (Ur.getD (m-d) []).getD e 0 else 0

theorem tWin_zero : tWin B Ur 0=List.replicate B (List.replicate B 0) := by
  simp only [tWin]
  rw [List.map_congr_left (g := fun _ => List.replicate B (0 : ℤ)) fun d hd => by
    have := List.mem_range'_1.mp hd
    rw [List.map_congr_left (g := fun _ => (0 : ℤ)) fun e _ => by simp; omega]
    simp]
  simp

theorem tWin_heads (m : ℕ) : (tWin B Ur m).map (·.headD 0)=ucolZ B Ur m := by
  simp only [tWin, ucolZ, List.map_map]
  refine List.map_congr_left fun d hd => ?_
  have hd' := List.mem_range'_1.mp hd
  obtain ⟨k, hk⟩ : ∃ k, B=k+1 := ⟨B-1, by omega⟩
  simp only [Function.comp, hk, List.range'_succ, List.map_cons, List.headD_cons]
  by_cases h : d ≤ m
  · rw [ite_eq_left ⟨h, by omega⟩, ite_eq_left h]
  · rw [ite_eq_right (fun h' => h h'.1), ite_eq_right h]

theorem drop_take_eq (l : List ℤ) (hl : B+1 ≤ l.length) :
    (l.drop 1).take B=(List.range' 1 B).map fun e => l.getD e 0 := by
  refine List.ext_getElem (by simp; omega) fun n h1 h2 => ?_
  have hn : n<B := by simpa using h2
  rw [List.getElem_take, List.getElem_drop, List.getElem_map, List.getElem_range',
    List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
  simp [add_comm]

theorem tWin_step (hB : 1 ≤ B) (m : ℕ) (hrow : B+1 ≤ (Ur.getD m []).length) :
    (tStep (tWin B Ur m) (((Ur.getD m []).drop 1).take B)).2=tWin B Ur (m+1) := by
  obtain ⟨k, rfl⟩ : ∃ k, B=k+1 := ⟨B-1, by omega⟩
  simp only [tStep, tWin]
  conv_rhs => rw [show List.range' 1 (k+1)=1 :: List.range' 2 k from rfl, List.map_cons]
  rw [drop_take_eq _ _ hrow]
  congr 1
  · refine List.map_congr_left fun e he => ?_
    have := List.mem_range'_1.mp he
    rw [ite_eq_left ⟨by omega, by omega⟩, Nat.add_sub_cancel]
  · rw [← List.map_dropLast, show List.range' 1 (k+1)=List.range' 1 k++[1+k] from
      by rw [List.range'_concat, Nat.one_mul], List.dropLast_concat, List.map_map,
      show List.range' 2 k=(List.range' 1 k).map (·+1) from
        List.ext_getElem (by simp) (fun n h1 h2 => by simp; omega), List.map_map]
    refine List.map_congr_left fun d hd => ?_
    have hd' := List.mem_range'_1.mp hd
    simp only [Function.comp]
    rw [← List.map_tail, List.tail_range', show List.range' (d+1) (k+1)=List.range' (d+1) k++[d+1+k] from
      by rw [List.range'_concat, Nat.one_mul], List.map_append, List.map_singleton]
    congr 1
    · refine List.map_congr_left fun e he => ?_
      have := List.mem_range'_1.mp he
      have e1 : m+1-(d+1)=m-d := by omega
      rw [e1]
      congr 1
      simp only [eq_iff_iff]; omega
    · rw [ite_eq_right (by omega)]

/-- The transpose run emits the backward-pass columns `ucolZ` in increasing order. -/
theorem tRun_eq (hB : 1 ≤ B) : ∀ n m, (∀ j, m ≤ j → j<m+n → B+1 ≤ (Ur.getD j []).length) →
    tRun (tWin B Ur m) ((List.range' m n).map fun j => ((Ur.getD j []).drop 1).take B)=
      (List.range' m n).map (ucolZ B Ur)
  | 0, _, _ => rfl
  | n+1, m, h => by
    rw [List.range'_succ, List.map_cons, List.map_cons, tRun, tWin_step B Ur hB m (h m le_rfl (by omega)),
      tRun_eq hB n (m+1) (fun j h1 h2 => h j (by omega) (by omega))]
    simp only [tStep, tWin_heads]

end IntegerMultBounds.MathlibTM2.Mult.BandFactor
