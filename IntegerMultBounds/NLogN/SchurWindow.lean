module

public import IntegerMultBounds.NLogN.SchurStages

/-! Banded elimination with a sliding window, as the tape machine runs it. For a
band of half width `B` in natural order, the active part of stage `k` lives in
rows `k, …, k+B`, each needed on columns `k, …, k+2B`. One step takes the head
row as pivot row, forms each later row's multiplier, subtracts the rounded
products, drops the pivot column, appends a zero and appends the next input row.
The window after the step is the window of the next stage matrix. -/
@[expose] public section
namespace IntegerMultBounds.NLogN.SchurDominance

variable (rd : ℝ → ℝ) (mul : ℝ → ℝ → ℝ) (B : ℕ)

/-- Row `i` of `M` on columns `k, …, k+2B`. -/
def winRow (M : Matrix ℕ ℕ ℝ) (k i : ℕ) : List ℝ := (List.range' k (2*B+1)).map (M i)

/-- Rows `k, …, k+B` of `M` on columns `k, …, k+2B`. -/
def window (M : Matrix ℕ ℕ ℝ) (k : ℕ) : List (List ℝ) := (List.range' k (B+1)).map (winRow B M k)

/-- Subtract rounded multiples of the pivot row. -/
def subRow (l : ℝ) : List ℝ → List ℝ → List ℝ := List.zipWith (fun a b => b-rd (l*a))

/-- One window step: eliminate with the head row, shift, append the next row. -/
def stepRows (rows : List (List ℝ)) (next : List ℝ) : List (List ℝ) :=
  match rows with
  | [] => [next]
  | row::rest => (rest.map fun r => subRow rd (mul (r.headD 0) (row.headD 0)) row.tail r.tail++[0])++[next]

/-- The multipliers of one step. -/
def lcol (rows : List (List ℝ)) : List ℝ :=
  match rows with
  | [] => []
  | row::rest => rest.map fun r => mul (r.headD 0) (row.headD 0)

/-- Band of half width `B` on the active part from `k` on. -/
def BandFrom (M : Matrix ℕ ℕ ℝ) (k : ℕ) : Prop :=
  ∀ i j, k ≤ i → k ≤ j → M i j≠0 → i ≤ j+B ∧ j ≤ i+B

theorem winRow_cons (M : Matrix ℕ ℕ ℝ) (k i : ℕ) :
    winRow B M k i=M i k::(List.range' (k+1) (2*B)).map (M i) := by
  simp [winRow, List.range'_succ]

theorem range'_snoc (a n : ℕ) : List.range' a (n+1)=List.range' a n++[a+n] := by
  rw [List.range'_concat, Nat.one_mul]

theorem subRow_map (l : ℝ) (M : Matrix ℕ ℕ ℝ) (k i : ℕ) (xs : List ℕ) :
    subRow rd l (xs.map (M k)) (xs.map (M i))=xs.map fun j => M i j-rd (l*M k j) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [subRow, List.zipWith_cons_cons] at ih ⊢

variable (hrd0 : rd 0=0) (hmul0 : ∀ c, mul 0 c=0)
include hrd0 hmul0

/-- A step turns the window of stage `k` into the window of stage `k+1`. -/
theorem stepRows_window (M : Matrix ℕ ℕ ℝ) (k : ℕ) (hM : BandFrom B M k) :
    stepRows rd mul (window B M k) (winRow B M (k+1) (k+B+1))=window B (relim rd mul M k) (k+1) := by
  have hrow : ∀ i, k+1 ≤ i → i ≤ k+B →
      subRow rd (mul (M i k) (M k k)) ((List.range' (k+1) (2*B)).map (M k))
        ((List.range' (k+1) (2*B)).map (M i))++[0]=winRow B (relim rd mul M k) (k+1) i := by
    intro i hi1 hi2
    rw [subRow_map]
    have hz1 : M i (k+1+2*B)=0 := by
      by_contra h; have := hM i (k+1+2*B) (by omega) (by omega) h; omega
    have hz2 : M k (k+1+2*B)=0 := by
      by_contra h; have := hM k (k+1+2*B) (by omega) (by omega) h; omega
    rw [winRow, range'_snoc, List.map_append, List.map_cons, List.map_nil]
    congr 1
    simp only [relim, hz1, hz2, mul_zero, hrd0, sub_zero]
  have hlast : winRow B M (k+1) (k+B+1)=winRow B (relim rd mul M k) (k+1) (k+B+1) := by
    have hz : M (k+B+1) k=0 := by
      by_contra h; have := hM (k+B+1) k (by omega) le_rfl h; omega
    refine List.map_congr_left fun j _ => ?_
    simp only [relim, hz, hmul0, zero_mul, hrd0, sub_zero]
  have e1 : List.range' k (B+1)=k::List.range' (k+1) B := List.range'_succ ..
  rw [window, window, e1, range'_snoc, List.map_cons, List.map_append, List.map_cons, List.map_nil,
    winRow_cons B M k k]
  simp only [stepRows, List.headD_cons, List.tail_cons]
  rw [show k+1+B=k+B+1 by omega, ← hlast]
  congr 1
  rw [List.map_map]
  refine List.map_congr_left fun i hi => ?_
  have hi' := List.mem_range'_1.mp hi
  simp only [Function.comp, winRow_cons, List.headD_cons, List.tail_cons]
  exact hrow i (by omega) (by omega)

omit hrd0 hmul0 in
/-- The multipliers of a step are the eliminated column. -/
theorem lcol_window (M : Matrix ℕ ℕ ℝ) (k : ℕ) :
    lcol mul (window B M k)=(List.range' (k+1) B).map fun i => mul (M i k) (M k k) := by
  simp only [window, List.range'_succ, List.map_cons, lcol, winRow_cons, List.headD_cons, List.map_map]
  rfl

/-- Elimination keeps the band on the remaining active part. -/
theorem bandFrom_relim (M : Matrix ℕ ℕ ℝ) (k : ℕ) (hM : BandFrom B M k) :
    BandFrom B (relim rd mul M k) (k+1) := by
  intro i j hi hj h
  simp only [relim] at h
  by_cases hij : M i j=0
  · rw [hij, zero_sub, neg_ne_zero] at h
    have hik : M i k≠0 := by
      intro h0; apply h; rw [h0, hmul0, zero_mul, hrd0]
    have hkj : M k j≠0 := by
      intro h0; apply h; rw [h0, mul_zero, hrd0]
    have h1 := hM i k (by omega) le_rfl hik
    have h2 := hM k j le_rfl (by omega) hkj
    omega
  · exact hM i j (by omega) (by omega) hij

omit hrd0 hmul0 in
/-- The factorization run: each step emits its multipliers and pivot row. -/
def factorRows : List (List ℝ) → List (List ℝ) → List (List ℝ × List ℝ)
  | rows, next::inputs => (lcol mul rows, rows.headD [])::factorRows (stepRows rd mul rows next) inputs
  | _, [] => []

/-- Stages stay banded. -/
theorem bandFrom_stg (A : Matrix ℕ ℕ ℝ) (hA : BandFrom B A 0) : ∀ k, BandFrom B (stg rd mul A 0 k) k
  | 0 => hA
  | k+1 => by
    have := bandFrom_relim rd mul B hrd0 hmul0 _ k (bandFrom_stg A hA k)
    simpa [stg] using this

/-- Rows beyond the window are still the input rows. -/
theorem stg_far (A : Matrix ℕ ℕ ℝ) (hA : BandFrom B A 0) : ∀ k i j, k+B ≤ i →
    stg rd mul A 0 k i j=A i j
  | 0, _, _, _ => rfl
  | k+1, i, j, hi => by
    have hz : stg rd mul A 0 k i k=0 := by
      by_contra h
      have := bandFrom_stg rd mul B hrd0 hmul0 A hA k i k (by omega) le_rfl h
      omega
    simp only [stg, zero_add, relim, hz, hmul0, zero_mul, hrd0, sub_zero]
    exact stg_far A hA k i j (by omega)

/-- The full run emits, for each pivot, the eliminated column and the pivot row
of its stage matrix. -/
theorem factorRows_run (A : Matrix ℕ ℕ ℝ) (hA : BandFrom B A 0) : ∀ n k,
    factorRows rd mul (window B (stg rd mul A 0 k) k)
        ((List.range' k n).map fun m => winRow B A (m+1) (m+B+1))=
      (List.range' k n).map fun m => ((List.range' (m+1) B).map fun i =>
        mul (stg rd mul A 0 m i m) (stg rd mul A 0 m m m), winRow B (stg rd mul A 0 m) m m)
  | 0, _ => rfl
  | n+1, k => by
    have hin : winRow B A (k+1) (k+B+1)=winRow B (stg rd mul A 0 k) (k+1) (k+B+1) :=
      List.map_congr_left fun j _ => (stg_far rd mul B hrd0 hmul0 A hA k _ j (by omega)).symm
    rw [List.range'_succ, List.map_cons, List.map_cons, factorRows, hin,
      stepRows_window rd mul B hrd0 hmul0 _ k (bandFrom_stg rd mul B hrd0 hmul0 A hA k),
      lcol_window]
    have e : relim rd mul (stg rd mul A 0 k) k=stg rd mul A 0 (k+1) := by simp [stg]
    rw [e, factorRows_run A hA n (k+1)]
    simp [window, List.range'_succ]

end IntegerMultBounds.NLogN.SchurDominance
