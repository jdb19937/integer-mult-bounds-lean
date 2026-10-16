module

public import IntegerMultBounds.MathlibTM2.Mult.BandList
public import IntegerMultBounds.NLogN.SchurWindow
public import IntegerMultBounds.NLogN.PhaseCellFoldSolve

/-! The sliding-window factorization on integer numerators, as the tape machine
computes it on the `2^-P` grid: Newton reciprocals by truncated products,
multipliers as truncated products with the reciprocal, and row updates by
truncated products with exact subtraction. Mapped to reals it is the real
window run `factorRows` with `rdP P` and the machine multiplier rule. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.BandFactor

open IntegerMultBounds.NLogN IntegerMultBounds.NLogN.SchurDominance
open IntegerMultBounds.MathlibTM2.Mult.Sizes IntegerMultBounds.MathlibTM2.Mult.BandList

variable (P K : ℕ)

/-- Grid value of a numerator. -/
noncomputable def gv (z : ℤ) : ℝ := (z : ℝ)/2^P

/-- Newton reciprocal numerators: start `1/4`, step `r ← r(2 - c r)` with truncation. -/
def newtonZ (c : ℤ) : ℕ → ℤ
  | 0 => 2^(P-2)
  | n+1 => (newtonZ c n*(2^(P+1)-(c*newtonZ c n).tdiv (2^P))).tdiv (2^P)

theorem newtonZ_eq (hP : 2 ≤ P) (c : ℤ) : ∀ n,
    NewtonRecip.newtonR (rdP P) (gv P c) n=gv P (newtonZ P c n)
  | 0 => by
    simp only [NewtonRecip.newtonR, newtonZ, gv]
    have e : (2 : ℝ)^P=2^(P-2)*4 := by
      rw [show (4 : ℝ)=2^2 by norm_num, ← pow_add]; congr 1; omega
    push_cast
    rw [e]; field_simp
  | n+1 => by
    simp only [NewtonRecip.newtonR, newtonZ]
    rw [newtonZ_eq hP c n]
    have h1 : rdP P (gv P c*gv P (newtonZ P c n))=gv P ((c*newtonZ P c n).tdiv (2^P)) :=
      rdP_mul_grid P _ _
    rw [h1]
    have h2 : 2-gv P ((c*newtonZ P c n).tdiv (2^P))=gv P (2^(P+1)-(c*newtonZ P c n).tdiv (2^P)) := by
      simp only [gv]; push_cast; rw [pow_succ]; field_simp
    rw [h2]
    exact rdP_mul_grid P _ _

/-- Machine multiplier numerators. -/
def mulZ (a c : ℤ) : ℤ := (a*newtonZ P c K).tdiv (2^P)

theorem mulZ_eq (hP : 2 ≤ P) (a c : ℤ) :
    PhaseCellMatrix.machMul (rdP P) K (gv P a) (gv P c)=gv P (mulZ P K a c) := by
  simp only [PhaseCellMatrix.machMul, mulZ]
  rw [newtonZ_eq P hP c K]
  exact rdP_mul_grid P _ _

/-- Row update on numerators. -/
def subRowZ (l : ℤ) : List ℤ → List ℤ → List ℤ := List.zipWith (fun a b => b-(l*a).tdiv (2^P))

theorem subRowZ_map (l : ℤ) : ∀ u v : List ℤ,
    (subRowZ P l u v).map (gv P)=subRow (rdP P) (gv P l) (u.map (gv P)) (v.map (gv P))
  | [], _ => rfl
  | _::_, [] => rfl
  | a::u, b::v => by
    have ih := subRowZ_map l u v
    simp only [subRowZ, subRow, List.zipWith_cons_cons, List.map_cons] at ih ⊢
    rw [ih]
    congr 1
    have h := rdP_mul_grid P l a
    simp only [gv] at h ⊢
    rw [h]; push_cast; ring

/-- One window step on numerators. -/
def stepRowsZ (rows : List (List ℤ)) (next : List ℤ) : List (List ℤ) :=
  match rows with
  | [] => [next]
  | row::rest => (rest.map fun r => subRowZ P (mulZ P K (r.headD 0) (row.headD 0)) row.tail r.tail++[0])++[next]

/-- The multipliers of one step on numerators. -/
def lcolZ (rows : List (List ℤ)) : List ℤ :=
  match rows with
  | [] => []
  | row::rest => rest.map fun r => mulZ P K (r.headD 0) (row.headD 0)

/-- The factorization run on numerators. -/
def factorRowsZ : List (List ℤ) → List (List ℤ) → List (List ℤ × List ℤ)
  | rows, next::inputs => (lcolZ P K rows, rows.headD [])::factorRowsZ (stepRowsZ P K rows next) inputs
  | _, [] => []

theorem headD_map (r : List ℤ) : (r.map (gv P)).headD 0=gv P (r.headD 0) := by
  cases r <;> simp [gv]

theorem stepRowsZ_map (hP : 2 ≤ P) (rows : List (List ℤ)) (next : List ℤ) :
    (stepRowsZ P K rows next).map (List.map (gv P))=
      stepRows (rdP P) (PhaseCellMatrix.machMul (rdP P) K) (rows.map (List.map (gv P))) (next.map (gv P)) := by
  cases rows with
  | nil => rfl
  | cons row rest =>
    simp only [stepRowsZ, stepRows, List.map_cons, List.map_append, List.map_map, List.map_nil]
    congr 1
    refine List.map_congr_left fun r _ => ?_
    simp only [Function.comp, List.map_append, List.map_cons, List.map_nil, headD_map,
      ← mulZ_eq P K hP, ← List.map_tail, subRowZ_map]
    simp [gv]

theorem lcolZ_map (hP : 2 ≤ P) (rows : List (List ℤ)) :
    (lcolZ P K rows).map (gv P)=lcol (PhaseCellMatrix.machMul (rdP P) K) (rows.map (List.map (gv P))) := by
  cases rows with
  | nil => rfl
  | cons row rest =>
    simp only [lcolZ, lcol, List.map_cons, List.map_map]
    refine List.map_congr_left fun r _ => ?_
    simp only [Function.comp, headD_map, mulZ_eq P K hP]

/-- On the grid the numerator run is the real window run. -/
theorem factorRowsZ_map (hP : 2 ≤ P) : ∀ (inputs rows : List (List ℤ)),
    (factorRowsZ P K rows inputs).map (fun x => (x.1.map (gv P), x.2.map (gv P)))=
      factorRows (rdP P) (PhaseCellMatrix.machMul (rdP P) K) (rows.map (List.map (gv P)))
        (inputs.map (List.map (gv P)))
  | [], _ => rfl
  | next::inputs, rows => by
    simp only [factorRowsZ, factorRows, List.map_cons]
    rw [factorRowsZ_map hP inputs, stepRowsZ_map P K hP, lcolZ_map P K hP]
    congr 2
    cases rows <;> rfl

end IntegerMultBounds.MathlibTM2.Mult.BandFactor
