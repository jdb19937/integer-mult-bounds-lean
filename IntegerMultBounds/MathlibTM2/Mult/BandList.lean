module

public import IntegerMultBounds.NLogN.SchurSubst
public import IntegerMultBounds.MathlibTM2.Mult.ConcreteB0Sizes
public import IntegerMultBounds.MathlibTM2.Fast.CMulArith

/-! List-level forward substitution on integer numerators, as the tape
machine computes it: the head of the pending list is final, and each later
pending numerator loses the truncated product with its column entry. On the
`2^-P` grid this reproduces the column-oriented real solve `colFwd` with
rounding toward zero. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.BandList

open IntegerMultBounds.NLogN IntegerMultBounds.NLogN.SchurDominance
open IntegerMultBounds.MathlibTM2.Mult.Sizes

/-- Subtract truncated products of a column with `y` from the leading pending
numerators; entries past the column are unchanged. -/
def subCol (P : ℕ) : List ℤ → ℤ → List ℤ → List ℤ
  | c::cs, y, r::rs => (r-(c*y).tdiv (2^P))::subCol P cs y rs
  | _, _, rs => rs

/-- Forward substitution on numerators, one column per step. -/
def fwdZ (P : ℕ) : List (List ℤ) → List ℤ → List ℤ
  | c::cs, y::rest => y::fwdZ P cs (subCol P c y rest)
  | _, _ => []

/-- `rdP` on a product of grid values is truncated integer division. -/
theorem rdP_mul_grid (P : ℕ) (a c : ℤ) :
    rdP P ((a : ℝ)/2^P*((c : ℝ)/2^P))=(((a*c).tdiv (2^P) : ℤ) : ℝ)/2^P := by
  unfold rdP
  congr 1
  rw [Fast.tdiv_rho0]
  congr 1
  push_cast
  field_simp

variable {ι : Type*} [DecidableEq ι]

/-- The full column table of a list order: for each pivot, its entries in the
rows after it. -/
def cols (Lz : ι → ι → ℤ) : List ι → List (List ℤ)
  | [] => []
  | k::rest => (rest.map fun i => Lz i k)::cols Lz rest

theorem colFwd_off (rd : ℝ → ℝ) (L : Matrix ι ι ℝ) (ks : List ι) :
    ∀ (y pend : ι → ℝ) (x : ι), x∉ks → colFwd rd L y pend ks x=y x := by
  induction ks with
  | nil => intro _ _ _ _; rfl
  | cons k ks ih =>
    intro y pend x hx
    simp only [List.mem_cons, not_or] at hx
    simp only [colFwd]
    rw [ih _ _ x hx.2, Function.update_of_ne hx.1]

omit [DecidableEq ι] in
theorem subCol_map (P : ℕ) (Lz : ι → ι → ℤ) (k : ι) (pendZ : ι → ℤ) (rest : List ι) :
    subCol P (rest.map fun i => Lz i k) (pendZ k) (rest.map pendZ)=
      rest.map fun i => pendZ i-(Lz i k*pendZ k).tdiv (2^P) := by
  induction rest with
  | nil => rfl
  | cons i rest ih => simp [subCol, ih]

omit [DecidableEq ι] in
theorem subCol_map' (P : ℕ) (Lz : ι → ι → ℤ) (k : ι) (v : ℤ) (pendZ : ι → ℤ) (rest : List ι) :
    subCol P (rest.map fun i => Lz i k) v (rest.map pendZ)=
      rest.map fun i => pendZ i-(Lz i k*v).tdiv (2^P) := by
  induction rest with
  | nil => rfl
  | cons i rest ih => simp [subCol, ih]

/-- The numerator list computation reproduces the column-oriented real solve. -/
theorem fwdZ_eq (P : ℕ) (L : Matrix ι ι ℝ) (Lz : ι → ι → ℤ)
    (hL : ∀ i k, L i k=(Lz i k : ℝ)/2^P) (ks : List ι) (hnd : ks.Nodup) :
    ∀ (y : ι → ℝ) (pendZ : ι → ℤ),
      (fwdZ P (cols Lz ks) (ks.map pendZ)).map (fun z : ℤ => (z : ℝ)/2^P)=
        ks.map (colFwd (rdP P) L y (fun i => (pendZ i : ℝ)/2^P) ks) := by
  induction ks with
  | nil => intro _ _; rfl
  | cons k rest ih =>
    intro y pendZ
    have hnd' := List.nodup_cons.mp hnd
    simp only [cols, List.map_cons, fwdZ, colFwd]
    rw [subCol_map]
    set pendZ' : ι → ℤ := fun i => if i∈rest then pendZ i-(Lz i k*pendZ k).tdiv (2^P) else pendZ i
    have hmap : (rest.map fun i => pendZ i-(Lz i k*pendZ k).tdiv (2^P))=rest.map pendZ' :=
      List.map_congr_left fun i hi => by simp [pendZ', hi]
    rw [hmap, ih hnd'.2]
    have hpend : (fun i => if i∈rest then (pendZ i : ℝ)/2^P-rdP P (L i k*((pendZ k : ℝ)/2^P))
        else (pendZ i : ℝ)/2^P)=fun i => (pendZ' i : ℝ)/2^P := by
      funext i
      by_cases hi : i∈rest
      · simp only [hi, ite_true, pendZ', hL, rdP_mul_grid]
        push_cast; ring
      · simp [hi, pendZ']
    rw [hpend, colFwd_off _ _ _ _ _ k hnd'.1, Function.update_self]

/-- Backward substitution on numerators, with stored reciprocal numerators. -/
def bwdZ (P : ℕ) : List (List ℤ) → List ℤ → List ℤ → List ℤ
  | c::cs, r::rs, q::rest => (q*r).tdiv (2^P)::bwdZ P cs rs (subCol P c ((q*r).tdiv (2^P)) rest)
  | _, _, _ => []

theorem colBwd_off (rd : ℝ → ℝ) (U : Matrix ι ι ℝ) (r : ι → ℝ) (ks : List ι) :
    ∀ (x pend : ι → ℝ) (z : ι), z∉ks → colBwd rd U r x pend ks z=x z := by
  induction ks with
  | nil => intro _ _ _ _; rfl
  | cons k ks ih =>
    intro x pend z hz
    simp only [List.mem_cons, not_or] at hz
    simp only [colBwd]
    rw [ih _ _ z hz.2, Function.update_of_ne hz.1]

theorem bwdZ_eq (P : ℕ) (U : Matrix ι ι ℝ) (Uz : ι → ι → ℤ)
    (hU : ∀ i k, U i k=(Uz i k : ℝ)/2^P) (rz : ι → ℤ) (ks : List ι) (hnd : ks.Nodup) :
    ∀ (x : ι → ℝ) (pendZ : ι → ℤ),
      (bwdZ P (cols Uz ks) (ks.map rz) (ks.map pendZ)).map (fun z : ℤ => (z : ℝ)/2^P)=
        ks.map (colBwd (rdP P) U (fun i => (rz i : ℝ)/2^P) x (fun i => (pendZ i : ℝ)/2^P) ks) := by
  induction ks with
  | nil => intro _ _; rfl
  | cons k rest ih =>
    intro x pendZ
    have hnd' := List.nodup_cons.mp hnd
    simp only [cols, List.map_cons, bwdZ, colBwd]
    set xk : ℤ := (pendZ k*rz k).tdiv (2^P)
    have hxk : rdP P ((pendZ k : ℝ)/2^P*((rz k : ℝ)/2^P))=(xk : ℝ)/2^P := rdP_mul_grid P _ _
    rw [subCol_map']
    set pendZ' : ι → ℤ := fun i => if i∈rest then pendZ i-(Uz i k*xk).tdiv (2^P) else pendZ i
    have hmap : (rest.map fun i => pendZ i-(Uz i k*xk).tdiv (2^P))=rest.map pendZ' :=
      List.map_congr_left fun i hi => by simp [pendZ', hi]
    rw [hmap, ih hnd'.2]
    have hpend : (fun i => if i∈rest then (pendZ i : ℝ)/2^P-rdP P (U i k*rdP P ((pendZ k : ℝ)/2^P*
        ((rz k : ℝ)/2^P))) else (pendZ i : ℝ)/2^P)=fun i => (pendZ' i : ℝ)/2^P := by
      funext i
      by_cases hi : i∈rest
      · simp only [hi, ite_true, pendZ', hU, hxk, rdP_mul_grid]
        push_cast; ring
      · simp [hi, pendZ']
    rw [hpend, colBwd_off _ _ _ _ _ _ k hnd'.1, Function.update_self, hxk]

/-- Zero column entries leave pending numerators unchanged. -/
theorem subCol_append_zeros (P : ℕ) (c₁ c₂ : List ℤ) (hz : ∀ x∈c₂, x=0) :
    ∀ (y : ℤ) (rs : List ℤ), subCol P (c₁++c₂) y rs=subCol P c₁ y rs := by
  induction c₁ with
  | nil =>
    intro y rs
    simp only [List.nil_append]
    induction c₂ generalizing rs with
    | nil => cases rs <;> rfl
    | cons c cs ihc =>
      cases rs with
      | nil => rfl
      | cons r rs =>
        simp only [subCol, hz c List.mem_cons_self, zero_mul, Int.zero_tdiv, sub_zero]
        rw [ihc (fun x hx => hz x (List.mem_cons_of_mem _ hx))]
        cases rs <;> rfl
  | cons c cs ih =>
    intro y rs
    cases rs with
    | nil => rfl
    | cons r rs => simp only [List.cons_append, subCol, ih]

end IntegerMultBounds.MathlibTM2.Mult.BandList
