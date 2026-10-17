module

public import IntegerMultBounds.NLogN.SchurSubst
public import IntegerMultBounds.MathlibTM2.Mult.ConcreteB0Sizes
public import IntegerMultBounds.MathlibTM2.Fast.CMulArith
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Bernstein

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

/-! ### Complex records, padded columns

The machine stores complex numerators and applies real column entries to both
parts at once; columns are padded to a fixed length with zeros and the pending
list carries the same number of zero dummies. -/

/-- Real column entries applied to complex pending numerators. -/
def subColC (P : ℕ) : List ℤ → GaussianInt → List GaussianInt → List GaussianInt
  | c::cs, y, r::rs => (r-Fast.tdivN P (⟨c, 0⟩*y))::subColC P cs y rs
  | _, _, rs => rs

def fwdZC (P : ℕ) : List (List ℤ) → List GaussianInt → List GaussianInt
  | c::cs, y::rest => y::fwdZC P cs (subColC P c y rest)
  | _, _ => []

theorem subColC_re (P : ℕ) : ∀ (c : List ℤ) (y : GaussianInt) (rs : List GaussianInt),
    (subColC P c y rs).map (·.re)=subCol P c y.re (rs.map (·.re))
  | c::cs, y, r::rs => by
      simp only [subColC, subCol, List.map_cons, Zsqrtd.re_sub, Fast.tdivN_re, Zsqrtd.re_mul]
      rw [subColC_re P cs y rs]
      simp
  | [], _, rs => by cases rs <;> rfl
  | _::_, _, [] => rfl

theorem subColC_im (P : ℕ) : ∀ (c : List ℤ) (y : GaussianInt) (rs : List GaussianInt),
    (subColC P c y rs).map (·.im)=subCol P c y.im (rs.map (·.im))
  | c::cs, y, r::rs => by
      simp only [subColC, subCol, List.map_cons, Zsqrtd.im_sub, Fast.tdivN_im, Zsqrtd.im_mul]
      rw [subColC_im P cs y rs]
      simp
  | [], _, rs => by cases rs <;> rfl
  | _::_, _, [] => rfl

theorem fwdZC_re (P : ℕ) : ∀ (cs : List (List ℤ)) (pend : List GaussianInt),
    (fwdZC P cs pend).map (·.re)=fwdZ P cs (pend.map (·.re))
  | c::cs, y::rest => by
      simp only [fwdZC, fwdZ, List.map_cons]
      rw [fwdZC_re P cs, subColC_re]
  | [], pend => by cases pend <;> rfl
  | _::_, [] => rfl

theorem fwdZC_im (P : ℕ) : ∀ (cs : List (List ℤ)) (pend : List GaussianInt),
    (fwdZC P cs pend).map (·.im)=fwdZ P cs (pend.map (·.im))
  | c::cs, y::rest => by
      simp only [fwdZC, fwdZ, List.map_cons]
      rw [fwdZC_im P cs, subColC_im]
  | [], pend => by cases pend <;> rfl
  | _::_, [] => rfl

def bwdZC (P : ℕ) : List (List ℤ) → List ℤ → List GaussianInt → List GaussianInt
  | c::cs, r::rs, q::rest => Fast.tdivN P (q*⟨r, 0⟩)::
      bwdZC P cs rs (subColC P c (Fast.tdivN P (q*⟨r, 0⟩)) rest)
  | _, _, _ => []

theorem bwdZC_re (P : ℕ) : ∀ (cs : List (List ℤ)) (rs : List ℤ) (pend : List GaussianInt),
    (bwdZC P cs rs pend).map (·.re)=bwdZ P cs rs (pend.map (·.re))
  | c::cs, r::rs, q::rest => by
      simp only [bwdZC, bwdZ, List.map_cons, Fast.tdivN_re, Zsqrtd.re_mul]
      rw [bwdZC_re P cs rs, subColC_re]
      simp [Fast.tdivN_re, Zsqrtd.re_mul]
  | [], _, pend => by cases pend <;> rfl
  | _::_, [], pend => by cases pend <;> rfl
  | _::_, _::_, [] => rfl

theorem bwdZC_im (P : ℕ) : ∀ (cs : List (List ℤ)) (rs : List ℤ) (pend : List GaussianInt),
    (bwdZC P cs rs pend).map (·.im)=bwdZ P cs rs (pend.map (·.im))
  | c::cs, r::rs, q::rest => by
      simp only [bwdZC, bwdZ, List.map_cons, Fast.tdivN_im, Zsqrtd.im_mul]
      rw [bwdZC_im P cs rs, subColC_im]
      simp [Fast.tdivN_im, Zsqrtd.im_mul]
  | [], _, pend => by cases pend <;> rfl
  | _::_, [], pend => by cases pend <;> rfl
  | _::_, _::_, [] => rfl

/-! ### Padding to a fixed band -/

theorem length_subCol (P : ℕ) : ∀ (c : List ℤ) (y : ℤ) (rs : List ℤ),
    (subCol P c y rs).length=rs.length
  | c::cs, y, r::rs => by simp [subCol, length_subCol P cs y rs]
  | [], _, rs => by cases rs <;> rfl
  | _::_, _, [] => rfl


/-- A column truncated to its first `B` entries and padded with zeros to length `B`. -/
def padCol (B : ℕ) (c : List ℤ) : List ℤ := c.take B++List.replicate (B-(c.take B).length) 0

theorem subCol_append_rest (P : ℕ) : ∀ (c : List ℤ) (y : ℤ) (rs D : List ℤ),
    c.length≤rs.length → subCol P c y (rs++D)=subCol P c y rs++D
  | [], _, rs, D, _ => by cases rs <;> rfl
  | c::cs, y, r::rs, D, h => by
      simp only [List.cons_append, subCol]
      rw [subCol_append_rest P cs y rs D (by simp at h; omega)]
  | _::_, _, [], _, h => by simp at h

theorem subCol_pad (P B : ℕ) (c : List ℤ) (y : ℤ) (rs : List ℤ) (hlen : c.length=rs.length)
    (hz : ∀ x∈c.drop B, x=0) :
    subCol P (padCol B c) y (rs++List.replicate B 0)=subCol P c y rs++List.replicate B 0 := by
  unfold padCol
  rw [subCol_append_zeros P _ _ (fun x hx => (List.mem_replicate.mp hx).2),
    subCol_append_rest P _ y rs _ (by simp [List.length_take]; omega)]
  congr 1
  conv_rhs => rw [←List.take_append_drop B c]
  rw [subCol_append_zeros P _ _ hz]

/-- Each column vanishes beyond its first `B` entries. -/
def Banded (B : ℕ) (Lz : ι → ι → ℤ) : List ι → Prop
  | [] => True
  | k::rest => (∀ x∈rest.drop B, Lz x k=0) ∧ Banded B Lz rest

omit [DecidableEq ι] in
theorem cols_drop_zero (B : ℕ) (Lz : ι → ι → ℤ) (k : ι) (rest : List ι)
    (h : ∀ x∈rest.drop B, Lz x k=0) : ∀ z∈(rest.map fun i => Lz i k).drop B, z=0 := by
  intro z hz
  rw [←List.map_drop] at hz
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hz
  exact h x hx

omit [DecidableEq ι] in
/-- Padded columns and `B` dummy zeros reproduce the full forward computation. -/
theorem fwdZ_pad (P B : ℕ) (Lz : ι → ι → ℤ) (ks : List ι) (hb : Banded B Lz ks) :
    ∀ pend : List ℤ, pend.length=ks.length →
      fwdZ P ((cols Lz ks).map (padCol B)) (pend++List.replicate B 0)=fwdZ P (cols Lz ks) pend := by
  induction ks with
  | nil => intro pend _; simp [cols, fwdZ]
  | cons k rest ih =>
    intro pend hlen
    obtain ⟨hk, hrest⟩ := hb
    cases pend with
    | nil => simp at hlen
    | cons y ps =>
      simp only [cols, List.map_cons, List.cons_append, fwdZ]
      have hl : ps.length=rest.length := by simpa using hlen
      rw [subCol_pad P B _ y ps (by simp [hl]) (cols_drop_zero B Lz k rest hk)]
      rw [ih hrest _ (by rw [length_subCol, hl])]

omit [DecidableEq ι] in
/-- The same for the backward computation with stored reciprocals. -/
theorem bwdZ_pad (P B : ℕ) (Uz : ι → ι → ℤ) (ks : List ι) (hb : Banded B Uz ks) (rs : List ℤ) :
    ∀ pend : List ℤ, pend.length=ks.length →
      bwdZ P ((cols Uz ks).map (padCol B)) rs (pend++List.replicate B 0)=
        bwdZ P (cols Uz ks) rs pend := by
  induction ks generalizing rs with
  | nil => intro pend _; simp [cols, bwdZ]
  | cons k rest ih =>
    intro pend hlen
    obtain ⟨hk, hrest⟩ := hb
    cases pend with
    | nil => simp at hlen
    | cons q ps =>
      cases rs with
      | nil => simp [cols, bwdZ]
      | cons r rs =>
        simp only [cols, List.map_cons, List.cons_append, bwdZ]
        have hl : ps.length=rest.length := by simpa using hlen
        rw [subCol_pad P B _ _ ps (by simp [hl]) (cols_drop_zero B Uz k rest hk)]
        rw [ih hrest rs _ (by rw [length_subCol, hl])]

/-! ### Step-indexed states of the forward computation -/

/-- Pending list after `j` forward steps. -/
def bandPend (P : ℕ) (cs : List (List ℤ)) (pend : List GaussianInt) : ℕ → List GaussianInt
  | 0 => pend
  | j+1 => match bandPend P cs pend j with
    | y::rest => subColC P (cs.getD j []) y rest
    | [] => []

/-- Outputs after `j` forward steps, most recent first. -/
def bandOut (P : ℕ) (cs : List (List ℤ)) (pend : List GaussianInt) : ℕ → List GaussianInt
  | 0 => []
  | j+1 => (bandPend P cs pend j).headD 0::bandOut P cs pend j

theorem bandPend_cons (P : ℕ) (c : List ℤ) (cs : List (List ℤ)) (y : GaussianInt)
    (rest : List GaussianInt) : ∀ j,
    bandPend P (c::cs) (y::rest) (j+1)=bandPend P cs (subColC P c y rest) j
  | 0 => rfl
  | j+1 => by
      rw [bandPend, bandPend_cons P c cs y rest j, bandPend]
      rfl

theorem bandOut_cons (P : ℕ) (c : List ℤ) (cs : List (List ℤ)) (y : GaussianInt)
    (rest : List GaussianInt) : ∀ j,
    bandOut P (c::cs) (y::rest) (j+1)=bandOut P cs (subColC P c y rest) j++[y]
  | 0 => rfl
  | j+1 => by
      rw [bandOut, bandOut_cons P c cs y rest j, bandPend_cons, bandOut]
      rfl

theorem length_subColC (P : ℕ) : ∀ (c : List ℤ) (y : GaussianInt) (rs : List GaussianInt),
    (subColC P c y rs).length=rs.length
  | c::cs, y, r::rs => by simp [subColC, length_subColC P cs y rs]
  | [], _, rs => by cases rs <;> rfl
  | _::_, _, [] => rfl

/-- The step-indexed outputs give the forward computation. -/
theorem fwdZC_eq_bandOut (P : ℕ) : ∀ (cs : List (List ℤ)) (pend : List GaussianInt),
    cs.length≤pend.length → fwdZC P cs pend=(bandOut P cs pend cs.length).reverse
  | [], pend, _ => by cases pend <;> rfl
  | c::cs, y::rest, h => by
      simp only [fwdZC, List.length_cons]
      rw [bandOut_cons, List.reverse_append, fwdZC_eq_bandOut P cs _ (by
        rw [length_subColC]; simp at h; omega)]
      rfl
  | _::_, [], h => by simp at h

theorem length_bandPend (P : ℕ) (cs : List (List ℤ)) (pend : List GaussianInt) :
    ∀ j, j≤pend.length → (bandPend P cs pend j).length=pend.length-j
  | 0, _ => by simp [bandPend]
  | j+1, h => by
      have ih := length_bandPend P cs pend j (by omega)
      simp only [bandPend]
      split
      · rename_i y rest heq
        rw [length_subColC]
        rw [heq] at ih
        simp at ih; omega
      · rename_i heq
        rw [heq] at ih; simp at ih; omega

/-- Pending list after `j` backward steps (heads scaled by stored reciprocals). -/
def bandPendB (P : ℕ) (cs : List (List ℤ)) (rs : List ℤ) (pend : List GaussianInt) :
    ℕ → List GaussianInt
  | 0 => pend
  | j+1 => match bandPendB P cs rs pend j with
    | q::rest => subColC P (cs.getD j []) (Fast.tdivN P (q*⟨rs.getD j 0, 0⟩)) rest
    | [] => []

/-- Outputs after `j` backward steps, most recent first. -/
def bandOutB (P : ℕ) (cs : List (List ℤ)) (rs : List ℤ) (pend : List GaussianInt) :
    ℕ → List GaussianInt
  | 0 => []
  | j+1 => Fast.tdivN P ((bandPendB P cs rs pend j).headD 0*⟨rs.getD j 0, 0⟩)::
      bandOutB P cs rs pend j

theorem bandPendB_cons (P : ℕ) (c : List ℤ) (cs : List (List ℤ)) (r : ℤ) (rs : List ℤ)
    (q : GaussianInt) (rest : List GaussianInt) : ∀ j,
    bandPendB P (c::cs) (r::rs) (q::rest) (j+1)=
      bandPendB P cs rs (subColC P c (Fast.tdivN P (q*⟨r, 0⟩)) rest) j
  | 0 => rfl
  | j+1 => by
      rw [bandPendB, bandPendB_cons P c cs r rs q rest j, bandPendB]
      rfl

theorem bandOutB_cons (P : ℕ) (c : List ℤ) (cs : List (List ℤ)) (r : ℤ) (rs : List ℤ)
    (q : GaussianInt) (rest : List GaussianInt) : ∀ j,
    bandOutB P (c::cs) (r::rs) (q::rest) (j+1)=
      bandOutB P cs rs (subColC P c (Fast.tdivN P (q*⟨r, 0⟩)) rest) j++[Fast.tdivN P (q*⟨r, 0⟩)]
  | 0 => rfl
  | j+1 => by
      rw [bandOutB, bandOutB_cons P c cs r rs q rest j, bandPendB_cons, bandOutB]
      rfl

theorem bwdZC_eq_bandOutB (P : ℕ) : ∀ (cs : List (List ℤ)) (rs : List ℤ) (pend : List GaussianInt),
    cs.length≤pend.length → cs.length≤rs.length →
      bwdZC P cs rs pend=(bandOutB P cs rs pend cs.length).reverse
  | [], rs, pend, _, _ => by cases rs <;> cases pend <;> rfl
  | c::cs, r::rs, q::rest, h1, h2 => by
      simp only [bwdZC, List.length_cons]
      rw [bandOutB_cons, List.reverse_append, bwdZC_eq_bandOutB P cs rs _ (by
        rw [length_subColC]; simp at h1; omega) (by simp at h2; omega)]
      rfl
  | _::_, [], _, _, h2 => by simp at h2
  | _::_, _::_, [], h1, _ => by simp at h1

theorem length_bandPendB (P : ℕ) (cs : List (List ℤ)) (rs : List ℤ) (pend : List GaussianInt) :
    ∀ j, j≤pend.length → (bandPendB P cs rs pend j).length=pend.length-j
  | 0, _ => by simp [bandPendB]
  | j+1, h => by
      have ih := length_bandPendB P cs rs pend j (by omega)
      simp only [bandPendB]
      split
      · rename_i q rest heq
        rw [length_subColC]
        rw [heq] at ih
        simp at ih; omega
      · rename_i heq
        rw [heq] at ih; simp at ih; omega

end IntegerMultBounds.MathlibTM2.Mult.BandList
