module

public import IntegerMultBounds.NLogN.PhaseCellRoundedInterior
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Algebra.Order.Ring.Star
public import IntegerMultBounds.Machine

/-! # The concrete rounded interior solve

The cell interval of an interior vertex `k` runs from the least to the greatest physical index of
the interior vertices of its cell (`cellLo`, `cellLen`); it has the properties the cell solves
require (`cell_interval`). The concrete cell run `cellRunOf` rounds every stage once with a
rounding `rd` within `η`, so it is valid (`cellRunOf_valid`): the scaled inputs are at most
`(C + 1) 2^(8p+2)` for right-hand sides at most `C`, since the similarity weights are at least
`2^-(8p+1)`. The concrete interior solve `pcInterior` takes at every interior vertex the output
of the run on its cell interval, and is within
`η + 64 s η (C + 1) 2^(8p+2) + 2(η + C η)` of the exact interior solution
(`pcInterior_error`). -/
@[expose] public section
namespace IntegerMultBounds.NLogN.PhaseCellMatrix

open scoped BigOperators
open Finset SchurDominance ToeplitzInverse
variable (s t : ℕ) [NeZero s]

/-! ### Cell intervals -/

/-- The interior vertices of the cell of `k`. -/
noncomputable def cellSet (I : Finset (ZMod s)) (k : ZMod s) : Finset (ZMod s) :=
  I.filter fun j => cell s t j=cell s t k

/-- The least physical index of the interior vertices of the cell of `k`. -/
noncomputable def cellLoVal (I : Finset (ZMod s)) (k : ZMod s) : ℕ :=
  if h : (cellSet s t I k).Nonempty then ((cellSet s t I k).image ZMod.val).min' (h.image _)
  else 0

/-- The greatest physical index of the interior vertices of the cell of `k`. -/
noncomputable def cellHiVal (I : Finset (ZMod s)) (k : ZMod s) : ℕ :=
  if h : (cellSet s t I k).Nonempty then ((cellSet s t I k).image ZMod.val).max' (h.image _)
  else 0

/-- The first vertex of the cell interval of `k`. -/
noncomputable def cellLo (I : Finset (ZMod s)) (k : ZMod s) : ZMod s := (cellLoVal s t I k : ZMod s)

/-- The length of the cell interval of `k`. -/
noncomputable def cellLen (I : Finset (ZMod s)) (k : ZMod s) : ℕ :=
  cellHiVal s t I k-cellLoVal s t I k+1

/-- The cell interval of an interior vertex consists of interior vertices of its cell, contains
all of them, and contains the vertex at offset `k - lo`. -/
theorem cell_interval (hst : s<t) (w : ℕ) (I : Finset (ZMod s))
    (hI : ∀ j, j∈I ↔ Interior s t w j) (k : ZMod s) (hk : k∈I) :
    0<cellLen s t I k ∧ (cellLo s t I k).val+cellLen s t I k≤s ∧
      (∀ a<cellLen s t I k, Interior s t w (cellLo s t I k+(a : ZMod s)) ∧
        cellLo s t I k+(a : ZMod s)∈I) ∧
      (∀ a<cellLen s t I k, cell s t (cellLo s t I k+(a : ZMod s))=cell s t (cellLo s t I k)) ∧
      (∀ j∈I, cell s t j=cell s t (cellLo s t I k) →
        ∃ a<cellLen s t I k, cellLo s t I k+(a : ZMod s)=j) ∧
      k.val-(cellLo s t I k).val<cellLen s t I k ∧
      cellLo s t I k+((k.val-(cellLo s t I k).val : ℕ) : ZMod s)=k := by
  set T := cellSet s t I k with hT
  have hkT : k∈T := mem_filter.mpr ⟨hk, rfl⟩
  have hne : T.Nonempty := ⟨k, hkT⟩
  obtain ⟨lo, hloT, hlov⟩ := mem_image.mp (min'_mem (T.image ZMod.val) (hne.image _))
  obtain ⟨hh, hhT, hhv⟩ := mem_image.mp (max'_mem (T.image ZMod.val) (hne.image _))
  have hlo : ∀ j∈T, lo.val≤j.val := fun j hj => by
    rw [hlov]; exact min'_le _ _ (mem_image_of_mem _ hj)
  have hhh : ∀ j∈T, j.val≤hh.val := fun j hj => by
    rw [hhv]; exact le_max' _ _ (mem_image_of_mem _ hj)
  have hLoV : cellLoVal s t I k=lo.val := by rw [cellLoVal, dite_eq_left hne]; exact hlov.symm
  have hHiV : cellHiVal s t I k=hh.val := by rw [cellHiVal, dite_eq_left hne]; exact hhv.symm
  have hLo : cellLo s t I k=lo := by rw [cellLo, hLoV, ZMod.natCast_zmod_val]
  have hLen : cellLen s t I k=hh.val-lo.val+1 := by rw [cellLen, hLoV, hHiV]
  rw [hLo, hLen]
  have hloI := (mem_filter.mp hloT).1
  have hhI := (mem_filter.mp hhT).1
  have hlocell := (mem_filter.mp hloT).2
  have hhcell := (mem_filter.mp hhT).2
  have hloint := (hI lo).mp hloI
  have hhint := (hI hh).mp hhI
  have hhs : hh.val<s := ZMod.val_lt hh
  have hlh : lo.val≤hh.val := hlo hh hhT
  have hval (a : ℕ) (ha : lo.val+a≤hh.val) : (lo+(a : ZMod s)).val=lo.val+a := by
    have has : (a : ZMod s).val=a := ZMod.val_cast_of_lt (by omega)
    rw [ZMod.val_add_of_lt (by omega), has]
  have hcover (j : ZMod s) (hj : lo.val≤j.val) (hj' : j.val≤hh.val) :
      Interior s t w j ∧ cell s t j=cell s t lo :=
    interior_convex s t hst w lo j hh hloint hhint (hlocell.trans hhcell.symm) hj hj'
  have hrepr (j : ZMod s) (hj : lo.val≤j.val) (hj' : j.val≤hh.val) :
      lo+((j.val-lo.val : ℕ) : ZMod s)=j := by
    apply ZMod.val_injective
    rw [hval _ (by omega)]
    omega
  refine ⟨by omega, by omega, fun a ha => ?_, fun a ha => ?_, fun j hj hjc => ?_, ?_,
    hrepr k (hlo k hkT) (hhh k hkT)⟩
  · have hv := hval a (by omega)
    have h := hcover (lo+(a : ZMod s)) (by omega) (by omega)
    exact ⟨h.1, (hI _).mpr h.1⟩
  · have hv := hval a (by omega)
    exact (hcover (lo+(a : ZMod s)) (by omega) (by omega)).2
  · have hjT : j∈T := mem_filter.mpr ⟨hj, hjc.trans hlocell⟩
    exact ⟨j.val-lo.val, by have := hlo j hjT; have := hhh j hjT; omega,
      hrepr j (hlo j hjT) (hhh j hjT)⟩
  · have := hhh k hkT
    have := hlo k hkT
    omega

/-! ### Concrete cell runs -/

variable (p u : ℕ)

/-- The computed cell run on `lo + [0, L)` for the right-hand side `c`: every stage of
`CellRun.Valid` rounded once by `rd`. -/
noncomputable def cellRunOf (rd : ℝ → ℝ) (lo : ZMod s) (L : ℕ) (c : ZMod s → ℝ) : CellRun :=
  let g := natInv L (PhaseCellToeplitz.coeff (2^15*p) s t u (PhaseCellBand.width p u))
  let r : ℕ → ℝ := fun k => rd (1/weight s t p u lo k)
  let v : ℕ → ℝ := fun k => rd (c (lo+(k : ZMod s))*r k)
  let xh : ℕ → ℝ := fun k => rd (col g k)
  let zh : ℕ → ℝ := fun k => rd (rev L g k)
  let w : ℝ := rd (1/g 0 0)
  let u₁ : ℕ → ℝ := fun j => rd (upper L xh v j)
  let u₂ : ℕ → ℝ := fun i => rd (lower xh u₁ i)
  let u₃ : ℕ → ℝ := fun j => rd (upper L zh v j)
  let u₄ : ℕ → ℝ := fun i => rd (lower zh u₃ i)
  let out : ℕ → ℝ := fun i => rd (w*(u₂ i-u₄ i))
  ⟨r, v, xh, zh, w, u₁, u₂, u₃, u₄, out, fun a => rd (weight s t p u lo a*out a)⟩

/-- The concrete run is valid, with scaled inputs at most `(C + 1) 2^(8p+2)`. -/
theorem cellRunOf_valid {α d : ℝ} (hp : 0<p) (hαu : α^2=(u : ℝ))
    (hθ : 0<(t : ℝ)/s-1) (hgap : (1 : ℝ)/4≤d*((t : ℝ)/s-1)) (hbudget : α^2*d≤p)
    (rd : ℝ → ℝ) (η : ℝ) (hrd : ∀ x, |rd x-x|≤η) (hη1 : η≤1)
    (lo : ZMod s) (L : ℕ) (c : ZMod s → ℝ) (C : ℝ) (hC : 0≤C)
    (hc : ∀ k<L, |c (lo+(k : ZMod s))|≤C) :
    (cellRunOf s t p u rd lo L c).Valid s t p u lo L c η ((C+1)*2^(8*p+2)) := by
  have hs : 0<s := Nat.pos_of_ne_zero (NeZero.ne s)
  have hQ : (1 : ℝ)≤2^(8*p+1) := one_le_pow₀ (by norm_num)
  have hrecip (k : ℕ) : |rd (1/weight s t p u lo k)|≤2^(8*p+1)+1 := by
    have hr := PhaseCellConcreteCoefficients.selected_similarity_range
      ((lo+(k : ZMod s)).val : ℤ) hp hs hαu hθ hgap hbudget
    have hw0 : 0<weight s t p u lo k := lt_of_lt_of_le (by positivity) hr.1
    have hinv : 1/weight s t p u lo k≤2^(8*p+1) := by
      rw [div_le_iff₀ hw0]
      have := mul_le_mul_of_nonneg_left hr.1 (by positivity : (0 : ℝ)≤2^(8*p+1))
      rw [mul_one_div_cancel (by positivity)] at this
      unfold weight; linarith
    have h1 := hrd (1/weight s t p u lo k)
    have h2 : |1/weight s t p u lo k|≤2^(8*p+1) := by
      rw [abs_of_pos (by positivity)]; exact hinv
    have := abs_add_le (rd (1/weight s t p u lo k)-1/weight s t p u lo k) (1/weight s t p u lo k)
    rw [sub_add_cancel] at this
    linarith
  refine ⟨fun k _ => hrd _, fun k _ => hrd _, fun k hk => ?_, fun k _ => hrd _, fun k _ => hrd _,
    hrd _, fun j _ => hrd _, fun i _ => hrd _, fun j _ => hrd _, fun i _ => hrd _,
    fun i _ => hrd _, fun a _ => hrd _⟩
  have hk' : k<L := mem_range.mp hk
  show |rd (c (lo+(k : ZMod s))*rd (1/weight s t p u lo k))|≤(C+1)*2^(8*p+2)
  have h1 := hrd (c (lo+(k : ZMod s))*rd (1/weight s t p u lo k))
  have h2 : |c (lo+(k : ZMod s))*rd (1/weight s t p u lo k)|≤C*(2^(8*p+1)+1) := by
    rw [abs_mul]; exact mul_le_mul (hc k hk') (hrecip k) (abs_nonneg _) hC
  have := abs_add_le (rd (c (lo+(k : ZMod s))*rd (1/weight s t p u lo k))-
    c (lo+(k : ZMod s))*rd (1/weight s t p u lo k)) (c (lo+(k : ZMod s))*rd (1/weight s t p u lo k))
  rw [sub_add_cancel] at this
  have e : (2 : ℝ)^(8*p+2)=2*2^(8*p+1) := by rw [pow_succ]; ring
  rw [e]
  nlinarith

/-- The concrete interior solve: at every interior vertex, the output of the concrete run on its
cell interval. -/
noncomputable def pcInterior (rd : ℝ → ℝ) (I : Finset (ZMod s)) (c : ZMod s → ℝ) (k : ZMod s) : ℝ :=
  (cellRunOf s t p u rd (cellLo s t I k) (cellLen s t I k) c).y (k.val-(cellLo s t I k).val)

/-- **The concrete interior solve** is within `η + 64 s η (C + 1) 2^(8p+2) + 2(η + C η)` of the
exact interior solution for right-hand sides at most `C`. -/
theorem pcInterior_error (hst : s<t) {α d : ℝ} (hp : 0<p) (hu : 1≤u) (hαu : α^2=(u : ℝ))
    (hθ : 0<(t : ℝ)/s-1) (hgap : (1 : ℝ)/4≤d*((t : ℝ)/s-1)) (hbudget : α^2*d≤p)
    (I : Finset (ZMod s)) (hI : ∀ j, j∈I ↔ Interior s t (PhaseCellBand.width p u) j)
    (x c : ZMod s → ℝ) (hx : Solves (realMatrix s t p u) I x c)
    (rd : ℝ → ℝ) (η : ℝ) (hrd : ∀ x, |rd x-x|≤η) (hη1 : η≤1) (hsη : s*η≤1)
    (C : ℝ) (hC : 0≤C) (hc : ∀ k∈I, |c k|≤C) (k : ZMod s) (hk : k∈I) :
    |pcInterior s t p u rd I c k-x k|≤η+64*s*η*((C+1)*2^(8*p+2))+2*(η+C*η) := by
  have hη : 0≤η := le_trans (abs_nonneg _) (hrd 0)
  obtain ⟨hL, hfit, hint, hcell, hmax, ha, hk'⟩ := cell_interval s t hst _ I hI k hk
  set lo := cellLo s t I k
  set L := cellLen s t I k
  set a := k.val-lo.val
  have hV : (1 : ℝ)≤(C+1)*2^(8*p+2) :=
    one_le_mul_of_one_le_of_one_le (by linarith) (one_le_pow₀ (by norm_num))
  have hLs : (L : ℝ)≤s := by exact_mod_cast (by omega : L≤s)
  have hLη : (L : ℝ)*η≤1 := le_trans (mul_le_mul_of_nonneg_right hLs hη) hsη
  have hcL : ∀ k'<L, |c (lo+(k' : ZMod s))|≤C := fun k' hk'' => hc _ (hint k' hk'').2
  obtain ⟨hr, hv, hvV, hxh, hzh, hw, hu₁, hu₂, hu₃, hu₄, hout, hy⟩ :=
    cellRunOf_valid s t p u hp hαu hθ hgap hbudget rd η hrd hη1 lo L c C hC hcL
  have h := rounded_cell s t hst p u hp hu hαu hθ hgap hbudget I x c hx lo L hL hfit hint hcell
    hmax _ _ _ _ _ _ _ _ _ _ _ η C _ hη hC hV hLη hcL hr hv hvV hxh hzh hw hu₁ hu₂ hu₃ hu₄ hout
    hy a ha
  rw [hk'] at h
  have : 64*(L : ℝ)*η*((C+1)*2^(8*p+2))≤64*s*η*((C+1)*2^(8*p+2)) := by
    have := mul_le_mul_of_nonneg_right hLs (mul_nonneg hη (by linarith : (0 : ℝ)≤(C+1)*2^(8*p+2)))
    nlinarith
  exact h.trans (by linarith)

end IntegerMultBounds.NLogN.PhaseCellMatrix
