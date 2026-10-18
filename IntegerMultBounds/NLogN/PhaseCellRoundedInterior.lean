module

public import IntegerMultBounds.NLogN.PhaseCellRoundedCell
public import IntegerMultBounds.NLogN.PhaseCellInteriorCover

/-! # The rounded interior solver

The exact interior solver of the phase-cell inverse decomposes into one similarity-scaled
Gohberg–Semencul solve per cell interval (`cell_solve`, `interior_cover`). A `CellRun` holds
the computed arrays of one rounded cell solve, and `CellRun.Valid` says that every computed
stage is within `η` of its exact operation on the computed inputs, as `rounded_cell` requires.
If every cell interval has a valid run whose outputs are the computed values, these are within
`η + 64 s η V + 2(η + C η)` of the exact interior solution at every interior vertex, for
right-hand sides at most `C` and scaled inputs at most `V` (`rounded_interior`). This supplies
the interior stage errors `e₁`, `e₅` of `rounded_four_step` and the column error `eR` of
`rounded_schur_solve`. -/
@[expose] public section
namespace IntegerMultBounds.NLogN.PhaseCellMatrix

open scoped BigOperators
open Finset SchurDominance ToeplitzInverse

/-- The computed arrays of one rounded cell solve: reciprocal weights `r`, scaled inputs `v`,
the generators `xh`, `zh` and `w` of the shared Toeplitz inverse, the four triangular Toeplitz
stages `u₁ … u₄`, their combination `out`, and the rescaled output `y`. -/
structure CellRun where
  r : ℕ → ℝ
  v : ℕ → ℝ
  xh : ℕ → ℝ
  zh : ℕ → ℝ
  w : ℝ
  u₁ : ℕ → ℝ
  u₂ : ℕ → ℝ
  u₃ : ℕ → ℝ
  u₄ : ℕ → ℝ
  out : ℕ → ℝ
  y : ℕ → ℝ

variable (s t : ℕ) [NeZero s]

/-- Every computed stage of the cell run on `lo + [0, L)` with right-hand side `c` is within
`η` of its exact operation on the computed inputs, and the scaled inputs are at most `V`. -/
def CellRun.Valid (p u : ℕ) (lo : ZMod s) (L : ℕ) (c : ZMod s → ℝ) (η V : ℝ) (A : CellRun) :
    Prop :=
  (∀ k<L, |A.r k-1/weight s t p u lo k|≤η) ∧
  (∀ k<L, |A.v k-c (lo+(k : ZMod s))*A.r k|≤η) ∧
  (∀ k∈range L, |A.v k|≤V) ∧
  (∀ k∈range L, |A.xh k-col (natInv L
    (PhaseCellToeplitz.coeff (2^15*p) s t u (PhaseCellBand.width p u))) k|≤η) ∧
  (∀ k∈range L, |A.zh k-rev L (natInv L
    (PhaseCellToeplitz.coeff (2^15*p) s t u (PhaseCellBand.width p u))) k|≤η) ∧
  |A.w-1/natInv L (PhaseCellToeplitz.coeff (2^15*p) s t u (PhaseCellBand.width p u)) 0 0|≤η ∧
  (∀ j∈range L, |A.u₁ j-upper L A.xh A.v j|≤η) ∧
  (∀ i∈range L, |A.u₂ i-lower A.xh A.u₁ i|≤η) ∧
  (∀ j∈range L, |A.u₃ j-upper L A.zh A.v j|≤η) ∧
  (∀ i∈range L, |A.u₄ i-lower A.zh A.u₃ i|≤η) ∧
  (∀ i∈range L, |A.out i-A.w*(A.u₂ i-A.u₄ i)|≤η) ∧
  ∀ a<L, |A.y a-weight s t p u lo a*A.out a|≤η

/-- **The rounded interior solver.** Values produced by valid cell runs on every cell interval
are within `η + 64 s η V + 2(η + C η)` of the exact interior solution. -/
theorem rounded_interior (hst : s<t) {α d : ℝ} (p u : ℕ) (hp : 0<p) (hu : 1≤u)
    (hαu : α^2=(u : ℝ)) (hθ : 0<(t : ℝ)/s-1)
    (hgap : (1 : ℝ)/4≤d*((t : ℝ)/s-1)) (hbudget : α^2*d≤p)
    (I : Finset (ZMod s)) (hI : ∀ j, j∈I ↔ Interior s t (PhaseCellBand.width p u) j)
    (x c : ZMod s → ℝ) (hx : Solves (realMatrix s t p u) I x c)
    (η C V : ℝ) (hη : 0≤η) (hC : 0≤C) (hV : 1≤V) (hsη : s*η≤1) (hc : ∀ k∈I, |c k|≤C)
    (z : ZMod s → ℝ)
    (hrun : ∀ (lo : ZMod s) (L : ℕ), 0<L → lo.val+L≤s →
      (∀ k<L, Interior s t (PhaseCellBand.width p u) (lo+(k : ZMod s)) ∧ lo+(k : ZMod s)∈I) →
      (∀ k<L, cell s t (lo+(k : ZMod s))=cell s t lo) →
      (∀ j∈I, cell s t j=cell s t lo → ∃ k<L, lo+(k : ZMod s)=j) →
      ∃ A : CellRun, A.Valid s t p u lo L c η V ∧ ∀ a<L, z (lo+(a : ZMod s))=A.y a)
    (j : ZMod s) (hj : j∈I) :
    |z j-x j|≤η+64*s*η*V+2*(η+C*η) := by
  obtain ⟨lo, L, hL, hfit, hint, hcell, hmax, a, ha, rfl⟩ :=
    interior_cover s t hst _ I hI j hj
  obtain ⟨A, ⟨hr, hv, hvV, hxh, hzh, hw, hu₁, hu₂, hu₃, hu₄, hout, hy⟩, hz⟩ :=
    hrun lo L hL hfit hint hcell hmax
  have hLs : (L : ℝ)≤s := by exact_mod_cast (by omega : L≤s)
  have hLη : (L : ℝ)*η≤1 := le_trans (mul_le_mul_of_nonneg_right hLs hη) hsη
  have h := rounded_cell s t hst p u hp hu hαu hθ hgap hbudget I x c hx lo L hL hfit hint hcell
    hmax A.xh A.zh A.r A.v A.u₁ A.u₂ A.u₃ A.u₄ A.out A.y A.w η C V hη hC hV hLη
    (fun k hk => hc _ (hint k hk).2) hr hv hvV hxh hzh hw hu₁ hu₂ hu₃ hu₄ hout hy a ha
  rw [hz a ha]
  have : 64*(L : ℝ)*η*V≤64*s*η*V := by
    have := mul_le_mul_of_nonneg_right hLs (mul_nonneg hη (by linarith : (0 : ℝ)≤V))
    nlinarith
  linarith

end IntegerMultBounds.NLogN.PhaseCellMatrix
