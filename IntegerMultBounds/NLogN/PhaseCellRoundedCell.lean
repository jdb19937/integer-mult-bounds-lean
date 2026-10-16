module

public import IntegerMultBounds.NLogN.PhaseCellInteriorSolve
public import IntegerMultBounds.NLogN.PhaseCellWeightRange
public import IntegerMultBounds.NLogN.ToeplitzScaled

/-! Rounded interior solve of one actual phase-cell interval. The computed
reciprocal weights, scaled inputs, five Gohberg–Semencul stages and rescaling
reproduce the exact interior solution of the actual rounded Gaussian matrix
within `η + 64 L η V + 2(η + C η)`. -/
@[expose] public section
namespace IntegerMultBounds.NLogN.PhaseCellMatrix

open scoped BigOperators
open Finset SchurDominance ToeplitzInverse
variable (s t : ℕ) [NeZero s]

theorem rounded_cell (hst : s<t) {α d : ℝ} (p u : ℕ) (hp : 0<p) (hu : 1≤u)
    (hαu : α^2=(u : ℝ)) (hθ : 0<(t : ℝ)/s-1)
    (hgap : (1 : ℝ)/4≤d*((t : ℝ)/s-1)) (hbudget : α^2*d≤p)
    (I : Finset (ZMod s)) (x c : ZMod s → ℝ) (hx : Solves (realMatrix s t p u) I x c)
    (lo : ZMod s) (L : ℕ) (hL : 0<L) (hfit : lo.val+L≤s)
    (hint : ∀ k<L, Interior s t (PhaseCellBand.width p u) (lo+(k : ZMod s)) ∧ lo+(k : ZMod s)∈I)
    (hcell : ∀ k<L, cell s t (lo+(k : ZMod s))=cell s t lo)
    (hmax : ∀ j∈I, cell s t j=cell s t lo → ∃ k<L, lo+(k : ZMod s)=j)
    (xh zh r v u₁ u₂ u₃ u₄ out y : ℕ → ℝ) (w η C V : ℝ)
    (hη : 0≤η) (hC : 0≤C) (hV : 1≤V) (hLη : L*η≤1)
    (hc : ∀ k<L, |c (lo+(k : ZMod s))|≤C)
    (hr : ∀ k<L, |r k-1/weight s t p u lo k|≤η)
    (hv : ∀ k<L, |v k-c (lo+(k : ZMod s))*r k|≤η)
    (hvV : ∀ k∈range L, |v k|≤V)
    (hxh : ∀ k∈range L, |xh k-col (natInv L
      (PhaseCellToeplitz.coeff (2^15*p) s t u (PhaseCellBand.width p u))) k|≤η)
    (hzh : ∀ k∈range L, |zh k-rev L (natInv L
      (PhaseCellToeplitz.coeff (2^15*p) s t u (PhaseCellBand.width p u))) k|≤η)
    (hw : |w-1/natInv L (PhaseCellToeplitz.coeff (2^15*p) s t u (PhaseCellBand.width p u)) 0 0|≤η)
    (hu₁ : ∀ j∈range L, |u₁ j-upper L xh v j|≤η)
    (hu₂ : ∀ i∈range L, |u₂ i-lower xh u₁ i|≤η)
    (hu₃ : ∀ j∈range L, |u₃ j-upper L zh v j|≤η)
    (hu₄ : ∀ i∈range L, |u₄ i-lower zh u₃ i|≤η)
    (hout : ∀ i∈range L, |out i-w*(u₂ i-u₄ i)|≤η)
    (hy : ∀ a<L, |y a-weight s t p u lo a*out a|≤η) (a : ℕ) (ha : a<L) :
    |y a-x (lo+(a : ZMod s))|≤η+64*L*η*V+2*(η+C*η) := by
  have hs : 0<s := Nat.pos_of_ne_zero (NeZero.ne s)
  have hP : 13≤2^15*p := (PhaseCellConcreteCoefficients.selected_precision p hp).1
  rw [cell_solve s t hst p u hp hu hαu hθ hgap hbudget I x c hx lo L hL hfit hint hcell hmax a ha]
  have hrange (k : ℕ) := PhaseCellConcreteCoefficients.selected_similarity_range
    ((lo+(k : ZMod s)).val : ℤ) hp hs hαu hθ hgap hbudget
  exact rounded_block (L := L) PhaseCellToeplitz.coeff_zero
    (PhaseCellToeplitz.rowMass hP hs hst.le hu L) le_rfl hL xh zh (weight s t p u lo) r
    (fun k => c (lo+(k : ZMod s))) v u₁ u₂ u₃ u₄ out y w η C V hη hC hV hLη
    (fun k _ => ⟨lt_of_lt_of_le (by positivity) (hrange k).1, (hrange k).2⟩) hc hr hv hvV
    hxh hzh hw hu₁ hu₂ hu₃ hu₄ hout hy a ha

end IntegerMultBounds.NLogN.PhaseCellMatrix
