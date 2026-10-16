module

public import IntegerMultBounds.NLogN.PhaseCellBandSolve
public import IntegerMultBounds.NLogN.PhaseCellFold

/-! The machine-faithful band solve of the actual rounded matrix in folded
order, where the factors are an ordinary band of half width `2w+1`. -/
@[expose] public section
namespace IntegerMultBounds.NLogN.PhaseCellMatrix

open scoped BigOperators
open Finset SchurDominance
variable (s t : ℕ) [NeZero s] [NeZero t]

/-- The machine-faithful band solve on the actual matrix in folded order: with
`2^16 p² s² η ≤ 1`, error at most `62000 p³ s² η`. -/
theorem bandSolveM_fold (hst : s<t) {α d : ℝ} (hα : 0<α)
    (p u : ℕ) (hp : 2≤p) (hwidth : 8*p≤2^u) (hαu : α^2=(u : ℝ))
    (hθ : 1/(4*(p : ℝ))≤(t : ℝ)/s-1)
    (hgap : (1 : ℝ)/4≤d*((t : ℝ)/s-1)) (hbudget : α^2*d≤p)
    (rd : ℝ → ℝ) (η : ℝ) (hrd : ∀ x, |rd x-x|≤η) (hrd0 : rd 0=0)
    (hsmall : 2^16*(p : ℝ)^2*(s : ℝ)^2*η≤1)
    (x b : ZMod s → ℝ) (hx : Matrix.mulVec (realMatrix s t p u) x=b) (hb : ∀ i, |b i|≤1/2)
    (j : ZMod s) :
    |bandSolveM rd (realMatrix s t p u) univ (foldOrder s) b j-x j|≤
      62000*(p : ℝ)^3*(s : ℝ)^2*η := by
  have hpR : (2 : ℝ)≤p := by exact_mod_cast hp
  have hs1 : (1 : ℝ)≤s := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne s)
  have hη : 0≤η := le_trans (abs_nonneg _) (hrd 0)
  have hμ : (0 : ℝ)<1/(8*(p : ℝ)) := by positivity
  have hA := matrix_gap s t hst hα p u hp hwidth hαu hθ hgap hbudget
  have hinv : StageInv (realMatrix s t p u) univ (1/(8*(p : ℝ))) 2 :=
    ⟨hA, fun i _ => row_mass s t hst hα p u hp hwidth hαu hθ hgap hbudget i⟩
  have hcard : ((univ : Finset (ZMod s)).card : ℝ)≤s := by simp [ZMod.card]
  have hlen := foldOrder_length s
  have hsol : Solves (realMatrix s t p u) univ x b := solves_of_mulVec s t p u x b hx
  have hX : ∀ i∈(univ : Finset (ZMod s)), |x i|≤4*p := by
    intro i hi
    have h := solves_bound _ _ _ hμ hA x b hsol (1/2) (fun i _ => hb i) i hi
    rw [div_div_eq_mul_div, div_one] at h
    linarith
  obtain ⟨hm', hmu', hMη, hsm', hfin⟩ := bandM_arith (p : ℝ) (s : ℝ) η hpR hs1 hη hsmall
  have key := bandSolveM_error rd η hrd hrd0 (foldPos s) (foldPos_injective s)
    (realMatrix s t p u) univ (1/(8*(p : ℝ))) 2 3 s hμ (by norm_num) (by norm_num) hinv hcard
    (foldOrder s) (foldOrder_toFinset s) (foldOrder_sorted s) (by rw [hlen]; exact hm')
    (by rw [hlen]; exact hmu') hMη x b hsol (4*p) (by positivity) hX (by rw [hlen]; exact hsm')
    j (mem_univ j)
  rw [hlen] at key
  exact key.trans hfin

end IntegerMultBounds.NLogN.PhaseCellMatrix
