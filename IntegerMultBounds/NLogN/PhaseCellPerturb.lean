module

public import IntegerMultBounds.NLogN.PhaseCellFoldSolve
public import IntegerMultBounds.NLogN.ToeplitzLocal

/-! The machine band solve of a perturbation of the phase-cell matrix. The tape
machine factors a grid rounding `Ã` of `realMatrix`. If every row of `Ã - A`
has absolute sum at most `ε ≤ 1/(32p)`, then `Ã` keeps margin `1/(16p)` and
mass at most `9/4`; the machine solve of `Ã` is within `62000 (2p)³ s² η'` of the
exact solution of `Ã`, which is within `64 p² ε` of the exact solution of `A`. -/
@[expose] public section
namespace IntegerMultBounds.NLogN.PhaseCellMatrix

open scoped BigOperators
open Finset SchurDominance
variable (s t : ℕ) [NeZero s] [NeZero t]

/-- Dominance and mass of a row-sum perturbation of the phase-cell matrix. -/
theorem perturb_stageInv (hst : s<t) {α d : ℝ} (hα : 0<α)
    (p u : ℕ) (hp : 2≤p) (hwidth : 8*p≤2^u) (hαu : α^2=(u : ℝ))
    (hθ : 1/(4*(p : ℝ))≤(t : ℝ)/s-1)
    (hgap : (1 : ℝ)/4≤d*((t : ℝ)/s-1)) (hbudget : α^2*d≤p)
    (At : Matrix (ZMod s) (ZMod s) ℝ) (ε : ℝ)
    (hε : ∀ j, ∑ l, |At j l-realMatrix s t p u j l|≤ε) (hε1 : ε≤1/(32*(p : ℝ))) :
    StageInv At univ (1/(8*(2*(p : ℝ)))) (9/4) := by
  have hpR : (2 : ℝ)≤p := by exact_mod_cast hp
  have hA := matrix_gap s t hst hα p u hp hwidth hαu hθ hgap hbudget
  refine ⟨fun i _ => ?_, fun i _ => ?_⟩
  · have hAi := hA i (mem_univ i)
    have hsplit := sum_erase_add univ (fun l => |At i l-realMatrix s t p u i l|) (mem_univ i)
    have hoff : ∑ l∈univ.erase i, |At i l|≤∑ l∈univ.erase i, |realMatrix s t p u i l|+
        ∑ l∈univ.erase i, |At i l-realMatrix s t p u i l| := by
      rw [← sum_add_distrib]
      refine sum_le_sum fun l _ => ?_
      have := abs_add_le (realMatrix s t p u i l) (At i l-realMatrix s t p u i l)
      rw [add_sub_cancel] at this; linarith
    have hdiag := neg_abs_le (At i i-realMatrix s t p u i i)
    have hεi := hε i
    have h0 : 0≤∑ l∈univ.erase i, |At i l-realMatrix s t p u i l| := sum_nonneg fun _ _ => abs_nonneg _
    have hm : 1/(8*(2*(p : ℝ)))=1/(8*(p : ℝ))-1/(16*(p : ℝ)) := by field_simp; ring
    have h32 : 1/(32*(p : ℝ))≤1/(16*(p : ℝ)) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]; linarith
    rw [hm]; linarith
  · have hrow := row_mass s t hst hα p u hp hwidth hαu hθ hgap hbudget i
    have hle : ∑ l, |At i l|≤∑ l, |realMatrix s t p u i l|+∑ l, |At i l-realMatrix s t p u i l| := by
      rw [← sum_add_distrib]
      refine sum_le_sum fun l _ => ?_
      have := abs_add_le (realMatrix s t p u i l) (At i l-realMatrix s t p u i l)
      rw [add_sub_cancel] at this; linarith
    have h32 : 1/(32*(p : ℝ))≤1/4 := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]; linarith
    linarith [hε i]

/-- The exact solutions of `A` and of its perturbation differ by at most `64 p² ε`. -/
theorem perturb_solution (hst : s<t) {α d : ℝ} (hα : 0<α)
    (p u : ℕ) (hp : 2≤p) (hwidth : 8*p≤2^u) (hαu : α^2=(u : ℝ))
    (hθ : 1/(4*(p : ℝ))≤(t : ℝ)/s-1)
    (hgap : (1 : ℝ)/4≤d*((t : ℝ)/s-1)) (hbudget : α^2*d≤p)
    (At : Matrix (ZMod s) (ZMod s) ℝ) (ε : ℝ)
    (hε : ∀ j, ∑ l, |At j l-realMatrix s t p u j l|≤ε) (hε1 : ε≤1/(32*(p : ℝ)))
    (x xt b : ZMod s → ℝ) (hx : Matrix.mulVec (realMatrix s t p u) x=b)
    (hxt : Solves At univ xt b) (hb : ∀ i, |b i|≤1/2) (i : ZMod s) :
    |xt i-x i|≤64*(p : ℝ)^2*ε := by
  have hpR : (2 : ℝ)≤p := by exact_mod_cast hp
  have hμ : (0 : ℝ)<1/(8*(p : ℝ)) := by positivity
  have hA := matrix_gap s t hst hα p u hp hwidth hαu hθ hgap hbudget
  have hX : ∀ l, |x l|≤4*p := by
    intro l
    have h := solves_bound _ _ _ hμ hA x b (solves_of_mulVec s t p u x b hx) (1/2)
      (fun i _ => hb i) l (mem_univ l)
    rw [div_div_eq_mul_div, div_one] at h
    linarith
  have hε0 : 0≤ε := le_trans (sum_nonneg fun _ _ => abs_nonneg _) (hε i)
  have hinv := perturb_stageInv s t hst hα p u hp hwidth hαu hθ hgap hbudget At ε hε hε1
  have hsol : Solves At univ (fun l => xt l-x l)
      (fun j => ∑ l, (realMatrix s t p u j l-At j l)*x l) := by
    intro j _
    dsimp only
    have h1 := hxt j (mem_univ j)
    have h2 : ∑ l, realMatrix s t p u j l*x l=b j := by
      rw [← hx]; rfl
    rw [show (∑ l∈univ, At j l*(xt l-x l))=(∑ l, At j l*xt l)-∑ l, At j l*x l by
        rw [← sum_sub_distrib]; congr 1; funext l; ring,
      show (∑ l, (realMatrix s t p u j l-At j l)*x l)=(∑ l, realMatrix s t p u j l*x l)-
        ∑ l, At j l*x l by rw [← sum_sub_distrib]; congr 1; funext l; ring, h2]
    exact congrArg (· - ∑ l, At j l*x l) h1
  have hres : ∀ j∈(univ : Finset (ZMod s)), |∑ l, (realMatrix s t p u j l-At j l)*x l|≤ε*(4*p) := by
    intro j _
    calc |∑ l, (realMatrix s t p u j l-At j l)*x l|
        ≤∑ l, |realMatrix s t p u j l-At j l| * (4*p) := by
          refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun l _ => ?_)
          rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hX l) (abs_nonneg _)
      _=(∑ l, |At j l-realMatrix s t p u j l|)*(4*p) := by
          rw [sum_mul]; congr 1; funext l; rw [abs_sub_comm]
      _≤ε*(4*p) := mul_le_mul_of_nonneg_right (hε j) (by positivity)
  have h := solves_bound At univ _ (by positivity) hinv.1 _ _ hsol _ hres i (mem_univ i)
  have e : ε*(4*(p : ℝ))/(1/(8*(2*(p : ℝ))))=64*(p : ℝ)^2*ε := by field_simp; ring
  rw [e] at h
  exact h

/-- The tape machine's band solve of a perturbation `Ã` of the phase-cell matrix
in folded order: within `62000 (2p)³ s² η' + 64 p² ε` of the exact solution of
the phase-cell system, where `η' = η(1+180/β²)` and `β ≤ 1/(32p)`. -/
theorem bandSolveMach_perturb (hst : s<t) {α d : ℝ} (hα : 0<α)
    (p u : ℕ) (hp : 2≤p) (hwidth : 8*p≤2^u) (hαu : α^2=(u : ℝ))
    (hθ : 1/(4*(p : ℝ))≤(t : ℝ)/s-1)
    (hgap : (1 : ℝ)/4≤d*((t : ℝ)/s-1)) (hbudget : α^2*d≤p)
    (At : Matrix (ZMod s) (ZMod s) ℝ) (ε : ℝ)
    (hε : ∀ j, ∑ l, |At j l-realMatrix s t p u j l|≤ε) (hε1 : ε≤1/(32*(p : ℝ)))
    (rd : ℝ → ℝ) (η : ℝ) (hrd : ∀ x, |rd x-x|≤η) (hrd0 : rd 0=0)
    (β : ℝ) (hβ : 0<β) (hβp : β≤1/(8*(2*(p : ℝ)))/2) (hηβ : 5*η≤2*(β/4)/9) (K : ℕ)
    (hK : (1-β/4/2)^(2^K)≤3*(5*η)/(β/4))
    (hsmall : 2^16*(2*(p : ℝ))^2*(s : ℝ)^2*(η*(1+60*3/β^2))≤1)
    (x b : ZMod s → ℝ) (hx : Matrix.mulVec (realMatrix s t p u) x=b) (hb : ∀ i, |b i|≤1/2)
    (j : ZMod s) :
    |bandSolveG rd (machMul rd K) (fun c => NewtonRecip.newtonR rd c K) At univ (foldOrder s) b j-x j|≤
      62000*(2*(p : ℝ))^3*(s : ℝ)^2*(η*(1+60*3/β^2))+64*(p : ℝ)^2*ε := by
  have hpR : (2 : ℝ)≤p := by exact_mod_cast hp
  have hqR : (2 : ℝ)≤2*(p : ℝ) := by linarith
  have hs1 : (1 : ℝ)≤s := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne s)
  have hη : 0≤η := le_trans (abs_nonneg _) (hrd 0)
  have hext : 0≤η*(60*3/β^2) := by positivity
  have hle : η≤η*(1+60*3/β^2) := by nlinarith
  set η' := η*(1+60*3/β^2) with hη'
  have hrd' : ∀ x, |rd x-x|≤η' := fun x => (hrd x).trans hle
  have hμ : (0 : ℝ)<1/(8*(2*(p : ℝ))) := by positivity
  have hinv := perturb_stageInv s t hst hα p u hp hwidth hαu hθ hgap hbudget At ε hε hε1
  have hinv' : StageInv At univ (1/(8*(2*(p : ℝ)))) (9/4) := hinv
  obtain ⟨R, hR⟩ := exists_solver At univ _ hμ hinv.1
  set xt := R b
  have hxt := hR b
  have hcard : ((univ : Finset (ZMod s)).card : ℝ)≤s := by simp [ZMod.card]
  have hlen := foldOrder_length s
  have hX : ∀ i∈(univ : Finset (ZMod s)), |xt i|≤4*(2*(p : ℝ)) := by
    intro i hi
    have h := solves_bound _ _ _ hμ hinv.1 xt b hxt (1/2) (fun i _ => hb i) i hi
    rw [div_div_eq_mul_div, div_one] at h
    linarith
  obtain ⟨hm', hmu', hMη, hsm', hfin⟩ := bandM_arith (2*(p : ℝ)) (s : ℝ) η' hqR hs1 (by positivity) hsmall
  -- mass `9/4` instead of `2`
  have hm'' : 9/4+(foldOrder s).length*(η'*(s+3))≤3 := by
    rw [hlen]
    have hη0 : 0≤η' := by positivity
    have hss : (s : ℝ)≤(s : ℝ)^2 := by nlinarith
    have h1 : (s : ℝ)*(η'*(s+3))≤4*((s : ℝ)^2*η') := by
      have e : (s : ℝ)*(η'*(s+3))=(s : ℝ)^2*η'+3*((s : ℝ)*η') := by ring
      have := mul_le_mul_of_nonneg_right hss hη0
      rw [e]; linarith
    have hq4 : (1 : ℝ)≤(2*(p : ℝ))^2 := by nlinarith
    have h3 : 2^16*((s : ℝ)^2*η')≤1 := by
      calc 2^16*((s : ℝ)^2*η')=1*(2^16*((s : ℝ)^2*η')) := (one_mul _).symm
        _≤(2*(p : ℝ))^2*(2^16*((s : ℝ)^2*η')) := mul_le_mul_of_nonneg_right hq4 (by positivity)
        _=2^16*(2*(p : ℝ))^2*(s : ℝ)^2*η' := by ring
        _≤1 := hsmall
    linarith
  have hgood := bandSolveG_congr rd (NewtonRecip.recipMul rd 3 β K) η' hrd'
    (NewtonRecip.recipMul_err rd η hrd 3 β (by norm_num) hβ hηβ K hK) (machMul rd K)
    (NewtonRecip.recipNewton rd β K) (fun c => NewtonRecip.newtonR rd c K) At univ _ (9/4) 3 s hμ
    (by norm_num) (by norm_num) hinv' hcard (foldOrder s) (foldOrder_toFinset s) hm''
    (by rw [hlen]; exact hmu')
    (fun a c ha hc hc3 => by
      simp only [machMul, NewtonRecip.recipMul, hβp.trans hc, hc3, ha, and_self, ite_true])
    (fun c hc hc3 => by
      simp only [NewtonRecip.recipNewton, hβp.trans hc, hc3, and_self, ite_true]) b
  rw [hgood]
  have key := bandSolveG_error rd (NewtonRecip.recipMul rd 3 β K) (NewtonRecip.recipNewton rd β K)
    η' (3*η') hrd' hrd0 (NewtonRecip.recipMul_err rd η hrd 3 β (by norm_num) hβ hηβ K hK)
    (NewtonRecip.recipMul_zero rd hrd0 3 β K) (foldPos s) (foldPos_injective s) At univ _ (9/4) 3 s
    hμ (by norm_num) (by norm_num) hinv' hcard (foldOrder s) (foldOrder_toFinset s)
    (foldOrder_sorted s) hm'' (by rw [hlen]; exact hmu')
    (fun c hc hc3 => by
      have h := NewtonRecip.recipNewton_residual rd η hrd β hβ hηβ K hK c (hβp.trans hc) hc3
      have e : 3*(η*(1+60*3/β^2))=3*η+3*(180*η/β^2) := by ring
      have h0 : 0≤180*η/β^2 := by positivity
      rw [hη', e]; linarith)
    hMη xt b hxt _ (by positivity) hX (by rw [hlen]; exact hsm') j (mem_univ j)
  rw [hlen] at key
  have hpert := perturb_solution s t hst hα p u hp hwidth hαu hθ hgap hbudget At ε hε hε1 x xt b hx
    hxt hb j
  have := abs_sub_le (bandSolveG rd (NewtonRecip.recipMul rd 3 β K) (NewtonRecip.recipNewton rd β K)
    At univ (foldOrder s) b j) (xt j) (x j)
  linarith [key.trans hfin]

end IntegerMultBounds.NLogN.PhaseCellMatrix
