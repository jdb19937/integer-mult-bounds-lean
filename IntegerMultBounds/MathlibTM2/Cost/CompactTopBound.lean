module

public import IntegerMultBounds.MathlibTM2.Cost.CompactLayerBound
public import IntegerMultBounds.MathlibTM2.Node.CompactTopProc
import IntegerMultBounds.MathlibTM2.Fast.SynSel
public import IntegerMultBounds.MathlibTM2.Fast.SynRec
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan

/-! Geometric summation and exact control-cost accounting for compact top calls.
The control budget below retains every stage of the actual top runner. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds IntegerMultBounds.Networks IntegerMultBounds.Machine
open IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.LayerMachine
open IntegerMultBounds.MathlibTM2.Fast
noncomputable section

/-- The level-zero leaf term is absorbed uniformly for base-m digits. -/
theorem compactDigit_envelope {a b lam tau C g u : ℝ} (j : ℕ)
    (ha : 0≤a) (hb : 1<b) (hl : 0≤lam) (ht : 0≤tau)
    (hal : Real.logb b a<lam) (hC : 0≤C) (hg : 1≤g)
    (hu : 0≤u) (hub : u≤b) :
    C*(b^j*u)^lam*g^tau+C*a^j*u ≤
      C*(b^lam+b)*g^tau*(b^lam)^j := by
  have hb0 := (lt_trans zero_lt_one hb).le
  have hx := (Recurrence.lt_rpow_of_logb_lt ha hb hal).le
  have hp : a^j≤(b^lam)^j := pow_le_pow_left₀ ha hx j
  have hu' : u^lam≤b^lam := Real.rpow_le_rpow hu hub hl
  have hg' : 1≤g^tau := Real.one_le_rpow hg ht
  have hg0 : 0≤g^tau := by positivity
  rw [Real.mul_rpow (pow_nonneg hb0 j) hu, Recurrence.pow_rpow_eq hb0]
  have hi : C*((b^lam)^j*u^lam)*g^tau ≤ C*((b^lam)^j*b^lam)*g^tau := by gcongr
  have hf : C*a^j*u ≤ C*(b^lam)^j*b := by gcongr
  have hf' : C*(b^lam)^j*b ≤ C*(b^lam)^j*b*g^tau := by
    exact le_mul_of_one_le_right (by positivity) hg'
  calc _ ≤ C*((b^lam)^j*b^lam)*g^tau+C*(b^lam)^j*b*g^tau := add_le_add hi (hf.trans hf')
    _ = _ := by ring

/-- A geometric sum with a fixed coefficient, with no factor for the number of digits. -/
theorem compactGeometric_sum {x : ℝ} (hx : 1<x) (J : ℕ) :
    (∑ j ∈ Finset.range (J+1), x^j) ≤ x/(x-1)*x^J := by
  have hx0 : 0≤x := by linarith
  have hd : 0<x-1 := by linarith
  induction J with
  | zero =>
    simp only [Nat.zero_add, Finset.sum_range_one, pow_zero, mul_one]
    exact (le_div_iff₀ hd).mpr (by linarith)
  | succ J ih =>
    rw [Finset.sum_range_succ]
    calc _ ≤ x/(x-1)*x^J+x^(J+1) := add_le_add ih le_rfl
      _ = x/(x-1)*x^(J+1) := by field_simp; ring

/-- A fixed power-of-two coefficient for the sum over all nonzero digits. -/
def compactDigitSumConst (C b lam : ℝ) : ℝ :=
  compactLayerDyadic (C*(b^lam+b)*(b^lam/(b^lam-1)))

/-- Sum of closed layer envelopes over any subset of digit levels. -/
theorem compactDigit_sum {a b lam tau C g active : ℝ} (u : ℕ→ℝ)
    (S : Finset ℕ) (J : ℕ) (ha : 0≤a) (hb : 1<b) (hl : 0<lam)
    (ht : 0≤tau) (hal : Real.logb b a<lam) (hC : 0≤C) (hg : 1≤g)
    (hu : ∀ j∈S,0≤u j ∧ u j≤b) (hS : S⊆Finset.range (J+1))
    (hactive : b^J≤active) :
    (∑ j∈S, (C*(b^j*u j)^lam*g^tau+C*a^j*u j)) ≤
      compactDigitSumConst C b lam*active^lam*g^tau := by
  have hb0 : 0≤b := by linarith
  have hx : 1<b^lam := Real.one_lt_rpow hb hl
  have hg0 : 0≤g^tau := by positivity
  have hc0 : 0≤C*(b^lam+b)*g^tau := by positivity
  have hper := Finset.sum_le_sum (s:=S) (fun j hj =>
    compactDigit_envelope j ha hb hl.le ht hal hC hg (hu j hj).1 (hu j hj).2)
  have hsub : (∑ j∈S,(b^lam)^j) ≤ ∑ j∈Finset.range (J+1),(b^lam)^j :=
    Finset.sum_le_sum_of_subset_of_nonneg hS (fun _ _ _ => by positivity)
  have hs := hsub.trans (compactGeometric_sum hx J)
  have hp : (b^lam)^J≤active^lam := by
    rw [← Recurrence.pow_rpow_eq hb0]
    exact Real.rpow_le_rpow (pow_nonneg hb0 J) hactive hl.le
  have hcoef : C*(b^lam+b)*(b^lam/(b^lam-1))≤compactDigitSumConst C b lam :=
    compactLayerDyadic_le _
  have hactive0 : 0≤active := (pow_nonneg hb0 J).trans hactive
  have hcoef0 : 0≤C*(b^lam+b)*(b^lam/(b^lam-1)) := by positivity
  calc
    _ ≤ C*(b^lam+b)*g^tau*(∑ j∈S,(b^lam)^j) := by
      simpa only [Finset.mul_sum] using hper
    _ ≤ C*(b^lam+b)*g^tau*((b^lam/(b^lam-1))*(b^lam)^J) := mul_le_mul_of_nonneg_left hs hc0
    _ = (C*(b^lam+b)*(b^lam/(b^lam-1)))*(b^lam)^J*g^tau := by ring
    _ ≤ (C*(b^lam+b)*(b^lam/(b^lam-1)))*active^lam*g^tau := by gcongr
    _ ≤ compactDigitSumConst C b lam*active^lam*g^tau := by gcongr

/-- Actual digit construction, including its reverse order and zero-digit skips. -/
theorem compactSynPcs_sum (K X D oS J t : ℕ) (f : TopPc→ℝ) :
    ((synPcs K X D oS J t).map f).sum =
      ∑ j∈(Finset.range t).filter (fun j => synDg D j≠0), f (synPc K X D oS J j) := by
  induction t with
  | zero => simp [synPcs]
  | succ t ih =>
    rw [Finset.sum_filter, Finset.sum_range_succ]
    rw [Finset.sum_filter] at ih
    unfold synPcs at ih ⊢
    rw [List.range_succ, List.reverse_append]
    by_cases hz : synDg D t=0
    · simpa [List.filterMap_append,hz] using ih
    · simp only [List.reverse_cons,List.reverse_nil,List.nil_append,List.filterMap_append,
        List.filterMap_cons,List.filterMap_nil,hz,↓reduceIte,List.map_append,List.map_cons,
        List.map_nil,List.sum_append,List.sum_cons,List.sum_nil]
      rw [ih]
      rw [ite_eq_left hz]
      ring

/-- The actual nonzero digit support lies below the base-m logarithm. -/
theorem compactSynDigits_support (D : ℕ) :
    (Finset.range D).filter (fun j => synDg D j≠0) ⊆ Finset.range (Nat.log m D+1) := by
  intro j hj
  have hpos := synDg_pos_div (Finset.mem_filter.mp hj).2
  have hpow : m^j≤D := (Nat.div_pos_iff).mp hpos |>.2
  exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.le_log_of_pow_le (by norm_num [m]) hpow))

/-- Closed layer envelopes summed over the actual emitted active digits. -/
theorem compactSynPcs_envelope_sum (K X D oS J : ℕ)
    {a lam tau C g : ℝ} (hD : D≠0) (ha : 0≤a) (hl : 0<lam)
    (ht : 0≤tau) (hal : Real.logb (m:ℝ) a<lam) (hC : 0≤C) (hg : 1≤g) :
    ((synPcs K X D oS J D).map (fun pc =>
      C*((m:ℝ)^pc.j*pc.u)^lam*g^tau+C*a^pc.j*pc.u)).sum ≤
      compactDigitSumConst C m lam*(D:ℝ)^lam*g^tau := by
  rw [compactSynPcs_sum]
  exact compactDigit_sum (fun j => (synDg D j:ℝ)) _ (Nat.log m D) ha
    (by norm_num [m]) hl ht hal hC hg
    (fun j _ => ⟨Nat.cast_nonneg _, by exact_mod_cast (Nat.mod_lt (D/m^j) (by norm_num [m] : 0<m)).le⟩)
    (compactSynDigits_support D) (by exact_mod_cast Nat.pow_log_le_self m hD)

/-- Removing call costs leaves exactly the piece records, row fields, cleanup,
and loop controls of the executable dispatcher. -/
theorem compactTopPcsCost_split (cfg : List ℕ) (K : ℕ) (cc : TopPc→ℕ) (pcs : List TopPc) :
    compactTopPcsCost cfg K cc pcs =
      compactTopPcsCost cfg K (fun _ => 0) pcs+(pcs.map cc).sum := by
  induction pcs with
  | nil => simp [compactTopPcsCost]
  | cons pc pcs ih =>
    simp only [compactTopPcsCost,List.map_cons,List.sum_cons,ih,compactTopPcCost]
    omega

/-- Full actual top control cost, including both phases, all padding, reservation
record processing, widening, unit, shift, and all descriptor reads. -/
def compactTopControlCost
    (w w' s n a R r K ρ q aT oS D R₂ : ℕ) (pcs : List TopPc) : ℕ :=
  compactTopCost w w' s n a R r K ρ q aT oS D R₂ pcs 0 (fun _ => 0)

/-- Exact accounting: no reservation/control cost disappears in extracting the
recursive calls and the top kernel. -/
theorem compactTopCost_split
    (w w' s n a R r K ρ q aT oS D R₂ kc : ℕ) (pcs : List TopPc) (cc : TopPc→ℕ) :
    compactTopCost w w' s n a R r K ρ q aT oS D R₂ pcs kc cc =
      compactTopControlCost w w' s n a R r K ρ q aT oS D R₂ pcs+kc+(pcs.map cc).sum := by
  unfold compactTopControlCost compactTopCost compactTopBlockCost compactTopKerSCost
  rw [compactTopPcsCost_split]
  omega

end
end IntegerMultBounds.MathlibTM2.Cost
