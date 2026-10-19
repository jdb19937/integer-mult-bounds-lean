module

public import IntegerMultBounds.MathlibTM2.M8.Machine.ArbitraryWidthPieceRun
public import Mathlib.Tactic.IrreducibleDef
public import IntegerMultBounds.MathlibTM2.M8.Machine.ArbitrarySliceStepBudget
public import IntegerMultBounds.MathlibTM2.M8.Machine.ArbitraryWidthPieceConsume
public import IntegerMultBounds.MathlibTM2.M8.Machine.ArbitraryWidthPieceExecution
public import IntegerMultBounds.MathlibTM2.M8.Machine.ArbitraryWidthPiecePrefix
public import IntegerMultBounds.MathlibTM2.M8.Machine.ArbitraryWidthPieces
public import IntegerMultBounds.MathlibTM2.M8.Machine.BudgetBound

/-! The real dispatcher adds only linear-width physical control overhead to
the fully paid power-piece slice budgets. -/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8.Machine.ArbitraryWidthPieceCost
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.Networks
variable [Net]
noncomputable section
open Networks
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
open RecursiveInterchangeLayout (Descriptor volume)
open RecursiveChildQuotientsConstant (bits)
open ArbitraryWidthPieceLoop (count digit)

omit [Net] in
theorem bits_length (n : ℕ) : (bits n).length ≤ n+1 := by
  have h := GrowingCounterData.canonical_width (bits n) (RecursiveChildQuotientsConstant.bits_canonical n)
  rw [RecursiveChildQuotientsConstant.bits_value] at h
  exact h.trans (Nat.add_le_add_right (Nat.log2_le_self n) 1)

theorem last_power (N : ℕ) : Machine.width^(count Machine.width N) ≤ Machine.width*(N+1) := by
  by_cases hN : N = 0
  · simp only [count,hN,↓reduceIte,pow_zero,zero_add,mul_one]
    exact width_pos
  · simp only [count,ite_eq_right hN,pow_succ]
    have h := Nat.pow_log_le_self Machine.width hN
    nlinarith

theorem power_sum (r : ℕ) :
    (∑ i ∈ Finset.range r, Machine.width^(i+1)) ≤ 2*Machine.width^r := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [Finset.sum_range_succ,pow_succ]
    have h2 : 2*Machine.width^r ≤ Machine.width^r*Machine.width := by
      rw [Nat.mul_comm]
      exact Nat.mul_le_mul_left _ two_le_width
    omega

theorem consume_bound (v : Descriptor) (hp : v.Positive) (i : ℕ)
    (hi : i < count Machine.width v.width) :
    ArbitraryWidthPieceExecution.consumeCost v i ≤
      digit Machine.width v.width i*ArbitrarySliceStepBudget.budget i (volume prime v)+
      6*digit Machine.width v.width i+(9*Machine.width+34)+120*Machine.width^(i+1) := by
  have hV := RecursiveAffinePrepare.volume_positive Shared50ModularControl.prime_prime.two_le v hp
  have hwV : v.width ≤ volume prime v :=
    RecursiveHeaderBounds.values_le_volume Shared50ModularControl.prime_prime.two_le v hp 3
  have hpw := ArbitraryWidthPiecePrefix.selected_power_le Machine.width v.width i two_le_width hi
  have hfit := (ArbitraryWidthPiecePrefix.step_fit Machine.width v.width i).trans hwV
  have h := ArbitraryWidthPieceConsume.cost_bound i (volume prime v)
    (ArbitraryWidthPiecePrefix.offset Machine.width v.width i) (Machine.width^i) (digit Machine.width v.width i)
    (bits (ArbitraryWidthPiecePrefix.offset Machine.width v.width i))
    (FixedBasePowerStep.bits Machine.width i) (bits (digit Machine.width v.width i))
    hV (hpw.trans hwV) hfit (RecursiveChildQuotientsConstant.bits_value _)
    (FixedBasePowerStep.bits_value _ _) (RecursiveChildQuotientsConstant.bits_canonical _)
    (FixedBasePowerStep.bits_canonical _ _)
  have hd : digit Machine.width v.width i < Machine.width := Nat.mod_lt _ width_pos
  have hl := bits_length (digit Machine.width v.width i)
  unfold ArbitraryWidthPieceExecution.consumeCost
  nlinarith

omit [Net] in
/-- Parameterizing the sealed constant prevents the kernel from evaluating
the fixed base's unary writer merely to compare two budget expressions.
`constant_def` records the complete explicit value. -/
irreducible_def constantWith (W O : ℕ) : ℕ := (2*(W+1)+20)*W+249*W+(3*(W+1)+6)+12+2*9+79+
  O

def constant := constantWith Machine.width (ArbitraryWidthPieceLoop.overheadConstant Machine.width)

theorem constant_def : constant =
  (2*(Machine.width+1)+20)*Machine.width+249*Machine.width+(3*(Machine.width+1)+6)+12+2*9+79+
  ArbitraryWidthPieceLoop.overheadConstant Machine.width := constantWith_def _ _

private theorem arithmetic (N H L Z A C I O E S Q D R P F EB AB CB IB : ℕ)
    (hsum : S ≤ Q+6*D+(9*Machine.width+34)*R+120*P)
    (hd : D ≤ 2*N) (hr : R ≤ N) (hp : P ≤ 2*F) (hf : F ≤ Machine.width*(N+1))
    (hH : H ≤ N+1) (hL : L ≤ N+1) (hZ : Z = 0)
    (hE : E ≤ EB) (hA : A ≤ AB) (hC : C ≤ CB) (hI : I ≤ IB) :
    (2*H+A+C+2*I+9)+(O*(N+1)+S)+(E*F+2*L+2*Z+10)+2 ≤
      Q+(EB*Machine.width+249*Machine.width+AB+CB+2*IB+79+O)*(N+1) := by
  subst Z
  have hfin := (Nat.mul_le_mul_right F hE).trans (Nat.mul_le_mul_left EB hf)
  have hAB := Nat.mul_le_mul_left AB (show 1 ≤ N+1 by omega)
  have hCB := Nat.mul_le_mul_left CB (show 1 ≤ N+1 by omega)
  have hIB := Nat.mul_le_mul_left IB (show 1 ≤ N+1 by omega)
  have hWR := Nat.mul_le_mul_left Machine.width hr
  simp only [Nat.add_mul,Nat.mul_add,Nat.mul_assoc,Nat.mul_one] at hfin hAB hCB hIB hsum hf hWR ⊢
  omega

omit [Net] in
theorem writer_cost (n : ℕ) : RecursiveChildQuotientsConstant.cost n ≤ 3*(n+1)+6 := by
  unfold RecursiveChildQuotientsConstant.cost
  exact Nat.add_le_add_right (Nat.mul_le_mul_left 3 (bits_length n)) 6

theorem consume_sum (v : Descriptor) (hp : v.Positive) : (∑ i ∈ Finset.range (count Machine.width v.width),
    ArbitraryWidthPieceExecution.consumeCost v i) ≤
      (∑ i ∈ Finset.range (count Machine.width v.width),
        digit Machine.width v.width i*ArbitrarySliceStepBudget.budget i (volume prime v))+
      6*(∑ i ∈ Finset.range (count Machine.width v.width),digit Machine.width v.width i)+
      (9*Machine.width+34)*count Machine.width v.width+
      120*(∑ i ∈ Finset.range (count Machine.width v.width),Machine.width^(i+1)) := by
    calc
      _ ≤ ∑ i ∈ Finset.range (count Machine.width v.width),
          (digit Machine.width v.width i*ArbitrarySliceStepBudget.budget i (volume prime v)+
            6*digit Machine.width v.width i+(9*Machine.width+34)+120*Machine.width^(i+1)) := by
        exact Finset.sum_le_sum fun i hi => consume_bound v hp i (Finset.mem_range.mp hi)
      _ = _ := by simp [Finset.sum_add_distrib,Finset.mul_sum,Nat.mul_comm]

theorem digit_sum (v : Descriptor) : (∑ i ∈ Finset.range (count Machine.width v.width),digit Machine.width v.width i) ≤ 2*v.width := by
    apply le_trans (Finset.sum_le_sum ?_)
      (ArbitraryWidthPieceLoop.remaining_sum Machine.width v.width (count Machine.width v.width) two_le_width)
    intro i _
    exact Nat.mod_le _ _

omit [Net] in
theorem header_length (v : Descriptor) (hs : Fin 6 → List Bool)
    (hv : RecursiveDimensionBank.Headers v hs) : (hs 3).length ≤ v.width+1 := by
  have hcan := GrowingCounterData.canonical_width (hs 3) (hv.2 3)
  have he : Counter.value (hs 3) = v.width := hv.1 3
  rw [he] at hcan
  exact hcan.trans (Nat.add_le_add_right (Nat.log2_le_self _) 1)

private theorem cost_bound_abstract (v : Descriptor) (hs : Fin 6 → List Bool) (hp : v.Positive)
    (hv : RecursiveDimensionBank.Headers v hs) (A L O : ℕ)
    (hA : RecursiveChildQuotientsConstant.cost Machine.width = A)
    (hL : (bits Machine.width).length = L)
    (hO : ArbitraryWidthPieceLoop.overheadConstant Machine.width = O) :
    ArbitraryWidthPieceRun.cost v hs ≤
      (∑ i ∈ Finset.range (count Machine.width v.width),
        digit Machine.width v.width i*ArbitrarySliceStepBudget.budget i (volume prime v))+
      constant*(v.width+1) := by
  unfold ArbitraryWidthPieceRun.cost
  rw [constant_def]
  rw [hA,hL,hO]
  exact arithmetic v.width (hs 3).length (bits v.width).length (bits 0).length
    A (RecursiveChildQuotientsConstant.cost 1)
    (RecursiveChildQuotientsConstant.cost 0) O
    (2*L+20)
    (∑ i ∈ Finset.range (count Machine.width v.width), ArbitraryWidthPieceExecution.consumeCost v i)
    (∑ i ∈ Finset.range (count Machine.width v.width),
      digit Machine.width v.width i*ArbitrarySliceStepBudget.budget i (volume prime v))
    (∑ i ∈ Finset.range (count Machine.width v.width),digit Machine.width v.width i)
    (count Machine.width v.width)
    (∑ i ∈ Finset.range (count Machine.width v.width),Machine.width^(i+1))
    (Machine.width^(count Machine.width v.width))
    (2*(Machine.width+1)+20) (3*(Machine.width+1)+6) 12 9
    (consume_sum v hp) (digit_sum v) (ArbitraryWidthPieceLoop.count_le _ _)
    (power_sum _) (last_power _) (header_length v hs hv) (bits_length _) (by
      rw [RecursiveChildQuotientsConstant.bits_eq_advance]; rfl)
    (Nat.add_le_add_right (Nat.mul_le_mul_left 2 (by simpa only [hL] using bits_length Machine.width)) 20)
    (by simpa only [hA] using writer_cost Machine.width) (writer_cost 1) (writer_cost 0)

theorem cost_bound (v : Descriptor) (hs : Fin 6 → List Bool) (hp : v.Positive)
    (hv : RecursiveDimensionBank.Headers v hs) :
    ArbitraryWidthPieceRun.cost v hs ≤
      (∑ i ∈ Finset.range (count Machine.width v.width),
        digit Machine.width v.width i*ArbitrarySliceStepBudget.budget i (volume prime v))+
      constant*(v.width+1) := by
  exact cost_bound_abstract v hs hp hv _ _ _ rfl rfl rfl

def coefficient : ℝ := ArbitrarySliceStepBudget.constant+2*(constant : ℝ)

theorem coefficient_positive : 0 < coefficient := by
  have h := ArbitrarySliceStepBudget.constant_positive
  have hc : (0 : ℝ) ≤ constant := Nat.cast_nonneg _
  unfold coefficient
  linarith only [h,hc]

theorem cost_tau (v : Descriptor) (hs : Fin 6 → List Bool) (hp : v.Positive)
    (hv : RecursiveDimensionBank.Headers v hs) (hN : 0 < v.width) :
    (ArbitraryWidthPieceRun.cost v hs : ℝ) ≤
      coefficient*(volume prime v : ℝ)*(v.width : ℝ)^BudgetBound.tau := by
  have hn : v.width ≠ 0 := by omega
  have hslices := ArbitrarySliceStepBudget.sum_bound (volume prime v) v.width
    (Nat.log Machine.width v.width) (Nat.pow_log_le_self _ hn)
  rw [ArbitraryWidthPieces.real_piece_sum] at hslices
  have hslices' :
      ((∑ i ∈ Finset.range (count Machine.width v.width),
        digit Machine.width v.width i*ArbitrarySliceStepBudget.budget i (volume prime v) : ℕ) : ℝ) ≤
      ArbitrarySliceStepBudget.constant*(volume prime v : ℝ)*(v.width : ℝ)^BudgetBound.tau := by
    simpa only [count,ite_eq_right hn,digit,ArbitraryWidthPieceLoop.remaining,
      Nat.cast_sum,Nat.cast_mul] using hslices
  have hcost := (Nat.cast_le (α := ℝ)).mpr (cost_bound v hs hp hv)
  simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_one] at hcost
  have hV := RecursiveAffinePrepare.volume_positive Shared50ModularControl.prime_prime.two_le v hp
  have hwV : v.width ≤ volume prime v :=
    RecursiveHeaderBounds.values_le_volume Shared50ModularControl.prime_prime.two_le v hp 3
  have hc : (0 : ℝ) ≤ constant := Nat.cast_nonneg _
  have hlin : ((v.width+1 : ℕ) : ℝ) ≤ 2*(volume prime v : ℝ) := by
    exact_mod_cast (show v.width+1 ≤ 2*volume prime v by omega)
  have hpow : (1 : ℝ) ≤ (v.width : ℝ)^BudgetBound.tau :=
    Real.one_le_rpow (by exact_mod_cast hN) BudgetBound.exponent_range.1.le
  have hcv : (0 : ℝ) ≤ (constant : ℝ)*(volume prime v : ℝ) :=
    mul_nonneg hc (Nat.cast_nonneg _)
  simp only [Nat.cast_add,Nat.cast_one] at hlin
  have hctrl := mul_le_mul_of_nonneg_left hlin hc
  have hscale := mul_le_mul_of_nonneg_left hpow (by simpa only [mul_assoc] using mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hcv)
  unfold coefficient
  nlinarith only [hcost,hslices',hctrl,hscale]

theorem cost_uniform_tau (v : Descriptor) (hs : Fin 6 → List Bool) (hp : v.Positive)
    (hv : RecursiveDimensionBank.Headers v hs) :
    (ArbitraryWidthPieceRun.cost v hs : ℝ) ≤
      coefficient*(volume prime v : ℝ)*((v.width+1 : ℕ) : ℝ)^BudgetBound.tau := by
  by_cases hn : v.width = 0
  · have h := cost_bound v hs hp hv
    simp only [hn,count,ite_true,Finset.range_zero,Finset.sum_empty,zero_add,
      zero_add,mul_one] at h
    have hreal : (ArbitraryWidthPieceRun.cost v hs : ℝ) ≤ (constant : ℝ) :=
      (Nat.cast_le (α := ℝ)).mpr h
    have hV := RecursiveAffinePrepare.volume_positive Shared50ModularControl.prime_prime.two_le v hp
    have hVreal : (1 : ℝ) ≤ volume prime v := by exact_mod_cast hV
    have hc : (0 : ℝ) ≤ constant := Nat.cast_nonneg _
    have hstep := ArbitrarySliceStepBudget.constant_positive
    have hcoeff : (constant : ℝ) ≤ coefficient := by
      unfold coefficient
      linarith only [hc,hstep]
    have hscale := mul_le_mul_of_nonneg_left hVreal coefficient_positive.le
    simp only [hn,zero_add,Nat.cast_one,Real.one_rpow,mul_one]
    linarith only [hreal,hcoeff,hscale]
  · have h := cost_tau v hs hp hv (by omega)
    have hpow : (v.width : ℝ)^BudgetBound.tau ≤ ((v.width+1 : ℕ) : ℝ)^BudgetBound.tau :=
      Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast (Nat.le_add_right v.width 1))
        BudgetBound.exponent_range.1.le
    have hcoef : (0 : ℝ) ≤ coefficient*(volume prime v : ℝ) :=
      mul_nonneg coefficient_positive.le (Nat.cast_nonneg _)
    exact h.trans (mul_le_mul_of_nonneg_left hpow hcoef)


end
end IntegerMultBounds.MathlibTM2.M8.Machine.ArbitraryWidthPieceCost
