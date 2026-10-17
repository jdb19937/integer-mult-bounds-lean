module

public import IntegerMultBounds.MathlibTM2.Fast.MainEmbed
public import IntegerMultBounds.MathlibTM2.Fast.SynLaySpec
public import IntegerMultBounds.MathlibTM2.Fast.DistWidth
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Algebra.Order.Ring.Star

/-!
# The layout bundle of the fast multiplier from the layout programs

The layout hypotheses `MnLay w` of the top-level assembly (`Fast/MainEmbed`) instantiated from
the verified layout programs `slyFwd`, `slyOpp` (`Fast/SynLayFwd`, `Fast/SynLayOpp`):

* the layout programs are `slyFwd mnQ_layer`, `slyOpp mnQ_layer` at the alphabet
  `prime + mnKa`;
* the park predicate at `n` is `slyPk (blW w n) (blE n)`: `park` holds the writer's word width
  `blW w n = slyW N B ℓ (d - 1)` (`N = Σ aᵢ`, `B = 2^ℓ w`) and the axis word `blE n`, whose bit
  `i` is set exactly on the long axes `numHalf n ≤ i < d n - 1` (`bl_ax`); the parking
  contents are `blP₀ w n = slyPark (blW w n) (blE n) []`;
* the layout costs are `blCL w v₀ n = slyFwdCost …`, `blCL' w v₀ n = slyOppCost …`.

`blLay w v₀ hw hv hc : MnLay w` takes the width condition `1 ≤ w n`, the parameter wires `v₀`
with the `wires` property of `MnLay`, and the cost bound of `MnLay` at `blCL`, `blCL'`; the
contracts `layF`, `layO` are `slyFwd_lay`, `slyOpp_lay` at the sizes of `Sizes`, with the word
width conditions from `slyW_ok`. `blLay_exists` packages this as an existence statement for the
final assembly, with `mnσL (blLay …) n = mnσ (blP₀ w n) (v₀ n)` (`blLay_σL`).
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2.Fast.Main

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.LayerMachine IntegerMultBounds.MathlibTM2.Mult.Rounds IntegerMultBounds.Networks
  IntegerMultBounds.NLogN IntegerMultBounds.MathlibTM2.Mult.SynthErr IntegerMultBounds.Spec.SignedRingProduct
open IntegerMultBounds.MathlibTM2.Node hiding LReg
open IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.ConvSt
open IntegerMultBounds.MathlibTM2.Mult IntegerMultBounds.MathlibTM2.Mult.Sizes
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
open IntegerMultBounds.MathlibTM2.Fast.TableVM (dsW)
open Filter

noncomputable section

/-! ### The axis word -/

/-- The axis word at `n`: `(2^(d-1) - 1) / 2^numHalf * 2^numHalf`, bit `i` set exactly for
`numHalf n ≤ i < d n - 1`, the long axes of the box. -/
def blE (n : ℕ) : ℕ := (2 ^ (d n - 1) - 1) / 2 ^ numHalf n * 2 ^ numHalf n

/-- Bit `i < D` of `(2^D - 1) / 2^m * 2^m` is set exactly when `m ≤ i`. -/
theorem bl_bits (D m i : ℕ) (hi : i < D) :
    (2 ^ D - 1) / 2 ^ m * 2 ^ m / 2 ^ i % 2 = if i < m then 0 else 1 := by
  split_ifs with h
  · have e : 2 ^ m = 2 ^ (m - i - 1) * 2 * 2 ^ i := by
      rw [mul_assoc, ← pow_succ', ← pow_add]; congr 1; omega
    generalize (2 ^ D - 1) / 2 ^ m = x
    rw [e, ← mul_assoc, Nat.mul_div_cancel _ (by positivity), ← mul_assoc, Nat.mul_mod_left]
  · have e : 2 ^ i = 2 ^ m * 2 ^ (i - m) := by rw [← pow_add]; congr 1; omega
    rw [e, ← Nat.div_div_eq_div_mul, Nat.mul_div_cancel _ (by positivity),
      Nat.div_div_eq_div_mul, ← pow_add, show m + (i - m) = i by omega]
    have := Nat.testBit_two_pow_sub_one D i
    rw [Nat.testBit_eq_decide_div_mod_eq] at this
    simpa [hi] using this

/-- The axis word is below `2^(d - 1)`. -/
theorem blE_lt (n : ℕ) : blE n < 2 ^ (d n - 1) :=
  lt_of_le_of_lt (Nat.div_mul_le_self _ _) (Nat.sub_lt (by positivity) one_pos)

/-- The axis word describes the axes `cvAx (t n)`: `aᵢ = ℓ - 1 + bit i`. -/
theorem bl_ax {n : ℕ} (hℓ : 1 ≤ ℓ n) :
    ∀ i < (List.ofFn (cvAx (t n))).length,
      ax (List.ofFn (cvAx (t n))) i = ℓ n - 1 + blE n / 2 ^ i % 2 := by
  intro i hi
  have hi' : i < d n - 1 := by simpa using hi
  unfold ax
  rw [List.getD_eq_getElem _ _ hi, List.getElem_ofFn]
  simp only [cvAx, t, blE]
  rw [bl_bits _ _ _ hi']
  split_ifs <;> simp [Nat.log_pow]
  omega

/-- The bit characterization in the form of the assembly. -/
theorem blE_spec : ∀ᶠ n in atTop, blE n < 2 ^ (d n - 1) ∧
    ∀ i < d n - 1, ax (List.ofFn (cvAx (t n))) i = ℓ n - 1 + blE n / 2 ^ i % 2 := by
  filter_upwards [eventually_big] with n hbig
  have hℓ : 1 ≤ ℓ n := by have := hbig.K_succ_le_ℓ; omega
  exact ⟨blE_lt n, fun i hi => bl_ax hℓ i (by simpa using hi)⟩

/-! ### The parameters of the layout programs -/

section Params

variable (w : ℕ → ℕ) (v₀ : ℕ → SynW → List (Fin (prime + mnKa + 4)))

/-- The writer's word width at `n`: `slyW N B ℓ (d - 1)`, `N = Σ aᵢ`, `B = 2^ℓ w`. -/
def blW (n : ℕ) : ℕ :=
  slyW (List.ofFn (cvAx (t n))).sum (2 ^ ℓ n * w n) (ℓ n) (d n - 1)

/-- The parking contents at `n`: `W` and `E` parked above nothing. -/
def blP₀ (n : ℕ) : List (Fin (prime + mnKa + 4)) := slyPark (blW w n) (blE n) []

/-- The layout cost of the forward transform at `n`. -/
def blCL (n : ℕ) : ℕ :=
  slyFwdCost mnKa (List.ofFn (cvAx (t n))) (ℓ n) (K n) (ℓ n) (w n) (blW w n) (blE n) (v₀ n)

/-- The layout cost of the opposite transform at `n`. -/
def blCL' (n : ℕ) : ℕ :=
  slyOppCost mnKa (List.ofFn (cvAx (t n))) (ℓ n) (K n) (ℓ n) (w n) (blW w n) (blE n) (v₀ n)

/-- The parking contents satisfy the park predicate. -/
theorem blP₀_pk (n : ℕ) : slyPk (blW w n) (blE n) (blP₀ w n) := ⟨[], rfl⟩

/-- The word width conditions of the writer at `n`. -/
theorem blW_ok (n : ℕ) :
    ((List.ofFn (cvAx (t n))).sum + 1) ^ (List.ofFn (cvAx (t n))).sum < 2 ^ blW w n ∧
      (List.ofFn (cvAx (t n))).sum + 2 ^ ℓ n * w n + 4 ≤ blW w n ∧ ℓ n < 2 ^ blW w n ∧
      blE n < 2 ^ blW w n :=
  slyW_ok _ _ _ _ _ (blE_lt n)

/-- The alphabet condition of the layout programs. -/
theorem bl_hA : 4 ≤ prime + mnKa := by have := mnKa_alpha; omega

/-! ### The bundle -/

/-- **The layout bundle from the layout programs.** The parameter wires `v₀` with the `wires`
property of `MnLay` and the cost bound of `MnLay` at `blCL`, `blCL'` are hypotheses. -/
def blLay (hw : ∀ᶠ n in atTop, 1 ≤ w n)
    (hv : ∀ᶠ n in atTop,
      SynV (v₀ n) (List.ofFn (cvAx (t n))) (ℓ n) (K n) (w n) (ℓ n) 0
          (layPerm (List.ofFn (cvAx (t n))) (ℓ n) (K n)) ∧
        v₀ n (.p .h) = [] ∧ v₀ n (.p .t) = [] ∧ (v₀ n (.p .c)).length = nRounds (cvAx (t n)) ∧
        blank ∉ v₀ n (.p .c))
    (hc : ∃ C : ℝ, ∀ᶠ n in atTop,
      ((mnCF n (w n) (blCL w v₀ n) (v₀ n) + mnCO n (w n) (blCL' w v₀ n) (v₀ n) : ℕ) : ℝ) ≤
        C * IntegerMultBounds.MathlibTM2.Cost.totConv n) : MnLay w where
  layP := slyFwd mnQ_layer
  layQ := slyOpp mnQ_layer
  Pk n := slyPk (blW w n) (blE n)
  P₀ := blP₀ w
  v₀ := v₀
  cL := blCL w v₀
  cL' := blCL' w v₀
  pk := Eventually.of_forall (blP₀_pk w)
  wires := hv
  layF := by
    filter_upwards [eventually_big, hw, hv] with n hbig hw hv
    have hℓ : 1 ≤ ℓ n := by have := hbig.K_succ_le_ℓ; omega
    obtain ⟨h1, h2, h3, h4⟩ := blW_ok w n
    exact slyFwd_lay mnQ_layer Cost.brDirs (cvAx (t n)) (mn_layHyp hbig) (v₀ n) hv.1 bl_hA hw
      (blW w n) (blE n) (bl_ax hℓ) h4 h1 h2 h3
  layO := by
    filter_upwards [eventually_big, hw, hv] with n hbig hw hv
    have hℓ : 1 ≤ ℓ n := by have := hbig.K_succ_le_ℓ; omega
    obtain ⟨h1, h2, h3, h4⟩ := blW_ok w n
    exact slyOpp_lay mnQ_layer Cost.brDirs (cvAx (t n)) (mn_layHyp hbig) (v₀ n) hv.1 bl_hA hw
      (blW w n) (blE n) (bl_ax hℓ) h4 h1 h2 h3
  cost := hc

variable {w v₀}

@[simp] theorem blLay_v₀ (hw hv hc) : (blLay w v₀ hw hv hc).v₀ = v₀ := rfl

@[simp] theorem blLay_P₀ (hw hv hc) : (blLay w v₀ hw hv hc).P₀ = blP₀ w := rfl

@[simp] theorem blLay_cL (hw hv hc) : (blLay w v₀ hw hv hc).cL = blCL w v₀ := rfl

@[simp] theorem blLay_cL' (hw hv hc) : (blLay w v₀ hw hv hc).cL' = blCL' w v₀ := rfl

@[simp] theorem blLay_layP (hw hv hc) : (blLay w v₀ hw hv hc).layP = slyFwd mnQ_layer := rfl

@[simp] theorem blLay_layQ (hw hv hc) : (blLay w v₀ hw hv hc).layQ = slyOpp mnQ_layer := rfl

/-- The transforms' parameter registers of the bundle: parking `blP₀ w n`, wires `v₀ n`. -/
theorem blLay_σL (hw hv hc) (n : ℕ) : mnσL (blLay w v₀ hw hv hc) n = mnσ (blP₀ w n) (v₀ n) :=
  rfl

/-- **The existence statement**: parameter wires with the `wires` property and the cost bound
at `blCL`, `blCL'` give a layout bundle with these wires, parking `blP₀ w`, and costs `blCL`,
`blCL'`. -/
theorem blLay_exists (hw : ∀ᶠ n in atTop, 1 ≤ w n)
    (h : ∃ v₀ : ℕ → SynW → List (Fin (prime + mnKa + 4)),
      (∀ᶠ n in atTop,
        SynV (v₀ n) (List.ofFn (cvAx (t n))) (ℓ n) (K n) (w n) (ℓ n) 0
            (layPerm (List.ofFn (cvAx (t n))) (ℓ n) (K n)) ∧
          v₀ n (.p .h) = [] ∧ v₀ n (.p .t) = [] ∧
          (v₀ n (.p .c)).length = nRounds (cvAx (t n)) ∧ blank ∉ v₀ n (.p .c)) ∧
      ∃ C : ℝ, ∀ᶠ n in atTop,
        ((mnCF n (w n) (blCL w v₀ n) (v₀ n) + mnCO n (w n) (blCL' w v₀ n) (v₀ n) : ℕ) : ℝ) ≤
          C * IntegerMultBounds.MathlibTM2.Cost.totConv n) :
    ∃ L : MnLay w, ∃ v₀, L.v₀ = v₀ ∧ L.P₀ = blP₀ w ∧ L.cL = blCL w v₀ ∧ L.cL' = blCL' w v₀ ∧
      L.layP = slyFwd mnQ_layer ∧ L.layQ = slyOpp mnQ_layer ∧
      ∀ n, mnσL L n = mnσ (blP₀ w n) (v₀ n) := by
  obtain ⟨v₀, hv, hc⟩ := h
  exact ⟨blLay w v₀ hw hv hc, v₀, rfl, rfl, rfl, rfl, rfl, rfl, fun _ => rfl⟩

end Params

/-! ### At the coefficient width `dsW` -/

/-- The coefficient width `dsW` of `Fast/DistWidth` is positive. -/
theorem bl_dsW_pos : ∀ᶠ n in atTop, 1 ≤ dsW n :=
  Eventually.of_forall fun n => by unfold dsW; omega

/-- The layout bundle at the coefficient width `dsW`. -/
def blLayDs (v₀ : ℕ → SynW → List (Fin (prime + mnKa + 4)))
    (hv : ∀ᶠ n in atTop,
      SynV (v₀ n) (List.ofFn (cvAx (t n))) (ℓ n) (K n) (dsW n) (ℓ n) 0
          (layPerm (List.ofFn (cvAx (t n))) (ℓ n) (K n)) ∧
        v₀ n (.p .h) = [] ∧ v₀ n (.p .t) = [] ∧ (v₀ n (.p .c)).length = nRounds (cvAx (t n)) ∧
        blank ∉ v₀ n (.p .c))
    (hc : ∃ C : ℝ, ∀ᶠ n in atTop,
      ((mnCF n (dsW n) (blCL dsW v₀ n) (v₀ n) + mnCO n (dsW n) (blCL' dsW v₀ n) (v₀ n) : ℕ) :
        ℝ) ≤ C * IntegerMultBounds.MathlibTM2.Cost.totConv n) : MnLay dsW :=
  blLay dsW v₀ bl_dsW_pos hv hc

end

end IntegerMultBounds.MathlibTM2.Fast.Main
