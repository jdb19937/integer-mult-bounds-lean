module

public import IntegerMultBounds.MathlibTM2.Fast.CRTControlProg
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Algebra.Order.Ring.Star

/-!
# Binary workspace bounds for direct CRT controls

These estimates hold even for invalid control digits. A descriptor scan with
weights at most `2^B` and address below `2^B` has value below `2^(2*B)`;
the final modular multiplication fits `3*B+1` bits. The extra bit also
represents an endpoint such as a place or modulus equal to `2^B`.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Fast

open IntegerMultBounds.MathlibTM2.Mult

/-- The binary envelope bounds every original mixed-radix weight. -/
theorem crtControl_weight_le {d : ℕ} (a s : Fin d → ℕ)
    (hs : ∀ j, s j ≤ 2 ^ a j) (j : Fin d) :
    prefixProd s j ≤ 2 ^ (∑ k, a k) := by
  calc
    prefixProd s j ≤ ∏ k ∈ Finset.Iio j, 2 ^ a k :=
      Finset.prod_le_prod fun k _ => hs k
    _ ≤ ∏ k : Fin d, 2 ^ a k :=
      Finset.prod_le_univ_prod_of_one_le fun k => Nat.one_le_pow _ _ (by decide)
    _ = 2 ^ (∑ k, a k) := Finset.prod_pow_eq_pow_sum _ _ _

/-- A positive-place scan cannot accumulate more than address times maximum
weight, regardless of active flags or digit validity. -/
theorem crtControlValue_le_mul (fs : List CrtControlField) (F M : ℕ)
    (hfields : ∀ f ∈ fs, 0 < f.place ∧ f.weight ≤ M) :
    crtControlValue fs F ≤ F * M := by
  induction fs generalizing F with
  | nil => simp [crtControlValue]
  | cons f fs ih =>
    have hf := hfields f (by simp)
    have ht := ih (F % f.place) (fun g hg => hfields g (by simp [hg]))
    have hd : F / f.place + F % f.place ≤ F := by
      have hm := Nat.mul_le_mul_left (F / f.place) hf.1
      have he := Nat.div_add_mod F f.place
      nlinarith
    have hc : (if f.active then F / f.place * f.weight else 0) ≤ F / f.place * M := by
      split <;> first | exact Nat.mul_le_mul_left _ hf.2 | omega
    simp only [crtControlValue]
    calc
      _ ≤ F / f.place * M + (F % f.place) * M := Nat.add_le_add hc ht
      _ = (F / f.place + F % f.place) * M := by ring
      _ ≤ F * M := Nat.mul_le_mul_right M hd

/-- Every descriptor has positive place and a globally bounded weight. -/
theorem crtControlFields_weight_le {d : ℕ} (a s : Fin d → ℕ)
    (hs : ∀ j, s j ≤ 2 ^ a j) (i : ℕ) (o : List (Fin d)) :
    ∀ f ∈ crtControlFields a s i o,
      0 < f.place ∧ f.weight ≤ 2 ^ (∑ j, a j) := by
  induction o with
  | nil => simp [crtControlFields]
  | cons j o ih =>
    intro f hf
    simp only [crtControlFields, List.mem_cons] at hf
    rcases hf with rfl | hf
    · exact ⟨by positivity, crtControl_weight_le a s hs j⟩
    · exact ih f hf

/-- Places, validity bounds, and mixed-radix weights all fit one address-width
block plus an endpoint bit. The layout width hypothesis allows a physical
prefix instead of requiring a complete permutation. -/
theorem crtControlFields_fit {d : ℕ} (a s : Fin d → ℕ)
    (hs : ∀ j, s j ≤ 2 ^ a j) (i B : ℕ) (o : List (Fin d))
    (hB : (∑ j, a j) ≤ B) (ho : crtW a o ≤ B) :
    ∀ f ∈ crtControlFields a s i o,
      0 < f.place ∧ f.place < 2 ^ (B + 1) ∧
      f.bound < 2 ^ (B + 1) ∧ f.weight < 2 ^ (B + 1) := by
  have hpow : (2 : ℕ) ^ B < 2 ^ (B + 1) := by
    rw [pow_succ]
    have : 0 < (2 : ℕ) ^ B := by positivity
    omega
  induction o with
  | nil => simp [crtControlFields]
  | cons j o ih =>
    have ht : crtW a o ≤ B := by rw [crtW_cons] at ho; omega
    intro f hf
    simp only [crtControlFields, List.mem_cons] at hf
    rcases hf with rfl | hf
    · have hj : a j ≤ B := by rw [crtW_cons] at ho; omega
      exact ⟨by positivity,
        (Nat.pow_le_pow_right (by decide) ht).trans_lt hpow,
        ((hs j).trans (Nat.pow_le_pow_right (by decide) hj)).trans_lt hpow,
        ((crtControl_weight_le a s hs j).trans
          (Nat.pow_le_pow_right (by decide) hB)).trans_lt hpow⟩
    · exact ih ht f hf

/-- A padded address yields a quadratic-volume bound, without a validity
assumption or any restriction on the physical axis order. -/
theorem crtControlValue_lt_pow {d : ℕ} (a s : Fin d → ℕ)
    (hs : ∀ j, s j ≤ 2 ^ a j) (i : ℕ) (o : List (Fin d)) (F B : ℕ)
    (hB : (∑ j, a j) ≤ B) (hF : F < 2 ^ B) :
    crtControlValue (crtControlFields a s i o) F < 2 ^ (2 * B) := by
  have hw : 2 ^ (∑ j, a j) ≤ (2 : ℕ) ^ B := Nat.pow_le_pow_right (by decide) hB
  calc
    _ ≤ F * 2 ^ (∑ j, a j) := crtControlValue_le_mul _ _ _
      (crtControlFields_weight_le a s hs i o)
    _ ≤ F * 2 ^ B := Nat.mul_le_mul_left F hw
    _ < 2 ^ B * 2 ^ B := Nat.mul_lt_mul_of_pos_right hF (by positivity)
    _ = 2 ^ (2 * B) := by rw [← pow_add]; congr 1; omega

/-- A scan invariant reserves enough space for every intermediate product and
addition, including ones performed before a failed validity test. -/
theorem crtControl_accumulate_le (f : CrtControlField)
    (F K M L : ℕ) (hbudget : K + F * M ≤ L)
    (hf : 0 < f.place ∧ f.weight ≤ M) :
    K + F / f.place * f.weight + (F % f.place) * M ≤ L := by
  have hd : F / f.place + F % f.place ≤ F := by
    have hm := Nat.mul_le_mul_left (F / f.place) hf.1
    have he := Nat.div_add_mod F f.place
    nlinarith
  have hw := Nat.mul_le_mul_left (F / f.place) hf.2
  have hb := Nat.mul_le_mul_right M hd
  nlinarith

/-- An explicit budget discharges the interpreter's only descriptor overflow
obligation. -/
theorem crtControlStep_descriptor_bounded {A W w : ℕ}
    (f : CrtControlField) (F K M : ℕ) (valid : Bool) (st : TableVM.TblSt 10 A)
    (hin : crtControlStepInput f F K valid st)
    (hf : 0 < f.place ∧ f.weight ≤ M) (hbudget : K + F * M < 2 ^ W) :
    TableVM.TblDo A W w crtControlStep st
      (fun t => t = crtControlStepState w st) 9 := by
  apply crtControlStep_do
  intro _
  obtain ⟨hF, hp, _, hw, _, hK, _⟩ := hin
  rw [hK, hF, hp, hw]
  have h := crtControl_accumulate_le f F K M (K + F * M) le_rfl hf
  omega

/-- Final modular multiplication needs at most three address-width blocks. -/
theorem crtControl_offset_mul_lt (B μ K : ℕ) (hμ : μ ≤ 2 ^ B)
    (hK : K < 2 ^ (2 * B)) : μ * K < 2 ^ (3 * B + 1) := by
  have hp : μ * K < 2 ^ B * 2 ^ (2 * B) :=
    lt_of_le_of_lt (Nat.mul_le_mul_right K hμ)
      (Nat.mul_lt_mul_of_pos_left hK (by positivity))
  have he : (2 : ℕ) ^ B * 2 ^ (2 * B) = 2 ^ (3 * B) := by
    rw [← pow_add]; congr 1; omega
  rw [he] at hp
  exact hp.trans_le (Nat.pow_le_pow_right (by decide) (by omega))

end IntegerMultBounds.MathlibTM2.Fast
