module

import IntegerMultBounds.MathlibTM2.Fast.CRTMachine
public import IntegerMultBounds.MathlibTM2.Fast.CRTSpec
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Bernstein

/-! # Content recurrences for the linear CRT driver

The physical exposure schedule is independent of content. Folding the original
rotation over descending or ascending target lists gives exactly `crtFwdC` or
`crtInvC`. Target zero is the identity and may be omitted in either direction.
Existing content-invariant lemmas from CRTMachine are reused here.
-/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast

/-- Axis zero has no lower controls and its rotation is the identity, even on
invalid coordinates. No coprimality or multiplier bound is needed. -/
theorem crtControlRot_zero {d : ℕ} (s : Fin d → ℕ) (hd : 0 < d)
    {α : Type*} (μ : ℕ) (fwd : Bool) (C : (Fin d → ℕ) → α) :
    crtRotC s 0 hd μ fwd C = C := by
  funext y
  unfold crtRotC
  by_cases hy : y ⟨0, hd⟩ < s ⟨0, hd⟩
  · have hK : crtKI s 0 y = 0 := by simp [crtKI, crtLow]
    have htest : (∀ j : Fin d, j.val < 0 → y j < s j) ∧ y ⟨0, hd⟩ < s ⟨0, hd⟩ :=
      ⟨by simp, hy⟩
    rw [ite_eq_left htest, hK]
    cases fwd <;> simp [crtShift, crtLo, Nat.mod_eq_of_lt hy]
  · rw [ite_eq_right (fun h => hy h.2)]

/-- Apply a runtime target sequence to the mathematical content. -/
def crtControlDriverContent {d : ℕ} {α : Type*} (s μ : Fin d → ℕ) (fwd : Bool)
    (C : (Fin d → ℕ) → α) (targets : List (Fin d)) : (Fin d → ℕ) → α :=
  targets.foldl (fun C i => crtRotC s i.val i.isLt (μ i) fwd C) C

private theorem take_succ {α : Type*} (xs : List α) (n : ℕ) (hn : n < xs.length) :
    xs.take (n + 1) = xs.take n ++ [xs[n]] := by
  induction xs generalizing n with
  | nil => simp at hn
  | cons x xs ih =>
    cases n with
    | zero => simp
    | succ n =>
      have hn' : n < xs.length := by simpa using hn
      simpa only [List.take_succ_cons, List.cons_append, List.getElem_cons_succ] using
        congrArg (List.cons x) (ih n hn')

/-- Every descending prefix agrees with the established forward recurrence. -/
theorem crtControlDriver_forward_prefix {d : ℕ} {α : Type*} (s μ : Fin d → ℕ)
    (C : (Fin d → ℕ) → α) (n : ℕ) (hn : n ≤ d) :
    crtControlDriverContent s μ true C ((List.finRange d).reverse.take n) = crtFwdC s μ C n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hn' : n < d := by omega
    rw [crtControlDriverContent, take_succ _ n (by simpa using hn'), List.foldl_append,
      List.foldl_cons, List.foldl_nil]
    rw [show List.foldl (fun C i => crtRotC s i.val i.isLt (μ i) true C) C
        ((List.finRange d).reverse.take n) = crtFwdC s μ C n from ih (by omega),
      crtFwdC_succ s μ C hn']
    congr 1 <;> simp [List.getElem_reverse]

/-- Every ascending prefix agrees with the established inverse recurrence. -/
theorem crtControlDriver_inverse_prefix {d : ℕ} {α : Type*} (s μ : Fin d → ℕ)
    (C : (Fin d → ℕ) → α) (n : ℕ) (hn : n ≤ d) :
    crtControlDriverContent s μ false C ((List.finRange d).take n) = crtInvC s μ C n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hn' : n < d := by omega
    rw [crtControlDriverContent, take_succ _ n (by simpa using hn'), List.foldl_append,
      List.foldl_cons, List.foldl_nil]
    rw [show List.foldl (fun C i => crtRotC s i.val i.isLt (μ i) false C) C
        ((List.finRange d).take n) = crtInvC s μ C n from ih (by omega),
      crtInvC_succ s μ C hn']
    congr 1 <;> simp

/-- Omitting target zero anywhere in a sequence preserves its exact content. -/
theorem crtControlDriver_filter_zero {d : ℕ} {α : Type*} (s μ : Fin d → ℕ)
    (fwd : Bool) (C : (Fin d → ℕ) → α) (targets : List (Fin d)) :
    crtControlDriverContent s μ fwd C (targets.filter fun i => i.val ≠ 0) =
      crtControlDriverContent s μ fwd C targets := by
  induction targets generalizing C with
  | nil => rfl
  | cons i targets ih =>
    by_cases hi : i.val = 0
    · have hd : 0 < d := by have := i.isLt; omega
      have he : i = ⟨0, hd⟩ := Fin.ext hi
      subst i
      simpa [crtControlDriverContent, crtControlRot_zero] using ih C
    · simpa [crtControlDriverContent, hi] using ih (crtRotC s i.val i.isLt (μ i) fwd C)

/-- The descending nonzero-target driver has exactly the original forward
content, so its final layout reversal does not alter the arithmetic proof. -/
theorem crtControlDriver_forward {d : ℕ} {α : Type*} (s μ : Fin d → ℕ)
    (C : (Fin d → ℕ) → α) :
    crtControlDriverContent s μ true C
      ((List.finRange d).reverse.filter fun i => i.val ≠ 0) = crtFwdC s μ C d := by
  rw [crtControlDriver_filter_zero]
  have ht : (List.finRange d).reverse.take d = (List.finRange d).reverse :=
    List.take_of_length_le (by simp)
  simpa only [ht] using crtControlDriver_forward_prefix s μ C d le_rfl

/-- The ascending nonzero-target driver has exactly the original inverse content. -/
theorem crtControlDriver_inverse {d : ℕ} {α : Type*} (s μ : Fin d → ℕ)
    (C : (Fin d → ℕ) → α) :
    crtControlDriverContent s μ false C
      ((List.finRange d).filter fun i => i.val ≠ 0) = crtInvC s μ C d := by
  rw [crtControlDriver_filter_zero]
  have ht : (List.finRange d).take d = List.finRange d := List.take_of_length_le (by simp)
  simpa only [ht] using crtControlDriver_inverse_prefix s μ C d le_rfl

/-- Any pointwise property of records survives every driver prefix. This
includes constant record length and the routing alphabet restriction. -/
theorem crtControlDriver_mem {d : ℕ} {α : Type*} (s μ : Fin d → ℕ)
    (fwd : Bool) (p : α → Prop) (C : (Fin d → ℕ) → α) (hC : ∀ x, p (C x))
    (targets : List (Fin d)) : ∀ x, p (crtControlDriverContent s μ fwd C targets x) := by
  induction targets generalizing C with
  | nil => exact hC
  | cons i targets ih =>
    exact ih _ (crtRotC_mem s p i.isLt (μ i) fwd C hC)

/-- Fixed record length and the interchange's eight-symbol restriction are
preserved together, independently of target order. -/
theorem crtControlDriver_records {d A : ℕ} (s μ : Fin d → ℕ) (fwd : Bool)
    (C : (Fin d → ℕ) → List (Fin (A + 4))) (c : ℕ)
    (hC : ∀ x, (C x).length = c) (h8 : ∀ x, ∀ z ∈ C x, z.val < 8)
    (targets : List (Fin d)) :
    (∀ x, (crtControlDriverContent s μ fwd C targets x).length = c) ∧
    (∀ x, ∀ z ∈ crtControlDriverContent s μ fwd C targets x, z.val < 8) := by
  exact ⟨crtControlDriver_mem s μ fwd (fun l => l.length = c) C hC targets,
    crtControlDriver_mem s μ fwd (fun l => ∀ z ∈ l, z.val < 8) C h8 targets⟩

end IntegerMultBounds.MathlibTM2.Fast
