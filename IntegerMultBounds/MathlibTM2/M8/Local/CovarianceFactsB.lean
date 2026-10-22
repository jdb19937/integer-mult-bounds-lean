module

public import IntegerMultBounds.MathlibTM2.M8.Local.CovarianceKernelB

/-! Passed mask checks imply coefficient equations for every target simultaneously. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M8.Local.CovarianceB
noncomputable section
open MaskWeightsB

/-- Each checked allocation names the coefficient at its actual consecutive slot. -/
theorem allocationOk_get (M : Masks) (s : Nat) (us : List Use)
    (h : allocationOk M s us = true) (i : Nat) (hi : i < us.length) :
    M.slot (s + i) = M.use us[i] := by
  induction us generalizing s i with
  | nil => simp at hi
  | cons u us ih =>
    simp only [allocationOk, Bool.and_eq_true, Nat.beq_eq] at h
    cases i with
    | zero => simpa using h.1
    | succ i =>
      have hi' : i < us.length := by simpa using hi
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih (s + 1) h.2 i hi'

/-- The node check separates the fresh-allocation and argument equations. -/
theorem nodeOk_parts (M : Masks) (n : Nat) (x : Nat × List Use)
    (h : nodeOk M n x = true) :
    allocationOk M (slotsBefore n) (if n < leafCount then x.2 else x.2.tail) = true ∧
      (n < leafCount ∨ argumentOk M n x.2 false = true ∧ argumentOk M n x.2 true = true) := by
  unfold nodeOk at h
  simp only [Bool.and_eq_true] at h
  refine ⟨h.1, ?_⟩
  by_cases hn : n < leafCount
  · exact Or.inl hn
  · exact Or.inr (by simpa only [ite_eq_right hn, Bool.and_eq_true] using h.2)

/-- One XOR equation certifies the scalar argument recurrence at every target. -/
theorem argumentOk_coeff (M : Masks) (n : Nat) (us : List Use) (pos : Bool)
    (h : argumentOk M n us pos = true) (t : Nat) :
    coeff (M.argument n pos) t = (us.map fun u => coeff (M.use u) t).sum +
      match (records.get width n).link with
      | none => 0
      | some L => if pos = L.operand then coeff (M.argument L.user L.pos) t else 0 := by
  unfold argumentOk at h
  have he := Nat.beq_eq.mp h
  rw [he, coeff_xor, coeff_xorSum, List.map_map]
  simp only [Function.comp_def]
  cases hl : (records.get width n).link with
  | none => simp
  | some L => by_cases hp : pos = L.operand <;> simp [hp]

theorem coeff_shiftLeft (s t : Nat) :
    coeff (Nat.shiftLeft 1 s) t = if s = t then 1 else 0 := by
  simp [coeff, Nat.shiftLeft_eq, Nat.testBit_two_pow]

/-- A list's mask counts occurrences over F₂; no duplicate-free hypothesis is needed. -/
theorem coeff_targets (ts : List Nat) (t : Nat) :
    coeff (xorSum (ts.map (Nat.shiftLeft 1))) t = (ts.count t : ZMod 2) := by
  induction ts with
  | nil => simp [xorSum]
  | cons s ts ih =>
    rw [List.map_cons, xorSum, coeff_xor, ih, coeff_shiftLeft]
    by_cases hs : s = t
    · simp [hs, add_comm]
    · simp [hs]

/-- The checked centre mask gives the exact root coefficient at every target. -/
theorem centreOk_coeff (M : Masks) (c : Nat) (h : centreOk M c = true) (t : Nat) :
    coeff (M.root (3 * leafCount + c)) t = ((centreTargets c).count t : ZMod 2) := by
  unfold centreOk at h
  rw [Nat.beq_eq.mp h, coeff_targets]

end
end IntegerMultBounds.MathlibTM2.M8.Local.CovarianceB
